theory "Coder_Test_TUnits"
  imports "../src/CleanCoder"  (* Coder_Test_Env_AEnv *)
          "../src/compiler/Clean_Annotation"
begin
ML\<open>
(*This is an override for the update_Root_Ast function that is registered in C_Command.*)

fun transform_type typ = if typ = HOLogic.intT then "int" 
                         else if typ = HOLogic.natT then "nat"
                         else if is_listTy typ then (transform_type (dest_listTy typ))^" list" 
                         else if typ = HOLogic.unitT then "unit"
                         else error "Unknown variable type"

local open C_AbsEnv HOLogic in
fun get_hol_type (C_Env.Parsed ret) params = let
      val base_type =the (C11_TypeSpec_2_CleanTyp.conv_cDeclarationSpecifier_typ (SOME ret))
      fun transform_type ((C_Ast.CArrDeclr0 _)::R) base_type = listT (transform_type R base_type)
         | transform_type [] base_type = base_type
      in transform_type params base_type end
fun map_env_ident_to_identifier (name,(positions,_,data)) =
     let fun get_ident_scope C_Env.Global = Global 
            |get_ident_scope C_Env.Local = Local ""
            |get_ident_scope C_Env.Parameter = Parameter ""
      in
     case #functionArgs data of C_Ast.None => Identifier(name, if null positions then @{here} else hd positions,get_hol_type (#ret data) (#params data),get_ident_scope (#scope data))
     |_=> Identifier(name, @{here},intT,FunctionCategory (Final, NONE))  (*this line is wrong because of different function types*)
      end
end

fun declare_function idents name ast ret_ty recursive ctxt =
   let  val param_idents = filter (fn i => case i of C_AbsEnv.Identifier(_,_,_, C_AbsEnv.Parameter f_name) => f_name = name |_=>false) idents
        val local_idents = filter (fn i => case i of C_AbsEnv.Identifier(_,_,_, C_AbsEnv.Local f_name) => f_name = name |_=>false) idents
        val global_idents = filter (fn i => case i of C_AbsEnv.Identifier(_,_,_, C_AbsEnv.Global) => true
                                                      | C_AbsEnv.Identifier(_,_,_,C_AbsEnv.FunctionCategory _)=>true
                                                      | _ => false) idents

        (*Obtain the parameters and local variables*)
        val params = map (fn C_AbsEnv.Identifier(name,pos,typ, _) => (Binding.make (name, pos), transform_type typ)) (param_idents)
        val locals = map (fn C_AbsEnv.Identifier(name,pos,typ, _) => (Binding.make (name, pos), transform_type typ, NoSyn)) (local_idents)

        (*This is necessary, as parameters are represented as free variables.
          When the Invariants, post- and preconditions are read through the term antiquotations, 
          Syntax.parse_term (Syntax.read_term does this too) would substitute them by another const,
          which could be a local or global variable*)
        fun remove_params_from_proof ctx = let
             val param_names = List.map (fn C_AbsEnv.Identifier(n,_,_,_) => n) param_idents
             fun filter_by_shortname param_names (n, _) =
               List.exists (fn ele => ele = Long_Name.base_name n) param_names
             val longnames =  List.filter (filter_by_shortname param_names) (#constants (Consts.dest (Sign.consts_of (Proof_Context.theory_of ctx))))
             val thy0 = Proof_Context.theory_of ctx
             val thy' = List.foldl (fn (longname, thy')=> thy' |> Sign.hide_const true longname)  thy0 (List.map fst longnames)
             in Proof_Context.init_global thy' end

        (*Invariants and measuress need to be matched to a loop. This is done by comparing the parse locations of all while loops.
          The following are helper methods, to obtain the function get_invariant: positiona \<rightarrow> (context\<rightarrow>term) option*)
        val invariants:((string*(Context.generic -> term)*Position.range) list) = List.filter (fn (f_name,_,_) => f_name = name) 
                                                                (#invariants (Clean_Annotation.Data_Clean_Annotations.get ctxt)) 
        val measures:((string*(Context.generic -> term)*Position.range) list) = List.filter (fn (f_name,_,_) => f_name = name) 
                                                                (#measures (Clean_Annotation.Data_Clean_Annotations.get ctxt))                                                                                                       
        val loop_pos =Library.distinct (op =) (C11_Ast_Lib.fold_cStatement (fn a => fn b => a@b) C11_Unit_2_Clean.get_loop_positions ast [])
        fun compare_pos ((C_Ast.Position0 (pos1,_,_,_)),(C_Ast.Position0 (pos2,_,_,_))) = Int.compare (pos1,pos2)
        val loop_pos_sorted = Library.sort compare_pos loop_pos 
        fun range_less_than_pos (range:Position.range) (C_Ast.Position0 (pos,_,_,_)) = the (Position.offset_of (fst range)) < pos
        fun get_for_position (((inv,inv_pos)::R_inv): ((Context.generic -> term)*Position.range)list)
                                       (loop_positions: C_Ast.positiona list)
                                       (pos3: C_Ast.positiona)
                      (* search the first invariant, which is not declared before pos3 *)
                      = (if range_less_than_pos inv_pos pos3 then get_for_position R_inv loop_positions pos3 
                        else case loop_positions of (* we found the first invariant after pos3 *)
                              (* Now check, if the next loop definition is after the invariant definition. 
                                  Otherwise there is no invariant for the given loop *)
                              (pos1::pos2::R) => if pos3 = pos1 andalso range_less_than_pos inv_pos pos2 then SOME inv
                                                   else get_for_position ((inv,inv_pos)::R_inv) (pos2::R) pos3
                              | (pos1::R) => if pos3 = pos1 then SOME inv else NONE
                              | [] => NONE)
           |get_for_position [] _ _ = NONE
        fun get_invariant pos = (get_for_position (List.map (fn inv => (#2 inv, #3 inv)) invariants) loop_pos_sorted) pos
        fun get_measure pos = (get_for_position (List.map (fn inv => (#2 inv, #3 inv)) measures) loop_pos_sorted) pos
        fun get_loop_annotations pos = (get_invariant pos, get_measure pos)

        (*generic function to get the first ele*)
        val get_precond = Option.map (fn (_,e,_) => e) (List.find (fn (a,_,_) => a = name) (#preconditions (Clean_Annotation.Data_Clean_Annotations.get ctxt)))
        val get_postcond = Option.map (fn (_,e,_) => e) (List.find (fn (a,_,_) => a = name) (#postconditions (Clean_Annotation.Data_Clean_Annotations.get ctxt)))    

        (*the translation of the precondition*)
        fun get_translation NONE default ctxt= C11_Expr_2_Clean.lifted_term (StateMgt.get_state_type (ctxt)) default
          | get_translation (SOME get_term) _ ctxt= let
                    val term = get_term (Context.Proof (remove_params_from_proof ctxt))
                    val lifted = C11_Expr_2_Clean.lifted_term (StateMgt.get_state_type ctxt) term
                    in
                       Syntax.check_term ctxt lifted
                    end
        (*The actual translation of the loop body*)
        fun get_translated_fun_bdy ctx _ = let
              val ctx' = remove_params_from_proof ctx
              val v = ((C11_Ast_Lib.fold_cStatement
              C11_Stmt_2_Clean.regroup 
              (C11_Stmt_2_Clean.convertStmt false 
                                            (StateMgt.get_state_type ctx') 
                                            (local_idents@param_idents@global_idents) 
                                            (Proof_Context.theory_of ctx') 
                                             name get_loop_annotations)
              ast []))
              in hd v end

        val test_function_sem = {binding = Binding.name name,
                                 locals = locals@[(Binding.name "dummylocalvariable","int", NoSyn)], (*There needs to be at least one local variable*)
                                 params = params,
                                 ret_type = transform_type ret_ty,
                                 read_pre = get_translation get_precond  (@{term True}),
                                 read_post = get_translation get_postcond (Abs ("ret",ret_ty, @{term True})),
                                 read_variant_opt = NONE,
                                 read_body = get_translated_fun_bdy}
        val decl = Function_Specification_Parser.checkNsem_function_spec_gen {recursive = recursive} test_function_sem
    in decl end

local open C_AbsEnv HOLogic in
fun handle_declarations translUnit ctxt =
     (let
        val env = (C_Module.Data_Last_Env.get ctxt)
        (*First we need to get all previously defined global vars and functions*)
        val m = (Symtab.dest (#idents(#var_table(env))))
        val prev_idents =map map_env_ident_to_identifier m
        (*the new identifiers are returned in reverse \<rightarrow> thus reverse *)
        val (new_idents, call_table) = C_AbsEnv.parseTranslUnitIdentifiers translUnit [] prev_idents Symtab.empty

        val identifiers = (rev new_idents)@prev_idents
        val map_idents = List.map (fn C_AbsEnv.Identifier(name,_,typ,_) => (Binding.name name, transform_type typ, NoSyn))

        fun get_declaration is_global idents = if null idents then I else StateMgt.new_state_record is_global (NONE,idents)
        
        val global_idents = (map_idents (List.filter (fn C_AbsEnv.Identifier(_,_,_,vis) => vis = C_AbsEnv.Global) new_idents))
        val global_declaration =get_declaration true global_idents
             
        val fun_asts = 
              List.map (fn C_AbsEnv.Identifier(name,_,ret_ty,C_AbsEnv.FunctionCategory ast) =>
                     let  fun is_recursive NONE = false
                            |is_recursive (SOME calls) = List.exists (fn x => x=name) calls
                     in 
                  (name,the (snd ast),ret_ty,  is_recursive (Symtab.lookup call_table name)) end) 
              (List.filter (fn a => case a of C_AbsEnv.Identifier(_,_,_,C_AbsEnv.FunctionCategory _) => true | _ => false) (rev new_idents))
        val function_declarations = List.map (fn (name,ast,ret_ty, recursive) => declare_function identifiers name ast ret_ty recursive ctxt) (fun_asts)

        val function_decl = fold (fn f => fn acc => f acc) function_declarations
    in
     Context.map_theory (function_decl o global_declaration) ctxt
    end);
end
\<close>
ML\<open>
fun handle_declarations_wrapper ast v2 ctxt =
  let val ctx1 = update_Root_Ast SOME ast v2 ctxt (*Note the call to the original callback - this somehow gets overwritten*)
  in
    case ast of (C_Ast.Left translUnit) => handle_declarations translUnit ctx1
                    | _ => ctx1
  end
\<close>

setup \<open>Context.theory_map (C_Module.Data_Accept.put (handle_declarations_wrapper))\<close> 

(* Note: The hook "C_Module.C_Term.map_translation_unit" is not adequate, as it is 
         meant for the term antiquotation (its callback returns a term, not a theory/context *)

setup \<open>C_Module.C_Term.map_expression 
    (fn cexpr => fn _ => fn ctxt => let 
    val sigma_i = (StateMgt.get_state_type o Context.proof_of )ctxt
    val env = C_Module.Data_Surrounding_Env.get ctxt
    val idents =  (Symtab.dest (#idents(#var_table(env))))
    val A_env = List.map map_env_ident_to_identifier idents
    val expr = (hd (C11_Ast_Lib.fold_cExpression (K I) 
                                      (C11_Expr_2_Clean.convertExpr true sigma_i  A_env  (Context.theory_of ctxt) "" (K NONE))
                                      cexpr [])) handle ERROR msg => (writeln("ERROR: "^(@{make_string}msg));@{term "1::int"})
in
  expr
(* @{term "1::int"}*)
 end

)\<close>
declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]

ML\<open>
val a = (Abs ("\<sigma>", StateMgt.get_state_type ( @{context}),
      Const ("Orderings.ord_class.greater_eq", @{typ "_"}) $ Const ("Groups.one_class.one",  @{typ "int"}) $
        Const ("Groups.one_class.one", @{typ "int"})))

val a' = absfree ("a",@{typ "int"}) (absfree ("b", @{typ "int"}) (Syntax.check_term @{context} a))

val b = HOLogic.mk_case_prod a'
\<close>


C\<open>
int multiply1(int a, int b){
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>1 \<ge> 1\<close> */
  return a;
}\<close>


term\<open>nat\<close>
C\<open>
int u;
int arrr[];
\<close>
C\<open>
int globvar;
unsigned nat1;
int u;
int fun_with_pre_test(int u){
  int localvar;

  localvar = u;
  /* pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>u\<close> > 1\<close> */
  /* post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<lambda>ret::int.\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>u\<close> > 1 \<and> ret > 0\<close> */

  while(localvar>0){
  /* inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>u\<close> \<ge> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>localvar\<close> \<close> */
  /*@ measure\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>nat1\<close>\<close> */
    localvar = localvar -1;
  }

  return 1;
}\<close>
find_theorems fun_with_pre_test_core


section\<open>Demonstration\<close>

subsection\<open>Global definitions\<close>
C\<open>
int global_integer;
unsigned global_nat;
\<close>
(*variables are declared accordingly*)
find_theorems global_integer
find_theorems global_nat
term\<open>global_integer\<close>
term\<open>global_nat\<close>




subsection\<open>Function definitions\<close>
C\<open>int threefunc(){
  return 1+2;
}

int sum5(int p1, int p2){
  return p1+p2;
}

void addToGlobalInteger(int value){
  global_integer = global_integer+value;
}
\<close>

find_theorems threefunc_core
term\<open>threefunc\<close>
find_theorems sum_core
term\<open>sum\<close>




subsection\<open>And function calls\<close>
C\<open>
void addPlusThree(int val){
  int three; /*Init expression currently unsupported*/
  three = threefunc();
  addToGlobalInteger(three+val);
}
\<close>


text\<open>we compare this to an equivalent definition\<close>
function_spec addPlusThree1(val :: int) returns unit
pre          "\<open>True\<close>" 
post         "\<open>\<lambda>res::unit. True \<close>"
local_vars   three :: int
defines "p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C threefunc \<open>()\<close> ; assign_local three_update (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p);-
         call\<^sub>C addToGlobalInteger \<open>(three + val)\<close>"

find_theorems addPlusThree_core
find_theorems addPlusThree1_core
term\<open>addPlusThree\<close>
term\<open>addPlusThree1\<close>




subsection \<open>Recursive functions\<close>

rec_function_spec recursive_add1(n::int) returns unit
pre          "\<open>True\<close>" 
post         "\<open>\<lambda>res::unit. True \<close>"
local_vars   localvar1 :: int
defines "if\<^sub>C \<open>n > 0\<close>  
         then (\<open> global_integer :=  global_integer + 1\<close>);-
               call\<^sub>C recursive_add1 \<open>(n-1)\<close>
         else skip\<^sub>S\<^sub>E 
         fi"

C\<open>
void recursive_add(int n){
  if(n > 0){
    global_integer = global_integer + 1;
    recursive_add(n-1);
  }
}\<close>

find_theorems recursive_add_core
find_theorems recursive_add1_core
term recursive_add
term recursive_add1




subsection\<open>(multidimensional) arrays are also supported\<close>
C\<open>
int globalArray[][];
int something(){
  int localvar;
  localvar = globalArray[0][3];
}
\<close>




subsection\<open>A fully annotated program\<close>
text\<open>disclaimer: C_expr antiquotation does not yet work\<close>



C\<open>
int multiply(int a, int b){
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>1 \<ge> 1\<close> */
  /*@ post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<lambda>ret::int. ret = \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a*b\<close>\<close> */
  int s;
  int counter;
  int counter_b;
  counter = 0;
  s = 0;

  while(counter < a){
    /*@ inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>counter*b\<close> = \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>s\<close> \<and> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>counter\<close> \<le> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a\<close>\<close> */
    counter_b = 0;
    while(counter_b < b){
      /*@ inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>counter_b\<close> \<le> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>b\<close>\<close> */      
      counter_b = counter_b +1;
    }
    
    s = s + counter_b;
    counter = counter + 1;
  }
  return s;
}
\<close>







section\<open>Some other tests\<close>

C\<open>
int intarr[][][];
int x;
\<close>
term x
find_theorems x
C\<open>
int sum1(int param1,int param2){
  x = threefunc();
  intarr[2][3][1] = x + param1 + param2;
  return 1;
}

int sum3(int param1,int param2){
  int x; // test to override
  x = sum1(param1, param2);
  return x;
}\<close>
find_theorems x
find_theorems sum1_core
C\<open>
int test_scope(){
  x = 1;
  return x;
}
\<close>

find_theorems sum3_core
term\<open>intarr\<close>


C\<open>
int a;
int testfunction(int v1, int v2){
  global_integer = sum1(v1,v2);
  return global_integer;
}
\<close>

C\<open>
int b;
\<close>

text\<open>Now the declaration of local variables\<close>
C\<open>
int funwithlocalvars(){
  int localvar1;
  localvar1 = threefunc();
  return localvar1;
}
\<close>
term localvar1
find_theorems funwithlocalvars_core
term funwithlocalvars_core

ML\<open>
val ast = @{C11_CTranslUnit}
\<close>
ML\<open>
val env = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>

function_spec testfunction1(param1 :: int, param2::int) returns int
pre          "\<open>True\<close>" 
post         "\<open>\<lambda>res::int. True \<close>"
local_vars   localvar1 :: int
defines "p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C sum1 \<open>(2::int, 3::int)\<close> ; assign_global global_integer_update (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p);-
         return\<^bsub>local_testfunction1_state.result_value_update\<^esub> \<open>global_integer\<close>"

find_theorems testfunction1_core
term\<open>testfunction1_core\<close>



(*
Recursions with return values are currently unsupported in CLEAN, but are about to be fixed by someone else

rec_function_spec recursive_function2(n::int) returns int
pre          "\<open>True\<close>" 
post         "\<open>\<lambda>res::int. True \<close>"
local_vars   localvar1 :: int
defines "p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C recursive_function2 \<open>2::int\<close> ; assign_local localvar1_update (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p);-
return\<^bsub>local_recursive_function2_state.result_value_update\<^esub> \<open>1::int\<close>"
*)


text\<open>Now the pre and post conditions\<close>



C\<open>
int xx;
int fun_with_pre(int u){
  int local1;
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>xx\<close> > 0\<close> */
  /*@ post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<lambda>ret::int.3 > \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>u\<close>\<close> */
  return local1;
}
int fun_with_pre2(int u){
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>u\<close>  > 0\<close> */

  return 1;
}
\<close>

ML\<open>

val annotation_data = Clean_Annotation.Data_Clean_Annotations.get (Context.Theory @{theory})
\<close>                                          


text\<open>Invariants are more tricky, as there can be several within one function\<close>

text\<open>Lets start with a simple example with two loops, 
    which computes a*b, given a and b are positive!

    The following program is fully annotated with pre-, and postcondition, aswell as 2 invariants\<close>
C\<open>int a;\<close>
C\<open>
int multiply2(int a, int b){
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a\<close> > 0\<close> */
  /*@ post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<lambda>ret::int. ret = \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a*b\<close>\<close> */
  int sum;
  int counter;
  int counter_b;

  while(counter < a){
    /* here we have a loop without an invariant */
    counter = counter + 1;
  }
  counter = 0;
  sum = 0;

  while(counter < a){
    /*@ inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>counter\<close> \<le> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a\<close>\<close> */
    counter = counter + 1;
  }

  while(counter > 0){
    /* inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>(a-counter)*b\<close> = \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>sum\<close> \<and> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>counter\<close> \<ge> 0\<close> */
    counter_b = 0;
    while(counter_b < b){
      /* inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>C\<open>counter_b\<close> \<le> b\<close>*/      
      counter_b = counter_b +1;
    }
    
    sum = sum + counter_b;
    counter = counter -1;

  }
  return sum;
}
\<close>

C\<open>
int globarr[];\<close>
C\<open>
void somefunction123(){
int localArray[];

}\<close>

find_theorems multiply_core

ML\<open>
val annotation_data = Clean_Annotation.Data_Clean_Annotations.get (Context.Theory @{theory})
\<close>   

