theory "Coder_Test_TUnits"
  imports "../src/CleanCoder"  (* Coder_Test_Env_AEnv *)
          "../src/compiler/Clean_Annotation"
begin
ML\<open>
(*This is an override for the update_Root_Ast function that is registered in C_Command.*)

fun transform_type typ = if typ = HOLogic.intT then "int" 
                         else if typ = HOLogic.natT then "uint"
                         else if is_listTy typ then (transform_type (dest_listTy typ))^" list" 
                         else error "Unknown variable type"


fun declare_function idents name ast ret_ty recursive ctxt =
   let  val param_idents = filter (fn i => case i of C_AbsEnv.Identifier(_,_,_, C_AbsEnv.Parameter f_name) => f_name = name |_=>false) idents
        val local_idents = filter (fn i => case i of C_AbsEnv.Identifier(_,_,_, C_AbsEnv.Local f_name) => f_name = name |_=>false) idents
        val global_idents = filter (fn i => case i of C_AbsEnv.Identifier(_,_,_, C_AbsEnv.Global) => true
                                                      | C_AbsEnv.Identifier(_,_,_,C_AbsEnv.FunctionCategory _)=>true
                                                      | _ => false) idents

        val params = map (fn C_AbsEnv.Identifier(name,pos,typ, _) => (Binding.make (name, pos), transform_type typ)) (param_idents)
        val locals = map (fn C_AbsEnv.Identifier(name,pos,typ, _) => (Binding.make (name, pos), transform_type typ, NoSyn)) (local_idents)
        fun get_translated_fun_bdy ctx _ = let
              val v = ((C11_Ast_Lib.fold_cStatement 
              C11_Stmt_2_Clean.regroup 
              (C11_Stmt_2_Clean.convertStmt false (StateMgt.get_state_type ctx) (local_idents@param_idents@global_idents) (Proof_Context.theory_of ctx))
              ast []))
              in hd v end

        val test_function_sem = {binding = Binding.name name,
                                 locals = locals@[(Binding.name "dummylocalvariable","int", NoSyn)], (*There needs to be at least one local variable*)
                                 params = params,
                                 ret_type = transform_type ret_ty,
                                 read_pre = fn ctx => Abs ("\<sigma>",(StateMgt.get_state_type ctx), @{term True}),
                                 read_post = fn ctx => Abs ("\<sigma>",(StateMgt.get_state_type ctx), Abs ("ret",ret_ty, @{term True})),
                                 read_variant_opt = NONE,
                                 read_body = get_translated_fun_bdy}
        val _ = writeln("passed translation")
        val decl = Function_Specification_Parser.checkNsem_function_spec_gen {recursive = recursive} test_function_sem
    in decl end

local open C_AbsEnv HOLogic in
fun handle_declarations translUnit ctxt =
     (let
        fun get_hol_type (C_Env.Parsed ret) params = let
              val base_type =the (C11_TypeSpec_2_CleanTyp.conv_cDeclarationSpecifier_typ (SOME ret))
              fun transform_type ((C_Ast.CArrDeclr0 _)::R) base_type = listT (transform_type R base_type)
                 | transform_type [] base_type = base_type
              in transform_type params base_type end

        fun map_prev_idents (name,(positions,_,data)) =
             case #functionArgs data of C_Ast.None => C_AbsEnv.Identifier(name, if null positions then @{here} else hd positions,get_hol_type (#ret data) (#params data),Global)
             |_=> Identifier(name, @{here},intT,FunctionCategory (Final, NONE))  (*this line is wrong because of different function types*)
        val env = (C_Module.env ctxt)
        (*First we need to get all previously defined global vars and functions*)
        val m = (Symtab.dest (#idents(#var_table(env))))
        val prev_idents =map map_prev_idents m

        (*the new identifiers are returned in reverse \<rightarrow> thus reverse *)
        val (new_idents, call_table) = C_AbsEnv.parseTranslUnitIdentifiers translUnit [] prev_idents Symtab.empty

        val _ = writeln("Call table: "^(@{make_string} call_table))
        val identifiers = (rev new_idents)@prev_idents
        val map_idents = List.map (fn C_AbsEnv.Identifier(name,_,typ,_) => (Binding.name name, transform_type typ, NoSyn))

        fun get_declaration is_global idents = if null idents then I else StateMgt.new_state_record is_global (NONE,idents)
        
        val global_idents = (map_idents (List.filter (fn C_AbsEnv.Identifier(_,_,_,vis) => vis = C_AbsEnv.Global) new_idents))
        val global_declaration =get_declaration true global_idents
             
        val fun_asts = 
              List.map (fn C_AbsEnv.Identifier(name,_,ret_ty,C_AbsEnv.FunctionCategory ast) =>
                     let fun is_recursive NONE = false
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

declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]


C\<open>
int globalvar_different_scope;
\<close>
text\<open>Todo: this fails because of parseTranslUnitIdentifiers - it needs to be rewritten to better
account for previously defined identifiers\<close>

C\<open>int threefunc(){
  return 1+2;
}\<close>

find_theorems threefunc_core

C\<open>
int intarr[][];
int x;
\<close>
term x
find_theorems x
C\<open>
int sum1(int param1,int param2){
  x = threefunc();
  intarr[2][3] = x + param1 + param2;
  return 1;
}

int sum3(int param1,int param2){
  int x; // test to override
  x = sum1(param1, param2);
  return x;
}\<close>
term\<open>global_3_state.x\<close>
find_theorems x

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
  globalvar_different_scope = sum1(v1,v2);
  return globalvar_different_scope;
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
defines "p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C sum1 \<open>(2::int, 3::int)\<close> ; assign_global globalvar_different_scope_update (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p);-
         return\<^bsub>local_testfunction1_state.result_value_update\<^esub> \<open>globalvar_different_scope\<close>"

find_theorems testfunction1_core
term\<open>testfunction1_core\<close>

text \<open>Recursive functions\<close>

rec_function_spec recursive_function1(n::int) returns unit
pre          "\<open>True\<close>" 
post         "\<open>\<lambda>res::unit. True \<close>"
local_vars   localvar1 :: int
defines "if\<^sub>C \<open>n > 0\<close>  
         then (\<open> globalvar_different_scope :=  globalvar_different_scope + 1\<close>);-
               call\<^sub>C recursive_function1 \<open>(n-1)\<close>
         else skip\<^sub>S\<^sub>E 
         fi"


C\<open>
int recursive_function(int n){
  if(n > 0){
    globalvar_different_scope = globalvar_different_scope + 1;
    recursive_function(n-1);
  }
}\<close>

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
int fun_with_pre(int u){
  int local1;
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>2 > 0\<close> */
  /*@ post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>3 > 0\<close> */
  /*@ inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>4 > 0\<close> */
  return local1;
}
int fun_with_pre2(int u){
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>C\<open>u\<close> > 0\<close> */

  return 1;
}
\<close>

ML\<open>

val annotation_data = Clean_Annotation.Data_Clean_Annotations.get (Context.Theory @{theory})
\<close>                                          



