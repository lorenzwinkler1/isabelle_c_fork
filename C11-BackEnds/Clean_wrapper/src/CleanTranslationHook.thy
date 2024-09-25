theory "CleanTranslationHook"
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
         | transform_type ps _ = error ("First type parameter unknown (maybe pointers): "^(@{make_string} ps))
      in transform_type params base_type end
    |get_hol_type a _ = error ("Can not get type of \""^(@{make_string} a)^"\"")
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
          The following are helper methods, to obtain the function get_invariant::positiona \<rightarrow> (context\<rightarrow>term) option*)
        val invariants:((string*(Context.generic -> term)*Position.range) list) = List.filter (fn (f_name,_,_) => f_name = name) 
                                                                (#invariants (Clean_Annotation.Data_Clean_Annotations.get ctxt)) 
        val measures:((string*(Context.generic -> term)*Position.range) list) = List.filter (fn (f_name,_,_) => f_name = name) 
                                                                (#measures (Clean_Annotation.Data_Clean_Annotations.get ctxt))                                                                                                       
        val loop_pos =Library.distinct (op =) (C11_Ast_Lib.fold_cStatement (fn a => fn b => a@b) C11_Unit_2_Clean.get_loop_positions ast [])
        fun compare_pos ((C_Ast.Position0 (pos1,_,_,_)),(C_Ast.Position0 (pos2,_,_,_))) = Int.compare (pos1,pos2)
            |compare_pos a = error ("Unable to compare positions (for invariants and measures): "^(@{make_string} a))
        val loop_pos_sorted = Library.sort compare_pos loop_pos 
        fun range_less_than_pos (range:Position.range) (C_Ast.Position0 (pos,_,_,_)) = the (Position.offset_of (fst range)) < pos
           |range_less_than_pos a b = error ("Unable to compare positions (for invariants and measures): "^(@{make_string} (a,b)))
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
                              | (pos1::_) => if pos3 = pos1 then SOME inv else NONE
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
        val prev_idents =map map_env_ident_to_identifier (Symtab.dest (#idents(#var_table(env))))
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
                  (name,the (snd ast),ret_ty,  is_recursive (Symtab.lookup call_table name)) end
                      | ident => error ("Expected function identifier. Instead: "^(@{make_string} ident)))
                          
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
setup \<open>C_Module.C_Term.map_expression 
    (fn cexpr => fn _ => fn ctxt => let 
    val sigma_i = (StateMgt.get_state_type o Context.proof_of )ctxt
    val env = C_Module.Data_Surrounding_Env.get ctxt
    val idents =  (Symtab.dest (#idents(#var_table(env))))
    val A_env = List.map map_env_ident_to_identifier idents
    val expr = (hd (C11_Ast_Lib.fold_cExpression (K I) 
                                      (C11_Expr_2_Clean.convertExpr false sigma_i  A_env  (Context.theory_of ctxt) "" (K NONE))
                                      cexpr [])) handle ERROR msg => (writeln("ERROR: "^(@{make_string}msg));@{term "1::int"})
in
  expr
 end)\<close>
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
                                      (C11_Expr_2_Clean.convertExpr false sigma_i  A_env  (Context.theory_of ctxt) "" (K NONE))
                                      cexpr [])) handle ERROR msg => (writeln("ERROR: "^(@{make_string}msg));@{term "1::int"})
in
  expr
 end)\<close>

end