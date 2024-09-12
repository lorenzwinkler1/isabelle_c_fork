theory "Coder_Test_TUnits"
  imports "../src/CleanCoder"  (* Coder_Test_Env_AEnv *)
begin
ML\<open>
(*This is an override for the update_Root_Ast function that is registered in C_Command.*)


fun declare_function idents name ast ctxt =
   let  
        fun get_translated_fun_bdy ctx _ = let 
              val v = ((C11_Ast_Lib.fold_cStatement 
              C11_Stmt_2_Clean.regroup 
              (C11_Stmt_2_Clean.convertStmt false (StateMgt.get_state_type ctx) idents (Proof_Context.theory_of ctx))
              ast []))
              in hd v end

        val test_function_sem = {binding = Binding.name name,
                                 locals = [(Binding.name "localvar1","int", NoSyn)], (*There needs to be at least one local variable*)
                                 params = [(Binding.name "param1","int"),(Binding.name "param2","int")],
                                 ret_type = "int",
                                 read_pre = fn ctx => Abs ("\<sigma>",(StateMgt.get_state_type ctx), @{term True}),
                                 read_post = fn ctx => Abs ("\<sigma>",(StateMgt.get_state_type ctx), Abs ("ret",@{typ int}, @{term True})),
                                 read_variant_opt = NONE,
                                 read_body = get_translated_fun_bdy}
        val decl = Function_Specification_Parser.checkNsem_function_spec_gen {recursive = false} test_function_sem
    in decl end

local open C_AbsEnv HOLogic in
fun handle_declarations translUnit ctxt =
     (let
        fun map_prev_idents (name,(positions,_,data)) =
             case #functionArgs data of C_Ast.None => C_AbsEnv.Identifier(name, if null positions then @{here} else hd positions,intT,Global)
             |_=> Identifier(name, @{here},intT,FunctionCategory (Final, NONE))  (*this line is wrong because of different function types*)
        val env = (C_Module.env ctxt)
        (*First we need to get all previously defined global vars and functions*)
        val m = (Symtab.dest (#idents(#var_table(env))))
        val prev_idents =map map_prev_idents m
        val (new_idents, _) = C_AbsEnv.parseTranslUnitIdentifiers translUnit [] prev_idents Symtab.empty
        val identifiers = new_idents@prev_idents
        fun transform_type typ = if typ = HOLogic.intT then "int" else if typ = HOLogic.natT then "uint" else error "Unknown variable type"
        val map_idents = List.map (fn C_AbsEnv.Identifier(name,_,typ,_) => (Binding.name name, transform_type typ, NoSyn))

        fun get_declaration is_global idents = if null idents then I else StateMgt.new_state_record is_global (NONE,idents)

        val global_declaration =get_declaration true
             (map_idents (List.filter (fn C_AbsEnv.Identifier(_,_,_,vis) => vis = C_AbsEnv.Global) new_idents))
        val fun_asts = 
              List.map (fn C_AbsEnv.Identifier(name,_,_,C_AbsEnv.FunctionCategory ast) => case snd ast of SOME value => (name,value)) (
              List.filter (fn a => case a of C_AbsEnv.Identifier(_,_,_,C_AbsEnv.FunctionCategory _) => true | _ => false) new_idents)
        val function_declarations = List.map (fn (name,ast) => declare_function identifiers name ast ctxt) fun_asts

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
int sum1(int param1,int param2){
  globalvar_different_scope = param1 + param2;
  return globalvar_different_scope;
}
\<close>

find_theorems sum1
term\<open>sum1\<close>

C\<open>
int a;
int testfunction(int param1, int param2){
  globalvar_different_scope = sum1(param1,param2);
  return globalvar_different_scope;
}
\<close>

C\<open>
int b;
\<close>


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