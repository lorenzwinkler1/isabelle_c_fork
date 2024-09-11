theory "Coder_Test_TUnits"
  imports "../src/CleanCoder"  (* Coder_Test_Env_AEnv *)
begin
ML\<open>
(*This is an override for the update_Root_Ast function that is registered in C_Command.*)


fun declare_function idents name ast ctxt =
   let  
        val _ = writeln(@{make_string}ast)
        fun get_translated_fun_bdy ctx _ = let 
              val _ = writeln("TRACE 1.1: ")
              val v = ((C11_Ast_Lib.fold_cStatement 
              C11_Stmt_2_Clean.regroup 
              (C11_Stmt_2_Clean.convertStmt true (StateMgt.get_state_type ctx) idents (Proof_Context.theory_of ctx))
              ast []))
              in (writeln("AA"^(@{make_string} v)));hd v end

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

fun handle_declarations translUnit ctxt =
     (let
        val env = (C_Module.env ctxt)
        (* val _ = writeln(@{make_string} translUnit) *)
        (* val _ = writeln(@{make_string} env) *)

       
        val (identifiers, _) = C_AbsEnv.parseTranslUnitIdentifiers translUnit [] Symtab.empty
        fun transform_type typ = if typ = HOLogic.intT then "int" else if typ = HOLogic.natT then "uint" else error "Unknown variable type"
        val map_idents = List.map (fn C_AbsEnv.Identifier(name,_,typ,_) => (Binding.name name, transform_type typ, NoSyn))

        fun get_declaration is_global idents = if null idents then I else StateMgt.new_state_record is_global (NONE,idents)

        val global_declaration =get_declaration true
             (map_idents (List.filter (fn C_AbsEnv.Identifier(_,_,_,vis) => vis = C_AbsEnv.Global) identifiers))
        
        val fun_asts = 
              List.map (fn C_AbsEnv.Identifier(name,_,_,C_AbsEnv.FunctionCategory ast) => case snd ast of SOME value => (name,value)) (
              List.filter (fn a => case a of C_AbsEnv.Identifier(_,_,_,C_AbsEnv.FunctionCategory _) => true | _ => false) identifiers)

        val function_declarations = List.map (fn (name,ast) => declare_function identifiers name ast ctxt) fun_asts

        val function_decl = fold (fn f => fn acc => f acc) function_declarations
    in
     Context.map_theory (function_decl o global_declaration) ctxt
    end);
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
int a;
int testfunction(int param1, int param2){
  return a;
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
local_vars   i :: int
defines " 
         return\<^bsub>local_testfunction1_state.result_value_update\<^esub> \<open>a\<close>"

find_theorems testfunction_core
find_theorems testfunction1_core