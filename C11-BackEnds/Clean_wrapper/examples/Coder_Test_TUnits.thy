theory "Coder_Test_TUnits"
  imports "../src/CleanCoder"  (* Coder_Test_Env_AEnv *)
begin
ML\<open>
(*This is an override for the update_Root_Ast function that is registered in C_Command.*)



fun handle_declarations translUnit ctxt =
     (let
        val env = (C_Module.env ctxt)
        val _ = writeln(@{make_string} translUnit)
        val _ = writeln(@{make_string} env)

       
        val (identifiers, _) = C_AbsEnv.parseTranslUnitIdentifiers translUnit [] Symtab.empty
        fun transform_type typ = if typ = HOLogic.intT then "int" else if typ = HOLogic.natT then "uint" else error "Unknown variable type"
        val map_idents = List.map (fn C_AbsEnv.Identifier(name,_,typ,_) => (Binding.name name, transform_type typ, NoSyn))

        fun get_declaration is_global idents = if null idents then I else StateMgt.new_state_record is_global (NONE,idents)

        val global_declaration =get_declaration true
             (map_idents (List.filter (fn C_AbsEnv.Identifier(_,_,_,vis) => vis = C_AbsEnv.Global) identifiers))
        
        val local_declaration =get_declaration false 
             (map_idents (List.filter (fn C_AbsEnv.Identifier(_,_,_,vis) => case vis of C_AbsEnv.Local _ => true | _ =>false) identifiers))
    in
     Context.map_theory (local_declaration o global_declaration) ctxt
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
int test(){
  int xyz;
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

find_theorems b