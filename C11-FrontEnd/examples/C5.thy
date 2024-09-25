theory C5
  imports "Isabelle_C.C_Main"
begin

(*This file contains some ways to retrieve the C-environment*)

ML\<open>
val SPY_ENV =  Unsynchronized.ref(NONE:C_Env.env_lang option);\<close>
declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]

C\<open>
int globalvar1;
void test(int param1){
  int localvariable1;
  
  return 12;   /*@ \<approx>setup \<open>fn _ => fn _ => fn env => 
               (*The environment can be retrieved using the generic setup command*)
               ((SPY_ENV := SOME env);I) \<close> */;
  int localvariable2;
}
int globalvar2;
\<close>

ML\<open>
(*We can see that the saved env in fact has all the current variables*)
val saved_vars = (map (fn (a,(_,_,b)) => (a,#scope b)) (Symtab.dest (
 #idents(#var_table(the (!SPY_ENV))))
))
val final_vars = (map (fn (a,(_,_,b)) => (a,#scope b)) (Symtab.dest (
 #idents(#var_table(@{C\<^sub>e\<^sub>n\<^sub>v})))))
\<close>

(*There is a second way to achieve the same, using the context*)
C\<open>
int globalvar3;
void test2(int param1){
  int localvariable3;
  
  return 12;   /*@ \<approx>setup \<open>fn _ => fn _ => fn _ => fn ctx =>
               (*The environment can be retrieved using the generic setup command*)
               ((SPY_ENV := SOME (snd (C_Stack.Data_Lang.get' ctx)));ctx) \<close> */;
  int localvariable4;
}
int globalvar4;
\<close>

ML\<open>
(*We can see that the saved env in fact has all the current variables*)
val saved_vars = (map (fn (a,(_,_,b)) => (a,#scope b)) (Symtab.dest (
 #idents(#var_table(the (!SPY_ENV))))
))
\<close>


(*Declaring a seperate antiquotation *)

ML\<open>
val env = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>

ML\<open>
Theory.setup
  (C_Inner_Syntax.command_no_range
       (C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup
         \<open>fn ((_, (_, pos1, pos2)) :: _) =>
              (fn _ => fn _ =>
                tap (fn ctx =>
                      (SPY_ENV := SOME (snd (C_Stack.Data_Lang.get' ctx));Position.reports_text [((Position.range (pos1, pos2)
                                               |> Position.range_position, Markup.intensify), "")])))
           | _ => fn _ => fn _ => I\<close>)
       ("store_and_highlight", \<^here>, \<^here>))
\<close>

(*this is btw how all previous identifiers can get deleted*)
setup\<open>Context.theory_map (C_Module.Data_In_Env.put C_Env.empty_env_lang)\<close>

C\<open>
int globalvar3;
void test2(int param1){
  int localvariable3;/*@ store_and_highlight */
}
\<close>

ML\<open>
val saved_vars = (map (fn (a,(_,_,b)) => (a,#scope b)) (Symtab.dest (
 #idents(#var_table(the (!SPY_ENV)))) (*NOTE: localvariable3 is in the environment*)
))\<close>

setup\<open>Context.theory_map (C_Module.Data_In_Env.put C_Env.empty_env_lang)\<close>

C\<open>
int globalvar3;
void test2(int param1){
  int localvariable3;/*@@@@@ store_and_highlight */
}
\<close>
ML\<open>
val saved_vars = (map (fn (a,(_,_,b)) => (a,#scope b)) (Symtab.dest (
 #idents(#var_table(the (!SPY_ENV)))) (*NOTE: localvariable3 is NOT in the environment*)
))\<close>