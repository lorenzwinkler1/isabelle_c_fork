(*****************************************************************************
 * MonadicPrograms.thy --- a basic testing theory for programs.
 * Burkhart Wolff and Chantal Keller, LRI, Univ. Paris-Sud, France
 ******************************************************************************)

chapter {* The Clean Language *}
text{* Pronounce : "C lean". *}

theory Clean_old
  imports Clean.Symbex_MonadSE
          "~~/src/HOL/Eisbach/Eisbach"
(*  keywords "global_vars" "local_vars" :: thy_decl 
     and "funct" :: thy_decl

     and "pre" "post" (* "local_vars" *)
     and "returns" 
     and "end_funct" :: thy_goal
*)
begin
  
text{* Clean is a minimalistic imperative language 
with C-like control-flow operators based on a shallow embedding into the
SE exception Monad theory formalized in @{theory "Clean.MonadSE"}. It comprises:
\begin{itemize}
\item C-like control flow with \verb+break+ and \verb+return+.
\item global variables.
\item function calls (seen as Monad-executions) with side-effects, recursion
      and local variables.
\item parameters are modeled via functional abstractions 
      (functions are Monads ...); a passing of parameters to local variables
      might be added later.
\item parametric polymorphism might be added later; at present, states are
      restricted to be monmorphic.
\item cartouche syntax for update operations.
\end{itemize} *}
  
  
chapter {* Proof of concept for a monadic symbolic execution calculus for WHILE programs *}


section\<open> Control-States  \<close>
  
record  control_state = 
          break_val  :: bool
          return_val :: bool
          
typ "('a) control_state_ext"

ML\<open> 
fun typ_2_string_raw (Type(s,S)) = 
        let  val h = if null S then "" else enclose "(" ")" (commas (map typ_2_string_raw S)) ;
        in h ^ s end
   |typ_2_string_raw (TFree(s,_))  = s 
   |typ_2_string_raw (TVar((s,n),_))  = s^(Int.toString n) ;

typ_2_string_raw @{ typ "('a) control_state_ext"}
\<close>


record  mmm = "control_state" +
       df :: "int"

record mmk = "mmm" + dsf :: int 

(* break quites innermost while or for, return quits an entire execution sequence. *)  
definition break :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"
  where   "break \<equiv> (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> break_val := True \<rparr>))"
  
definition unset_break :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"
  where   "unset_break \<equiv> (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> break_val := False \<rparr>))"

definition return :: "'\<alpha> \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"    
  where   "return x = (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> return_val := True \<rparr>))"
    
definition unset_return :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"    
  where   "unset_return  = (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> return_val := False \<rparr>))"
    
definition exec_stop :: "('\<sigma>_ext) control_state_ext \<Rightarrow> bool"
  where   "exec_stop = (\<lambda> \<sigma>. break_val \<sigma> \<or> return_val \<sigma> )"

text\<open> A "lifter" that embeds a state transformer into the state-exception monad. \<close>

consts syntax_assign :: "('\<alpha>  \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> term" (infix ":=" 60)

definition assign :: "('\<sigma> control_state_scheme  \<Rightarrow> 
                       '\<sigma> control_state_scheme) \<Rightarrow> 
                      (unit, '\<sigma> control_state_scheme) MON\<^sub>S\<^sub>E"
  where   "assign \<U> = (\<lambda>\<sigma>. if break_val \<sigma> \<or> return_val \<sigma>
                           then Some((), \<sigma>) else Some((), \<U> \<sigma>))"

definition if\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n :: "['\<sigma> control_state_ext \<Rightarrow> bool, 
                      ('\<beta>, '\<sigma> control_state_ext) MON\<^sub>S\<^sub>E, 
                      ('\<beta>, '\<sigma> control_state_ext) MON\<^sub>S\<^sub>E] \<Rightarrow>
                     ('\<beta>, '\<sigma> control_state_ext) MON\<^sub>S\<^sub>E"
  where   "if\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n \<B> T F = (\<lambda>\<sigma>. if break_val \<sigma> \<or> return_val \<sigma>
                              then Some (undefined, \<sigma>) \<comment>
                            \<open>state unchanged, return arbitrary\<close>
                              else if \<B> \<sigma> then T \<sigma> else F \<sigma>)"     

end