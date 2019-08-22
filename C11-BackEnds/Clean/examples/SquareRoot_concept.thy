(*****************************************************************************
 * SquareRoot_concept.thy --- Example of monadic symbolic execution for a WHILE program.
 * Burkhart Wolff and Chantal Keller, LRI, Univ. Paris-Sud, France
 ******************************************************************************)

chapter {* Proof of concept for a monadic symbolic execution calculus for WHILE programs *}

theory SquareRoot_concept
imports Clean.Clean
begin


section{* Re-visiting the squareroot program example *}

text\<open>The state is just a record; and the global variables correspond to fields in this
     record. This corresponds to typed, structured, non-aliasing states.
     Note that the types in the state can be arbitrary HOL-types - want to have
     sets of functions in a ghost-field ? No problem !
    \<close>

text\<open> The state of the square-root program looks like this : \<close>

typ "Clean.control_state"

ML\<open>
val Type(s,t) = StateMgt_core.get_state_type_global @{theory}
val Type(u,v) = @{typ unit}
\<close>

global_vars state
   tm    :: int
   i     :: int
   sqsum :: int
   a     :: int



txt\<open> The program and the property under test \<close>

lemma 
assumes annotated_program: 
         "\<sigma>\<^sub>0 \<Turnstile> assume\<^sub>S\<^sub>E \<open>0 \<le> a\<close> ;- 
               \<open>tm := 1\<close> ;-
               \<open>sqsum := 1\<close> ;-
               \<open>i := 0\<close> ;-
               (while\<^sub>S\<^sub>E \<open>sqsum <= a\<close> do 
                  \<open>i := i+1\<close> ;-
                  \<open>tm := tm + 2\<close> ;-
                  \<open>sqsum := tm + sqsum\<close>
               od) ;-
               assert\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<sigma>=\<sigma>\<^sub>R)"
shows "\<sigma>\<^sub>R \<Turnstile>assert\<^sub>S\<^sub>E \<open>i * i \<le> a \<and> a < (i + 1) * (i + 1)\<close> "
oops


(* TODO: automate this *)
text\<open> Some lemmas to reason about memory\<close>

lemma tm_simp : "tm (\<sigma>\<lparr>tm := t\<rparr>) = t"
  using [[simp_trace]]  by simp
(* from trace:
   [1]Procedure "record" produced rewrite rule:
   tm (?r\<lparr>tm := ?k\<rparr>) \<equiv> ?k 

   Unfortunately, this lemma is not exported ... It looks as if it is computed on the fly ...
   This could explain why this is slow for our purposes ...
*)
lemma tm_simp1 : "tm (\<sigma>\<lparr>sqsum := s\<rparr>) = tm \<sigma>" by simp
lemma tm_simp2 : "tm (\<sigma>\<lparr>i := s\<rparr>) = tm \<sigma>" by simp
lemma tm_simp3 : "tm (\<sigma>\<lparr>a := s\<rparr>) = tm \<sigma>" by simp
lemma sqsum_simp : "sqsum (\<sigma>\<lparr>sqsum := s\<rparr>) = s" by simp
lemma sqsum_simp1 : "sqsum (\<sigma>\<lparr>tm := t\<rparr>) = sqsum \<sigma>" by simp
lemma sqsum_simp2 : "sqsum (\<sigma>\<lparr>i := t\<rparr>) = sqsum \<sigma>" by simp
lemma sqsum_simp3 : "sqsum (\<sigma>\<lparr>a := t\<rparr>) = sqsum \<sigma>" by simp
lemma i_simp : "i (\<sigma>\<lparr>i := i'\<rparr>) = i'" by simp
lemma i_simp1 : "i (\<sigma>\<lparr>tm := i'\<rparr>) = i \<sigma>" by simp
lemma i_simp2 : "i (\<sigma>\<lparr>sqsum := i'\<rparr>) = i \<sigma>" by simp
lemma i_simp3 : "i (\<sigma>\<lparr>a := i'\<rparr>) = i \<sigma>" by simp
lemma a_simp : "a (\<sigma>\<lparr>a := a'\<rparr>) = a'" by simp
lemma a_simp1 : "a (\<sigma>\<lparr>tm := a'\<rparr>) = a \<sigma>" by simp
lemma a_simp2 : "a (\<sigma>\<lparr>sqsum := a'\<rparr>) = a \<sigma>" by simp
lemma a_simp3 : "a (\<sigma>\<lparr>i := a'\<rparr>) = a \<sigma>" by simp

lemmas memory_theory =
  tm_simp tm_simp1 tm_simp2 tm_simp3
  sqsum_simp sqsum_simp1 sqsum_simp2 sqsum_simp3
  i_simp i_simp1 i_simp2 i_simp3
  a_simp a_simp1 a_simp2 a_simp3
declare memory_theory [memory_theory]



text\<open> Now we run a symbolic execution. We run match-tactics (rather than the Isabelle simplifier 
      which would do the trick as well) in order to demonstrate an efficient way for symbolic 
      execution in Isabelle. \<close>



lemma 
assumes annotated_program: 
         "\<sigma>\<^sub>0 \<Turnstile> assume\<^sub>S\<^sub>E \<open>0 \<le> a\<close> ;- 
               \<open>tm := 1\<close> ;-
               \<open>sqsum := 1\<close> ;-
               \<open>i := 0\<close> ;-
               (while\<^sub>S\<^sub>E \<open>sqsum <= a\<close> do 
                  \<open>i := i+1\<close> ;-
                  \<open>tm := tm + 2\<close> ;-
                  \<open>sqsum := tm + sqsum\<close>
               od) ;-
               assert\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<sigma>=\<sigma>\<^sub>R)"
       shows "\<sigma>\<^sub>R \<Turnstile>assert\<^sub>S\<^sub>E \<open>i * i \<le> a \<and> a < (i + 1) * (i + 1)\<close> "
  oops
(*
apply(insert annotated_program)
apply(tactic "ematch_tac @{context} [@{thm \"assume_E'\"}] 1")
apply(tactic "dmatch_tac @{context} [@{thm \"exec_assignD'\"}] 1")+
apply(tactic "dmatch_tac @{context} [@{thm \"exec_whileD\"}] 1")
apply(tactic "ematch_tac @{context} [@{thm \"if_SE_execE''\"}] 1")
apply(simp_all only: memory_theory MonadSE.bind_assoc')
apply(tactic "dmatch_tac @{context} [@{thm \"exec_assignD'\"}] 1")+
apply(tactic "dmatch_tac @{context} [@{thm \"exec_whileD\"}] 1")
apply(tactic "ematch_tac @{context} [@{thm \"if_SE_execE''\"}] 1")
apply(simp_all only: memory_theory MonadSE.bind_assoc')
apply(tactic "dmatch_tac @{context} [@{thm \"exec_assignD'\"}] 1")+
apply(tactic "dmatch_tac @{context} [@{thm \"exec_whileD\"}] 1")
apply(tactic "ematch_tac @{context} [@{thm \"if_SE_execE''\"}] 1")
apply(simp_all only: memory_theory MonadSE.bind_assoc')
 apply(tactic "dmatch_tac @{context} [@{thm \"exec_assignD'\"}] 1")+
apply(simp_all)
text\<open>Here are the test-statements explicit. \<close>

txt\<open>push away the test-hyp: postcond is true for programs with more than
    three loop traversals (criterion: all-paths(k). This reveals explicitly
    the three test-cases for  @{term "k<3"}. \<close>   
defer 1 

txt\<open>Instead of testing, we @{emph \<open>prove\<close>} that the test cases satisfy the
    post-condition for all @{term "k<3"} loop traversals and @{emph \<open>all\<close>} 
    positive inputs @{term "a \<sigma>"}.\<close>     
apply(auto  simp: assert_simp)
oops

(* TODO Develop a Hoare-Calculus with WP *) 

(* TODO Re-Develop IMP for Program testing *) 


text\<open> Using the automatic covering tactics \<close>
*)
lemma 
assumes annotated_program: 
         "\<sigma>\<^sub>0 \<Turnstile> assume\<^sub>S\<^sub>E \<open>0 \<le> a\<close> ;- 
               \<open>tm := 1\<close> ;-
               \<open>sqsum := 1\<close> ;-
               \<open>i := 0\<close> ;-
               (while\<^sub>S\<^sub>E \<open>sqsum <= a\<close> do 
                  \<open>i := i+1\<close> ;-
                  \<open>tm := tm + 2\<close> ;-
                  \<open>sqsum := tm + sqsum\<close>
               od) ;-
               assert\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<sigma>=\<sigma>\<^sub>R)"
shows "\<sigma>\<^sub>R \<Turnstile>assert\<^sub>S\<^sub>E \<open>i * i \<le> a \<and> a < (i + 1) * (i + 1)\<close> "
(*
  
  apply(insert annotated_program)

txt\<open>Automatically unrolls the loop 10 times using branch coverage criterion\<close>
apply (mcdc_and_loop_coverage "Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))")
(* Takes 22s for 100 unrollings *)
(* apply (mcdc_and_loop_coverage "Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))") *)

text\<open>Here are the test-statements explicit. \<close>

txt\<open>push away the test-hyp: postcond is true for programs with more than
    10 loop traversals (criterion: all-paths(k). This reveals explicitly
    the ten test-cases for @{term "k<10"}. \<close>   
defer 1 

txt\<open>Instead of testing, we @{emph \<open>prove\<close>} that the test cases satisfy the
    post-condition for all @{term "k<10"} loop traversals and @{emph \<open>all\<close>} 
    positive inputs @{term "a \<sigma>"}.\<close>     
apply(auto simp: assert_simp)
*)
oops

end
