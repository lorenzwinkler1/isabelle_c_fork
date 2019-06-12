(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * Monads.thy --- a base testing theory for sequential computations.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
 *               2009-2017 Univ. Paris-Sud, France 
 *               2009-2012 Achim D. Brucker, Germany
 *               2015-2017 University Sheffield, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)
(* $Id:$ *)

chapter {* Basic Monad Theory for Sequential Computations *}

  section{*General Framework for Monad-based Sequence-Test *}
text{* As such, Higher-order Logic as a purely functional specification
       formalism has no built-in mechanism for state and state-transitions.
       Forms of testing involving state require therefore explicit mechanisms 
       for their treatment inside the logic; a well-known technique to model
       states inside purely functional languages are \emph{monads} made popular
       by Wadler and Moggi and extensively used in Haskell. \HOL is powerful 
       enough to represent the most important \emph{instances} of standard monads; 
       however, it is not possible to represent monads as such due to well-known 
       limitations of the Hindley-Milner type-system (no type-constructor-classes). *}

text{* Here is a variant for state-exception monads, that models precisely
       transition functions with preconditions. Next, we declare the 
       state-backtrack-monad. In all of them, our concept of i/o stepping
       functions can be formulated; these are functions mapping input
       to a given monad. Later on, we will build the usual concepts of:
       \begin{enumerate}
       \item deterministic i/o automata,
       \item non-deterministic i/o automata, and
       \item labelled transition systems (LTS)
       \end{enumerate}
*}

theory Monads 
  imports MonadSE  Seq_MonadSE Symbex_MonadSE Hoare_MonadSE
          MonadSBE Symbex_MonadSBE
begin 

section{* A Generic (Approximative) Notion of Monad *}

text {*
  A (fake) monad is a structure with a return and a bind satisfying three laws.
  Since we cannot use generic type constructors in HOL,
  we formulate monads using only one type 'a and its monadic representation 'am.
*}

locale Monad =
fixes   return :: "'a \<Rightarrow> 'am"  
  and   bind   :: "'am \<Rightarrow> ('a \<Rightarrow> 'am) \<Rightarrow> 'am" (infixr ">>=" 70)
assumes left_unit : "(return x) >>= f = f x"
    and right_unit: "m >>= return = m"
    and assoc     : "(m >>= f) >>= g = m >>= (\<lambda> x . f x >>= g)"
begin

definition pipe :: "'am \<Rightarrow> 'am \<Rightarrow> 'am"
where     "pipe f g \<equiv> bind f (\<lambda> _. g)"

lemma pipe_left_unit : "pipe (return x) f = f"
by(simp add: left_unit pipe_def)


lemma pipe_right_unit : "pipe f (return x) = f"
oops (* Not possible to formulate in this Monad Framework generically ! ! !
        In the concrete SE-Monad, we have the (interesting) special case: 
        "(m;- (return ())) = m"  *)

lemma pipe_assoc : "pipe f (pipe g h) = pipe (pipe f g) h"
by(simp add: assoc pipe_def)

primrec Mrun :: "('b \<Rightarrow> 'a \<Rightarrow> 'am) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> 'am"
where  "Mrun m []     = return"
     | "Mrun m (b#bs) = (\<lambda> a . Mrun m bs a >>= m b)"

end

  
interpretation SE : Monad unit_SE bind_SE
  by unfold_locales (simp_all)

interpretation SBE : Monad unit_SBE bind_SBE
  by unfold_locales (simp_all add:  bind_left_unit_SBE  bind_right_unit_SBE bind_assoc_SBE)



    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
subsection{* Legacy Bindings *}


lemma valid_true[simp]: (* legacy: special case *)
  "(\<sigma> \<Turnstile> (s \<leftarrow> result x ; result (P s))) = P x" by simp


(*
lemmas valid_both = exec_mbindFSave (* legacy *)
lemmas valid_success = exec_mbindFSave_success (* legacy *)
lemmas valid_success'' = exec_mbindFSave_success(* legacy *)
lemmas valid_success' = exec_bind_SE_success (* legacy *)
lemmas valid_failure = exec_mbindFSave_failure (* legacy : *)
lemmas valid_failure' = exec_bind_SE_failure (* legacy *)
lemmas valid_failure''=valid_failure (* legacy : *)
lemmas valid_failure''' = exec_mbindFStop_failure (* legacy : *)
lemmas valid_propagate_fail = exec_fail_SE (* legacy *)
lemmas valid_propagate_fail' = exec_fail_SE' (* legacy *)
lemmas valid_propoagate_3' = valid_propagate_fail' (* legacy *)
lemmas valid_propagate_2 = exec_bind_SE_success''(* legacy *)
lemmas valid_propagate_1 = exec_unit_SE (* legacy *)
lemmas valid_successElem = exec_bind_SE_success' (* legacy *)
lemmas valid_propagate_2' = exec_bind_SE_success'''(* legacy *)
lemmas valid_propagate_2'' = exec_bind_SE_success'''' (* legacy *)
lemmas valid_propoagate_3 = exec_unit_SE' (* legacy *)
  *)
(* legacy ?: 
lemma valid_success'':
"ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow>
   (\<sigma>  \<Turnstile> (s \<leftarrow> mbind (a#S) ioprog ; return (P s))) =
   (\<sigma>' \<Turnstile> (s \<leftarrow> mbind S ioprog ; return (P (b#s))))"
unfolding valid_SE_def unit_SE_def bind_SE_def 
by(cases "mbind S ioprog \<sigma>'", auto)
*) 




end
