(******************************************************************************
 * Isabelle/C/AutoCorres
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
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
(* For the C - example:
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

chapter \<open>Example: A Sqrt Prime Sample Proof\<close>

text\<open>This example is used to demonstrate Isabelle/C/AutoCorres in a version that keeps
the theory development of the background theory as well as the program annotations completely 
\<^emph>\<open>outside\<close> the C source. This particular development style that keeps the program
separate from its theory we call CET (\<^emph>\<open>Code embedded-in Theory\<close>). It has the 
advantage that developers of development and verification teams can be separated,
as is required by many certification standards.
Note that the opposite style that we call TEC (\<^emph>\<open>Theory embedded-in Code\<close>) is also 
supported by Isabelle/C. In TEC style, Programs become a kind of ``proof-carrying (high-level) code''.
Exports of the C-sources will contain their theory (not only their annotations) as comments
\<^emph>\<open>inside\<close> which might be also useful in certification as well as advanced  
``proof-carrying code'' securization schemes of server platforms. 

Of course, since developments can mix C code and HOL developments in an arbitrary manner,
these two style have to be thought of as extremes in a continuum. \<close>


theory IsPrime_sqrt_CAS
imports
  Isabelle_C_AutoCorres.AutoCorres_Wrapper
  "HOL-Computational_Algebra.Primes"
begin
\<comment> \<open>Derived from: \<^file>\<open>../../../src_ext/l4v/src/tools/autocorres/tests/examples/IsPrime.thy\<close>\<close>

section\<open>The Theory of the \<open>O(sqrt(n))\<close> Primality Test Algorithm\<close>
text\<open>This section develops basic concepts of the invariant. This bit is presented here \<^emph>\<open>before\<close>
the actual code, but could also be after or even inside the \<^theory_text>\<open>C\<close> command as comment-annotation of 
the source.\<close>


text\<open>The example is non-trivial both from the C semantics side as well as from its 
algorithmic side. 
\<^enum> From the C side: it is far from trivial to see that the precondition
  @{term "\<lambda>\<sigma>. n \<le> UINT_MAX"} suffices to make sure that no arithmetic
  overflow occurs.
\<^enum> From the algorithmic side: the (small) amount of number theory required by
  this exercise makes it impossible for automated provers to establish the result
  without additional nonlinear axioms, i.e. the background theory is non-trivial.
  In our example, everything is proven, the TCB of this verification resides
  only on:
  \<^item> The logical consistency of HOL and its correct implementation in Isabelle/HOL, and
  \<^item> that the assumptions of AutoCorres wrt. to the underlying C-semantics
    are valid. \<close>



definition
  "partial_prime p (n :: nat) \<equiv>  (1 < p \<and> (\<forall>i \<in> {2 ..< min p n}. \<not> i dvd p))"

lemma partial_prime_ge [simp]:
     "\<lbrakk> p' \<ge> p \<rbrakk> \<Longrightarrow> partial_prime p p' = prime p"
  by (clarsimp simp: partial_prime_def prime_nat_iff' min_def)

lemma divide_self_plus_one [simp]: "(x dvd Suc x) = (x = 1)"
  apply (case_tac "x = 0", simp)
  apply (case_tac "x = 1", simp)
  apply (clarsimp simp: dvd_def)
  apply (case_tac "k = 0", simp)
  apply (case_tac "k = 1", simp)
  apply (subgoal_tac "x * 2 \<le> x * k")
   apply (subgoal_tac "Suc x < x * 2")
    apply simp
   apply clarsimp
  apply clarsimp
  done

lemma partial_prime_Suc [simp]:
  "partial_prime p (Suc n)
              = (partial_prime p n \<and> (1 < n \<and> Suc n < p \<longrightarrow> \<not> n dvd p))"
   apply (clarsimp simp: partial_prime_def min_def atLeastLessThanSuc not_le)
  apply (case_tac "p = Suc n")
   apply (clarsimp simp: atLeastLessThanSuc)
  apply fastforce
  done

lemma partial_prime_2 [simp]: "(partial_prime a 2) = (a > 1)"
  by (clarsimp simp: partial_prime_def)

lemma not_prime:
    "\<lbrakk> \<not> prime (a :: nat); a > 1 \<rbrakk> \<Longrightarrow> \<exists>x y. x * y = a \<and> 1 < x \<and> 1 < y \<and> x * x \<le> a"
  apply (clarsimp simp: prime_nat_iff dvd_def)
  apply (case_tac "m > k")
   apply (metis Suc_lessD Suc_lessI less_imp_le_nat mult.commute nat_0_less_mult_iff nat_mult_less_cancel_disj)
  apply fastforce
  done

lemma sqrt_prime:
  "\<lbrakk> a * a > n; \<forall>x<a. (x dvd n) = (x = Suc 0 \<or> x = n); 1 < n \<rbrakk> \<Longrightarrow> prime n"
  apply (rule ccontr)
  apply (drule not_prime)
   apply clarsimp
  apply (metis dvd_triv_right less_le_trans mult.commute mult_le_cancel2
           One_nat_def less_eq_nat.simps(1) less_not_refl2
           mult_eq_self_implies_10 not_less)
  done

lemma partial_prime_sqr [simp]:
     "\<lbrakk> n * n > p \<rbrakk> \<Longrightarrow> partial_prime p n = prime p"
  apply (case_tac "n \<ge> p")
   apply clarsimp
  apply (case_tac "partial_prime p n")
   apply clarsimp
   apply (erule sqrt_prime)
    apply (clarsimp simp: partial_prime_def)
    apply (case_tac "x = 0", simp)
    apply (case_tac "x = 1", simp)
    apply (frule_tac x=x in bspec)
     apply (clarsimp simp: min_def)
    apply clarsimp
   apply (clarsimp simp: not_le partial_prime_def)
  apply (case_tac "p = 0", simp)
  apply (case_tac "p = 1", simp)
  apply (auto simp: not_le partial_prime_def min_def prime_nat_iff')
  done

lemma prime_dvd [simp]:
    "\<lbrakk> prime (p::nat) \<rbrakk> \<Longrightarrow> (r dvd p) = (r = 1 \<or> r = p)"
  by (fastforce simp: prime_nat_iff)

section\<open>The C code for \<open>O(sqrt(n))\<close> Primality Test Algorithm\<close>

text\<open> This C code contains a function that determines if the given number 
      @{term n} is prime.

      It returns 0 if @{term n}  is composite, or non-zero if @{term n}  is prime.
 
      This is a faster version than a linear primality test; runs in O(sqrt(n)). \<close>

declare [[AutoCorres]]
(*
C \<open>
//  Setup of AutoCorres for semantically representing this C element.
//@ install_autocorres is_prime [ ts_rules = nondet, unsigned_word_abs =  is_prime ]
int A;  /* dummy */
\<close>
*)

setup \<open>C_Module.C_Term.map_expression
        (fn expr => fn _ => fn _ => 
          case expr of C_Ast.CVar0 (C_Ast.Ident0 (_, x, _), _) =>
                         Free (C_Grammar_Rule_Lib.ident_decode x, dummyT)
                     | s => Free (\<^make_string> s, dummyT))\<close>

C \<open>
     #define SQRT_UINT_MAX 65536
     
     unsigned int is_prime(unsigned int n)
       //@ +@ requires \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>n\<close> \<le> UINT_MAX\<close>
       //@ +@ ensures  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>is_prime(n)\<close> \<noteq> 0 \<longleftrightarrow> prime \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>n\<close>\<close>
     {
       if (n < 2) return 0;
     
       for (unsigned i = 2; i < SQRT_UINT_MAX && i * i <= n; i++)
         //@ definition \<comment> \<open>outer\<close>  is_prime_inv where [simp]:  \<open>is_prime_inv n i s \<equiv> (1 < i \<and> i \<le> n \<and> i \<le> SQRT_UINT_MAX \<and> i * i \<le> SQRT_UINT_MAX * SQRT_UINT_MAX \<and> partial_prime n i)\<close>
         //@ invariant  \<comment> \<open>inner\<close> \<open>is_prime_inv \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>n\<close>\<close>
         //@ measure    \<comment> \<open>inner\<close> \<open>\<lambda>(r, s). (Suc \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>n\<close>) * (Suc \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>n\<close>) - r * r\<close>
         //@ term       \<comment> \<open>outer\<close> \<open>is_prime_inv \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>n\<close> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>i\<close> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>s\<close>\<close>
       {
         if (n % i == 0) return 0; 
       }
       return 1;
     }

     //@ install_autocorres is_prime [ ts_rules=nondet, unsigned_word_abs=is_prime ]
\<close>

section\<open>The Results of the AutoCorres Evaluation\<close>

C_export_file  (* This exports the C code into a C file ready to be compiled by gcc. *)

text\<open>AutoCorres produced internally the following definitions of this input:\<close>
find_theorems name:is_prime

text\<open>The following definitions are key importance: they represent the C program
     as a HOL function over a state modeling modeled by AutoCorres for the given 
     C program.\<close>
thm is_prime_global_addresses.is_prime_body_def
thm is_prime.is_prime'_def   
thm SQRT_UINT_MAX_def

text\<open>Note that the pre-processor macro has been converted into a definition in HOL.\<close>


section\<open>Preliminaries of the Proof\<close>
text\<open>This section contains the auxilliary definitions and lemmas for the 
     final correctness proof; in particular, it uses the loop invariant.\<close>

lemma uint_max_factor [simp]:  "UINT_MAX = SQRT_UINT_MAX * SQRT_UINT_MAX - 1"
  by (clarsimp simp: UINT_MAX_def SQRT_UINT_MAX_def)

lemma sqr_less_mono [simp]:
    "((i::nat) * i < j * j) = (i < j)" 
  by (meson le_def mult_le_mono mult_strict_mono' zero_le)

lemma [simp]: "(a - b < a - c) = ((b::nat) > c \<and> c < a)"
  by arith

declare mult_le_mono [intro]

lemma sqr_le_sqr_minus_1 [simp]:
    "\<lbrakk> b \<noteq> 0 \<rbrakk> \<Longrightarrow> (a * a \<le> b * b - Suc 0) = (a < b)"
  by (metis gr0I sqr_less_mono nat_0_less_mult_iff nat_le_Suc_less)



section\<open>The Correctness Proof \<close>

text\<open>Note that the proof \<^emph>\<open>injects\<close> the loop invariant at the point where the proof
     treats the loop.\<close>

theorem (in is_prime) is_prime_faster_correct:
  notes times_nat.simps(2) [simp del] mult_Suc_right [simp del]
  shows "\<lbrace> \<lambda>s. n \<le> UINT_MAX \<rbrace> is_prime' n \<lbrace> \<lambda>r s. (r \<noteq> 0) \<longleftrightarrow> prime n \<rbrace>!"
  apply (rule validNF_assume_pre)
  apply (case_tac "n = 0")
   apply (clarsimp simp: is_prime'_def, wp, simp)[1]
  apply (case_tac "n = 1")
   apply (clarsimp simp: is_prime'_def, wp, simp)[1]
  apply (unfold is_prime'_annot dvd_eq_mod_eq_0 [symmetric] SQRT_UINT_MAX_def [symmetric])
   apply wp
    apply clarsimp
    apply (metis One_nat_def Suc_leI Suc_lessD order_leE prime_dvd leD mult_le_mono n_less_n_mult_m)
   apply (fastforce elim: order_leE simp: partial_prime_sqr)   
  apply (clarsimp simp: SQRT_UINT_MAX_def)
  done

(* we pimp up the logical context such that the final auto constructs the proof "automatically". *)

lemma aux5[simp]:"(2::nat) \<le> SQRT_UINT_MAX" by(simp add: SQRT_UINT_MAX_def)
lemma aux6[simp]:"(4::nat) \<le> SQRT_UINT_MAX * SQRT_UINT_MAX" by(simp add: SQRT_UINT_MAX_def)
lemma aux7[simp]: 
" r < SQRT_UINT_MAX \<Longrightarrow>   Suc (r + (r + r * r)) \<le> SQRT_UINT_MAX * SQRT_UINT_MAX"
  by (metis Suc_le_eq add_Suc  mult.commute mult_Suc mult_Suc_right not_less sqr_less_mono)          
lemma aux8[simp]:
"Suc r < SQRT_UINT_MAX \<Longrightarrow> Suc (r + (r + r * r)) \<le> SQRT_UINT_MAX * SQRT_UINT_MAX - Suc 0" 
by (metis add_Suc le0 mult.commute mult_Suc mult_Suc_right not_less sqr_le_sqr_minus_1)
lemma aux9[simp]:
" r \<le> n \<Longrightarrow>  \<not> r dvd n \<Longrightarrow> Suc r \<le> n"
  using not_less_eq_eq by force




theorem (in is_prime) is_prime_correct':
    "\<lbrace> \<lambda>\<sigma>. n \<le> UINT_MAX \<rbrace> is_prime' n \<lbrace> \<lambda>res \<sigma>. (res \<noteq> 0) \<longleftrightarrow> prime n \<rbrace>!"
proof (rule validNF_assume_pre)
  assume 1 : "n \<le> UINT_MAX"
  have   2 : "n = 0 \<or> n = 1 \<or> n > 1" by linarith
  show ?thesis
    proof (insert 2, elim disjE)
      assume "n = 0" then show ?thesis   by (clarsimp simp: is_prime'_def, wp, auto)
    next
      assume "n = 1" then show ?thesis   by (clarsimp simp: is_prime'_def, wp, auto)
    next
      assume "n > 1" then show ?thesis
        text\<open>... and here happens the unfolding with the annotated (generated) invariant:\<close>
        unfolding is_prime'_annot 
        apply (fold dvd_eq_mod_eq_0  SQRT_UINT_MAX_def)
        using 1 by (wp, auto)
    qed
qed


section\<open>A Schematic Presentation for the Automated Proof \<close>
(* step 0 : "lifting over parameter" over the free variables of the correctness statement: *)
lemma whileLoopE_inv_lift1 : 
  "whileLoopE (B n) (C n) = (\<lambda>x. whileLoopE_inv (B n) (C n) x (I n) (measure' (M n)))"
  by (simp add: whileLoopE_inv_def)

(* step 1 : encapsulating inv and mesure for each loop *)
definition is_prime_requires : "is_prime_requires n \<equiv> \<lambda>\<sigma>. n \<le> UINT_MAX"
definition is_prime_ensures  : "is_prime_ensures n \<equiv> \<lambda>res \<sigma>. (res \<noteq> 0) \<longleftrightarrow> prime n"

definition is_prime_inv\<^sub>1     : "is_prime_inv\<^sub>1 n \<equiv> \<lambda>r s. is_prime_inv n r s"
definition is_prime_mesure\<^sub>1  : "is_prime_mesure\<^sub>1 n \<equiv> \<lambda>(r, s). (Suc n) * (Suc n) - r * r"

(* step 2 : specific replacement rule for the loop with the annotated loop *)
lemmas whileLoopE_invL1 = whileLoopE_inv_lift1 [of _ _ _ "is_prime_inv\<^sub>1" "is_prime_mesure\<^sub>1",
                                                simplified is_prime_inv\<^sub>1 is_prime_mesure\<^sub>1]

declare prime_ge_2_nat[dest] (* misère, preconfig pour le dernier auto. *)

(* configure the general methods "preparation" and annotate loops. *)
named_theorems prog_annotations
declare is_prime.is_prime'_def[prog_annotations]
        is_prime_requires [prog_annotations]
        is_prime_ensures [prog_annotations]


named_theorems folds
declare dvd_eq_mod_eq_0[symmetric,folds]
declare SQRT_UINT_MAX_def [symmetric,folds]

method prep declares prog_annotations folds = 
               (rule validNF_assume_pre, (* always!*)
                unfold prog_annotations folds)

method annotate_loops for n::nat = (prep, subst whileLoopE_invL1[of _ n])
                                   (* this must be generalized for several loops *)


(* and now the scheme for an automated proof, provided that sufficient
   background knowledge had been inserted into the prover 'auto'. *)

theorem is_prime_correct'':
  "\<lbrace>\<lambda>\<sigma>. n \<le> UINT_MAX \<rbrace> 
   is_prime.is_prime' n 
   \<lbrace>\<lambda>res \<sigma>. (res \<noteq> 0) \<longleftrightarrow> prime n \<rbrace>!"
   apply (annotate_loops n)    
   by    (wp, auto )  
  
(* or also: just another presentation *)
theorem (in is_prime) is_prime_correct''':
  "\<lbrace>is_prime_requires n\<rbrace> is_prime' n \<lbrace>is_prime_ensures n\<rbrace>!"
   apply (annotate_loops n)    
   by    (wp, auto )  


(* yet another way with Frédéric's stuff *)

method vcg = (subst is_prime.is_prime'_annot,prep, wp)

thm is_prime.is_prime'_annot

context is_prime 
begin

definition [prog_annotations]:"requires = is_prime_requires"
definition [prog_annotations]:"ensures  = is_prime_ensures"



theorem is_prime_correct'''': 
  "\<lbrace>requires n\<rbrace> is_prime' n \<lbrace>ensures n\<rbrace>!" 
  by(vcg, auto)  



end


end
