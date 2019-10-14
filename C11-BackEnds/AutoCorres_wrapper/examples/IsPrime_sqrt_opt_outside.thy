(******************************************************************************
 * Isabelle/C
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
(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

chapter\<open>A Sqrt Prime Sample Proof\<close>

text\<open>This example is used to demonstrate Isabelle/C/Autocorres in a version that keeps
annotations completely \<^emph>\<open>outside\<close> the C source. \<close>

theory IsPrime_sqrt_opt_outside
imports
  Isabelle_C_AutoCorres.Backend
  "HOL-Computational_Algebra.Primes"
begin

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
  by (metis dvd_add_triv_right_iff nat_dvd_1_iff_1 plus_1_eq_Suc)

lemma partial_prime_Suc [simp]:
  "partial_prime p (Suc n) = (partial_prime p n \<and> (1 < n \<and> Suc n < p \<longrightarrow> \<not> n dvd p))" 
proof(cases "p = Suc n")
  case True
  then show ?thesis 
       by(clarsimp simp: partial_prime_def min_def atLeastLessThanSuc not_le) 
next
  case False
  then show ?thesis
       by (clarsimp simp: partial_prime_def min_def atLeastLessThanSuc not_le, fastforce)
qed


lemma partial_prime_2 [simp]: "(partial_prime a 2) = (a > 1)"
  by (clarsimp simp: partial_prime_def)


lemma not_prime:
    "\<lbrakk> \<not> prime (a :: nat); a > 1 \<rbrakk> \<Longrightarrow> \<exists>x y. x * y = a \<and> 1 < x \<and> 1 < y \<and> x * x \<le> a" 
  apply (clarsimp simp: prime_nat_iff dvd_def, rename_tac "m" "k")
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


lemma partial_prime_sqr:
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

lemma prime_dvd:
    "\<lbrakk> prime (p::nat) \<rbrakk> \<Longrightarrow> (r dvd p) = (r = 1 \<or> r = p)"
  by (fastforce simp: prime_nat_iff)


lemma three_is_prime_nat: "prime (3::nat)"
  by (metis One_nat_def atLeastLessThan_iff dvd_triv_left even_Suc le_Suc_eq le_def 
            nat_mult_1_right not_less_eq numeral_2_eq_2 numeral_3_eq_3 prime_nat_numeral_eq set_upt)

lemma three_and_divides : "prime (p::nat) \<Longrightarrow> 3 < p \<Longrightarrow> \<not>(3 dvd p)"
  using primes_dvd_imp_eq three_is_prime_nat by blast





section\<open>The C code for \<open>O(sqrt(n))\<close> Primality Test Algorithm\<close>

text\<open> This C code contains a function that determines if the given number 
      @{term n} is prime.

      It returns 0 if @{term n}  is composite, or non-zero if @{term n}  is prime.
 
      This is a faster version than a linear primality test; runs in O(sqrt(n)). \<close>



C \<open>
//  Setup of AutoCorres for semantically representing this C element.
//@ install_autocorres is_prime [ ts_rules = nondet, unsigned_word_abs =  is_prime ]

#define SQRT_UINT_MAX 65536

unsigned int is_prime(unsigned int n)
{
    /* Numbers less than 2 are not primes. */
    if (n < 2) return 0;
    /* Numbers 2 and 3 are primes. */
    if (n < 4) return 1;
    /* Numbers larger or equal 4 devisable by 2 or 3 are not primes. */
    if (n % 2 == 0 || n % 3 == 0) return 0;
    /* Remaining numbers smaller 9 (so 5 and 7) primes. */
    if (n < 9) return 1;

    /* Find the first non-trivial factor of 'n' or sqrt(UINT_MAX), whichever comes first. */
    /* Find the first non-trivial factor of 'n' less than sqrt(n). */

    for (unsigned i = 3; i <= SQRT_UINT_MAX - 2 && i * i <= n; i+=2) {
        if (n % i == 0)
            return 0; 
    }

    /* No factors. */
    return 1;
}\<close>

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
     final correctness proof; in particular, the loop invariant is stated here.\<close>

definition is_prime_inv
  where [simp]: "is_prime_inv n i s \<equiv> (8 < i \<and> i \<le> n \<and> i \<le> SQRT_UINT_MAX \<and>
                                         i * i \<le> UINT_MAX + 1\<and>
                                       \<not> 2 dvd i \<and>  partial_prime n i)"

lemma uint_max_factor [simp]:  "UINT_MAX = SQRT_UINT_MAX * SQRT_UINT_MAX - 1"
  by (clarsimp simp: UINT_MAX_def SQRT_UINT_MAX_def)

lemma uint_max_factor_even [simp]: "(2::nat) dvd SQRT_UINT_MAX "
  by (clarsimp simp:  SQRT_UINT_MAX_def) 

lemma uint_max_factor_min1_dvd3 [simp]: "(3::nat) dvd (SQRT_UINT_MAX-1) "
  by (clarsimp simp:  SQRT_UINT_MAX_def) 

lemma uint_max_factor_min1_dvd4 [simp]: "(4::nat) dvd (SQRT_UINT_MAX) "
  by (clarsimp simp:  SQRT_UINT_MAX_def) 


lemma sqr_less_mono [simp]:
    "((i::nat) * i < j * j) = (i < j)" 
  by (meson le_def mult_le_mono mult_strict_mono' zero_le)

lemma sqr_le_mono [simp]:
    "((i::nat) * i \<le> j * j) = (i \<le> j)" 
  by (meson le_def mult_le_mono mult_strict_mono' zero_le)


lemma [simp]: "(a - b < a - c) = ((b::nat) > c \<and> c < a)"
  by arith

declare mult_le_mono [intro]

lemma sqr_le_sqr_minus_1 [simp]:
    "\<lbrakk> b \<noteq> 0 \<rbrakk> \<Longrightarrow> (a * a \<le> b * b - Suc 0) = (a < b)"
  by (metis gr0I sqr_less_mono nat_0_less_mult_iff nat_le_Suc_less)

lemma sqr_bla : 
  "Suc (Suc (Suc (Suc (r + (r + (r + (r + r * r))))))) = Suc(Suc r)*Suc(Suc r)"
  by simp

section\<open>The Correctness Proof \<close>

text\<open>Note that the proof \<^emph>\<open>injects\<close> the loop invariant at the point where the proof
     treats the loop.\<close>

(*
theorem (in is_prime) is_prime_faster_correct:
  notes times_nat.simps(2) [simp del] mult_Suc_right [simp del]
  shows "\<lbrace> \<lambda>s. n \<le> UINT_MAX \<rbrace> is_prime' n \<lbrace> \<lambda>r s. (r \<noteq> 0) \<longleftrightarrow> prime n \<rbrace>!"
  apply (rule validNF_assume_pre)
  apply (case_tac "n = 0")
   apply (clarsimp simp: is_prime'_def, wp, simp)[1]
  apply (case_tac "n = 1")
   apply (clarsimp simp: is_prime'_def, wp, simp)[1]
  apply (unfold is_prime'_def dvd_eq_mod_eq_0 [symmetric] SQRT_UINT_MAX_def [symmetric])
  apply (subst whileLoopE_add_inv [  where I = "\<lambda>r s. is_prime_inv n r s"
                                       and M = "(\<lambda>(r, s). (Suc n) * (Suc n) - r * r)"])
   apply wp
    apply clarsimp
    apply (metis One_nat_def Suc_leI Suc_lessD order_leE prime_dvd leD mult_le_mono n_less_n_mult_m)
   apply (fastforce elim: order_leE simp: partial_prime_sqr)   
  apply (clarsimp simp: SQRT_UINT_MAX_def)
  done
*)


theorem (in is_prime) is_prime_correct':
    "\<lbrace> \<lambda>\<sigma>. n \<le> UINT_MAX \<rbrace> is_prime' n \<lbrace> \<lambda>res \<sigma>. (res \<noteq> 0) \<longleftrightarrow> prime n \<rbrace>!"
proof (rule validNF_assume_pre)
  assume 1 : "n \<le> UINT_MAX"
  have   2 : "n=0 \<or> n=1 \<or> n=2 \<or> n=3 \<or> n=4 \<or> n=5 \<or> n=6 \<or> n=7 \<or> n=8 \<or> n > 8" by linarith
  show ?thesis
    proof (insert 2, elim disjE)
      assume  "n=0" 
      then show ?thesis  by (clarsimp simp:  is_prime'_def, wp, auto) 
    next
      assume  "n=1" 
      then show ?thesis  by (clarsimp simp:  is_prime'_def, wp, auto) 
    next
      assume  "n=2" 
      then show ?thesis  by (clarsimp simp:  is_prime'_def, wp, auto) 
    next
      assume  "n=3" 
      then show ?thesis  by (clarsimp simp:  is_prime'_def, wp, auto) 
    next
      assume  "n=4" 
      then show ?thesis  by (clarsimp simp:  is_prime'_def, wp, auto) 
    next
      assume  "n=5" 
      then show ?thesis  by (clarsimp simp:  is_prime'_def, wp, auto) 
    next
      assume  "n=6" 
      then show ?thesis  by (clarsimp simp:  is_prime'_def, wp, auto) 
    next
      assume  "n=7" 
      then show ?thesis  by (clarsimp simp:  is_prime'_def, wp, auto) 
    next
      assume  "n=8" 
      then show ?thesis  by (clarsimp simp:  is_prime'_def, wp, auto) 
    next
      assume *: "8 < n" 
      then show ?thesis
      proof (cases "2 dvd n")
        case True
        then show ?thesis  apply (clarsimp simp:  is_prime'_def, wp, auto simp: prime_odd_nat) 
          by (metis even_Suc even_zero less_antisym numeral_2_eq_2 numeral_eqs(3) two_is_prime_nat)
      next
        case False
        assume ** :"odd n"
        then show ?thesis 
        proof(cases "3 dvd n")
          case True
          then show ?thesis  by (clarsimp simp:  is_prime'_def, wp, insert *, auto simp: prime_odd_nat three_and_divides) 
        next
          case False
          then show ?thesis
           apply (unfold is_prime'_def dvd_eq_mod_eq_0 [symmetric] SQRT_UINT_MAX_def [symmetric], insert 1 * **)
           text\<open>... and here happens the annotation with the invariant:
                by instancing @{thm whileLoopE_add_inv}.
                One can say that the while loop is spiced up with the
                invariant and the measure by a rewrite step. \<close>
           apply (subst whileLoopE_add_inv [  where I = "\<lambda>r s. is_prime_inv n r s"
                                              and M = "(\<lambda>(r, s). (Suc n) * (Suc n) - r * r)"])
           apply wp
              apply(clarsimp, intro conjI) 
           apply (metis "*" Nat.diff_diff_eq bigger_prime diff_diff_cancel diff_self_eq_0 diff_zero dvd_1_left le_square nat_dvd_not_less nat_le_Suc_less not_numeral_le_zero numeral_1_eq_Suc_0 prime_gt_0_nat prime_nat_iff prime_nat_not_dvd prime_product zero_diff zero_less_numeral)
              apply(clarsimp, intro conjI) 
           apply (metis "**" All_less_Suc Suc_le_eq dvd_refl even_Suc le_less_Suc_eq less_Suc_eq less_zeroE linorder_neqE_nat nat_mult_dvd_cancel_disj sqr_less_mono)
           apply(simp add: SQRT_UINT_MAX_def)
                 apply(subst sqr_bla)
           apply(subst sqr_le_mono,simp add: SQRT_UINT_MAX_def) 
                apply auto[1]
               prefer 3 apply clarsimp
           apply(erule HOL.impCE')
           apply (simp add: partial_prime_sqr)

(*
              apply (wp,auto simp: prime_dvd partial_prime_sqr)
               apply (metis "**" Ex_less_Suc dvd_refl even_Suc le_Suc_eq le_antisym le_refl le_trans 
                                 nat_mult_dvd_cancel_disj not_less_eq_eq not_less_zero)
*)
(*
              apply (smt SQRT_UINT_MAX_def Suc_numeral add.commute diff_add_inverse diff_diff_left 
                         diff_is_0_eq eval_nat_numeral(3) even_numeral le_add_diff_inverse 
                         nat_le_Suc_less_imp not_le plus_1_eq_Suc semiring_norm(2) semiring_norm(8))
             prefer 2
             apply(drule Orderings.linorder_class.leI[THEN Orderings.order_class.le_imp_less_or_eq])
           apply(safe)
              apply (simp add: SQRT_UINT_MAX_def) 
           apply(subst (asm)  IsPrime_sqrt2_outside.partial_prime_sqr)
                     sledgehammer
   
           find_theorems "partial_prime"
           sledgehammer

              apply (metis Suc_lessD dvdI le_def less_trans_Suc n_less_m_mult_n nat_neq_iff)
           prefer 4     
           sledgehammer
                 apply (metis One_nat_def atLeastLessThan_iff le_neq_implies_less less_trans_Suc 
                              not_less_eq numeral_2_eq_2 numeral_eqs(3) prime_nat_iff')
           prefer 6 
                apply (simp add: prime_nat_iff')
           prefer 4 
           apply (simp add: le_def partial_prime_sqr) sledgehammer
           prefer 4 apply auto
*)
(*
           sledgehammer
               using not_less_eq_eq apply force
              apply (metis Suc_leI add_Suc mult_Suc mult_Suc_right mult_le_mono)
             apply (metis SQRT_UINT_MAX_def mult_Suc_right plus_nat.simps(2) rel_simps(76) 
                          sqr_le_sqr_minus_1 times_nat.simps(2))
           apply (simp_all add: SQRT_UINT_MAX_def)
           sorry
    qed
 *)

           sorry
         qed
qed
qed
qed

end
