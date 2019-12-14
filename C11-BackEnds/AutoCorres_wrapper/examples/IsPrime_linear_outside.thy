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

chapter \<open>Example: Linear Prime Sample Proof\<close>

text\<open>This example is used to demonstrate Isabelle/C/AutoCorres in a version that keeps
annotations completely \<^emph>\<open>outside\<close> the C source. \<close>

theory IsPrime_linear_outside
imports
  Isabelle_C_AutoCorres.AutoCorres_Wrapper
  "HOL-Computational_Algebra.Primes"
begin
\<comment> \<open>Derived from: \<^file>\<open>../../../src_ext/l4v/src/tools/autocorres/tests/examples/IsPrime.thy\<close>\<close>

section\<open>The Theory of the linear Primality Test Algorithm\<close>
text\<open>This section develops basic concepts of the invariant. This bit is presented here \<^emph>\<open>before\<close>
the actual code, but could also be after or even inside the \<^theory_text>\<open>C\<close> command as comment-annotation of 
the source.\<close>

definition  "partial_prime p (n :: nat) \<equiv> (1 < p \<and> (\<forall>i \<in> {2 ..< min p n}. \<not> i dvd p))"

lemma partial_prime_ge [simp]: "\<lbrakk> p' \<ge> p \<rbrakk> \<Longrightarrow> partial_prime p p' = prime p"
  by (clarsimp simp: partial_prime_def prime_nat_iff' min_def)

lemma divide_self_plus_one [simp]: "(x dvd Suc x) = (x = 1)" 
  by (metis dvd_add_triv_right_iff nat_dvd_1_iff_1 plus_1_eq_Suc)

lemma partial_prime_Suc [simp]:
  "partial_prime p (Suc n) = (partial_prime p n \<and> (1 < n \<and> Suc n < p \<longrightarrow> \<not> n dvd p))"
  apply (clarsimp simp: partial_prime_def min_def atLeastLessThanSuc not_le)
  by (metis atLeastLessThan_iff divide_self_plus_one dvd_add_triv_right_iff le_simps(2) 
            linorder_not_le order_le_less plus_1_eq_Suc prime_nat_iff' prime_nat_naiveI)

lemma mod_to_dvd:
   "(n mod i \<noteq> 0) = (\<not> i dvd (n :: nat))"
  by (clarsimp simp: dvd_eq_mod_eq_0)

lemma prime_of_product [simp]: "prime ((a::nat) * b) = ((a = 1 \<and> prime b) \<or> (prime a \<and> b = 1))"
  by (metis mult.commute mult.right_neutral prime_product)

lemma partial_prime_2 [simp]: "(partial_prime a 2) = (a > 1)"
  by (clarsimp simp: partial_prime_def)



definition [simp]: "is_prime_linear_inv n i s \<equiv> (1 < i \<and> 1 < n \<and> i \<le> n \<and> partial_prime n i)"


section\<open>The Gory C Code --- pure without annotations\<close>
text\<open>... except just one : the invocation of AutoCorres.\<close>

C \<open>
//  Setup of AutoCorres for semantically representing this C element.
//@ install_autocorres is_prime [ ts_rules = nondet, unsigned_word_abs = is_prime_linear  ]

#define SQRT_UINT_MAX 65536

unsigned is_prime_linear(unsigned n)
{
    /* Numbers less than 2 are not prime. */
    if (n < 2)
        return 0;

    /* Find the first non-trivial factor of 'n'. */
    for (unsigned i = 2; i < n; i++) {
        if (n % i == 0)
            return 0;
    }

    /* No factors. */
    return 1;
}
\<close>

find_theorems name:"is_prime_linear"
thm IsPrime_linear_outside.is_prime_global_addresses.is_prime_linear_body_def
thm is_prime.is_prime_linear'_def

C_export_file  (* This exports the C code into a C file ready to be compiled by gcc. *)

lemma uint_max_factor [simp]: "UINT_MAX = SQRT_UINT_MAX * SQRT_UINT_MAX - 1"
  by (clarsimp simp: UINT_MAX_def SQRT_UINT_MAX_def)


section\<open>The Correctness Proof of \<^const>\<open>is_prime.is_prime_linear'\<close>\<close>
text\<open>Note that the proof \<^emph>\<open>injects\<close> the loop invariant at the point where the proof
     treats the loop.\<close>


lemma
"whileLoopE (B n) (C n) = 
 (\<lambda>x. whileLoopE_inv (B n) (C n) x (is_prime_linear_inv n) (measure' (\<lambda>(r, _). n - r))) "
  unfolding whileLoopE_inv_def
  by simp


(* imperative "red" style proof *)
theorem (in is_prime) is_prime_correct:
    "\<lbrace> \<lambda>s. n \<le> UINT_MAX \<rbrace> is_prime_linear' n \<lbrace> \<lambda>r s. (r \<noteq> 0) \<longleftrightarrow> prime n \<rbrace>!"
  apply (rule validNF_assume_pre)
  apply (case_tac "n = 0")
   apply (clarsimp simp: is_prime_linear'_def, wp, simp)[1]
  apply (case_tac "n = 1")
   apply (clarsimp simp: is_prime_linear'_def, wp, simp)[1]
  apply (unfold is_prime_linear'_def)
  text\<open>... and here happens the annotation with the invariant:
       by instancing @{thm whileLoopE_add_inv}.
       One can say that the while loop is spiced up with the
       invariant and the measure by a rewrite step. \<close>
  apply (subst whileLoopE_add_inv [ where I = "is_prime_linear_inv n"
                                      and M = "\<lambda>(r, _). n - r"])
  apply (wp, auto)
  done



(* declarative "blue" style proof *)

theorem (in is_prime) is_prime_correct':
    "\<lbrace> \<lambda>\<sigma>. n \<le> UINT_MAX \<rbrace> is_prime_linear' n \<lbrace> \<lambda>res \<sigma>. (res \<noteq> 0) \<longleftrightarrow> prime n \<rbrace>!"
proof (rule validNF_assume_pre)
  assume 1 : "n \<le> UINT_MAX"
  have   2 : "n=0 \<or> n=1 \<or> n > 1" by linarith
  show ?thesis
  proof (insert 2, elim disjE)
    assume  "n=0" 
    then show ?thesis  by (clarsimp simp:  is_prime_linear'_def, wp, auto) 
  next
    assume  "n=1" 
    then show ?thesis  by (clarsimp simp:  is_prime_linear'_def, wp, auto) 
  next
    assume  "1 < n" 
    then show ?thesis
           apply (unfold is_prime_linear'_def, insert 1)
           text\<open>... and here happens the annotation with the invariant:
                by instancing @{thm whileLoopE_add_inv}.
                One can say that the while loop is spiced up with the
                invariant and the measure by a rewrite step. \<close>
           apply (subst whileLoopE_add_inv [ where I = "is_prime_linear_inv n"
                                               and M = "\<lambda>(r, _). n - r"])
           by (wp, auto)
  qed
qed

end
