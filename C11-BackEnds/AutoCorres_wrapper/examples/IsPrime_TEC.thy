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
(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

chapter \<open>Example: Integrated Prime Sample Proof\<close>

text \<open> This example is used to demonstrate Isabelle/C/AutoCorres in a version that keeps
the theory development of the background theory as well as annotations completely \<^emph>\<open>inside\<close> the 
C source. This development style we call TEC (\<^emph>\<open>Theory embedded-in Code\<close>) is also 
supported by Isabelle/C. TEC - style development makes
the overall command execution slower, since the execution not only includes parsing, but also 
AutoCorres' default generation of intermediate theorems and proofs. However, this has useful 
applications, when for example directly attaching some properties next to where a particular 
cpp macro is actually defined. Methodologically, it is relevant to express semantic dependencies 
locally in order to ensure fast feedback as a consequence of changes of the source. 

In TEC style, Programs become a kind of ``proof-carrying (high-level) code''.
Exports of the C-sources will contain their theory (not only their annotations) as comments
\<^emph>\<open>inside\<close> which might be also useful in certification as well as advanced  
``proof-carrying code'' load-and-check schemes for server platforms. 

Note that the opposite style  we call TEC (\<^emph>\<open>Theory embedded-in Code\<close>) is also 
supported by Isabelle/C. It is characteristic for this style that developers of development and 
verification  teams can be separated, as is required by many certification standards.
\<close>

theory IsPrime_TEC
imports
  Isabelle_C_AutoCorres.AutoCorres_Wrapper
  "HOL-Computational_Algebra.Primes"
begin
\<comment> \<open>Derived from: \<^file>\<open>../../../src_ext/l4v/src/tools/autocorres/tests/examples/IsPrime.thy\<close>\<close>

declare [[AutoCorres]]

C \<open>
   //  Setup of AutoCorres for semantically representing this C element.
   //@ install_autocorres is_prime [ ts_rules = nondet, unsigned_word_abs = is_prime_linear is_prime ]
   
   #define SQRT_UINT_MAX 65536
   /* We prove locally some facts on this C preprocessor macro, which is internally
      converted into an Isabelle/HOL definition: */
   /*@
   lemma uint_max_factor [simp]:
     "UINT_MAX = SQRT_UINT_MAX * SQRT_UINT_MAX - 1"
     by (clarsimp simp: UINT_MAX_def SQRT_UINT_MAX_def)
    */
   
   
   /* in the sequel, we give the definitions and theory relevant for the statement of the invariant */
   
   /*@
   definition   "partial_prime p (n :: nat) \<equiv>  (1 < p \<and> (\<forall>i \<in> {2 ..< min p n}. \<not> i dvd p))"
   
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
   
   lemma mod_to_dvd:
      "(n mod i \<noteq> 0) = (\<not> i dvd (n :: nat))"
     by (clarsimp simp: dvd_eq_mod_eq_0)
   
   lemma prime_of_product [simp]: "prime ((a::nat) * b) = ((a = 1 \<and> prime b) \<or> (prime a \<and> b = 1))"
     by (metis mult.commute mult.right_neutral prime_product)
   
   lemma partial_prime_2 [simp]: "(partial_prime a 2) = (a > 1)"
     by (clarsimp simp: partial_prime_def)
   
   definition [simp]:
     "is_prime_linear_inv n i s \<equiv> (1 < i \<and> 1 < n \<and> i \<le> n \<and> partial_prime n i)"
   
    */
   /*
    * Determine if the given number 'n' is prime.
    *
    * We return 0 if 'n' is composite, or non-zero if 'n' is prime.
    */
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
   }/*@
   
   theorem (in is_prime) is_prime_correct:
       "\<lbrace> \<lambda>s. n \<le> UINT_MAX \<rbrace> is_prime_linear' n \<lbrace> \<lambda>r s. (r \<noteq> 0) \<longleftrightarrow> prime n \<rbrace>!"
     apply (rule validNF_assume_pre)
     apply (case_tac "n = 0")
      apply (clarsimp simp: is_prime_linear'_def, wp, simp)[1]
     apply (case_tac "n = 1")
      apply (clarsimp simp: is_prime_linear'_def, wp, simp)[1]
     apply (unfold is_prime_linear'_def)
     apply (subst whileLoopE_add_inv [
         where I="\<lambda>r s. is_prime_linear_inv n r s"
                     and M="(\<lambda>(r, s). n - r)"])
     apply (wp, auto simp: mod_to_dvd [simplified])
     done
   
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
   
   definition is_prime_inv
     where [simp]: "is_prime_inv n i s \<equiv> (1 < i \<and> i \<le> n \<and> i \<le> SQRT_UINT_MAX \<and> i * i \<le> SQRT_UINT_MAX * SQRT_UINT_MAX \<and> partial_prime n i)"
   
   lemma nat_leE: "\<lbrakk> (a::nat) \<le> b; a < b \<Longrightarrow> R; a = b \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
     apply atomize_elim
       apply clarsimp
     done
   
   lemma sqr_less_mono [simp]:
       "((i::nat) * i < j * j) = (i < j)"
     by (metis (full_types) le0 less_not_refl3 linorder_neqE_nat
           mult_strict_mono' order.strict_trans)
   
   lemma [simp]: "(a - b < a - c) = ((b::nat) > c \<and> c < a)"
     by arith
   
   declare mult_le_mono [intro]
   
   lemma sqr_le_sqr_minus_1 [simp]:
       "\<lbrakk> b \<noteq> 0 \<rbrakk> \<Longrightarrow> (a * a \<le> b * b - Suc 0) = (a < b)"
     by (metis gr0I sqr_less_mono nat_0_less_mult_iff nat_le_Suc_less)
   
    */
   /*
    * Determine if the given number 'n' is prime.
    *
    * We return 0 if 'n' is composite, or non-zero if 'n' is prime.
    *
    * Faster version that 'is_prime'; runs in O(sqrt(n)).
    */
   unsigned int is_prime(unsigned int n)
   {
       /* Numbers less than 2 are not primes. */
       if (n < 2)
           return 0;
   
       /* Find the first non-trivial factor of 'n' or sqrt(UINT_MAX), whichever
        * comes first. */
       /* Find the first non-trivial factor of 'n' less than sqrt(n). */
       for (unsigned i = 2; i < SQRT_UINT_MAX && i * i <= n; i++) {
           if (n % i == 0)
               return 0;
       }
   
       /* No factors. */
       return 1;
   }
   /*@
   
   theorem (in is_prime) is_prime_faster_correct:
     notes times_nat.simps(2) [simp del] mult_Suc_right [simp del]
     shows "\<lbrace> \<lambda>s. n \<le> UINT_MAX \<rbrace> is_prime' n \<lbrace> \<lambda>r s. (r \<noteq> 0) \<longleftrightarrow> prime n \<rbrace>!"
     apply (rule validNF_assume_pre)
     apply (case_tac "n = 0")
      apply (clarsimp simp: is_prime'_def, wp, simp)[1]
     apply (case_tac "n = 1")
      apply (clarsimp simp: is_prime'_def, wp, simp)[1]
     apply (unfold is_prime'_def dvd_eq_mod_eq_0 [symmetric] SQRT_UINT_MAX_def [symmetric])
     apply (subst whileLoopE_add_inv [
         where I="\<lambda>r s. is_prime_inv n r s"
         and M="(\<lambda>(r, s). (Suc n) * (Suc n) - r * r)"])
      apply wp
       apply clarsimp
       apply (metis One_nat_def Suc_leI Suc_lessD nat_leE prime_dvd leD mult_le_mono n_less_n_mult_m)
      apply (fastforce elim: nat_leE simp: partial_prime_sqr)
     apply (clarsimp simp: SQRT_UINT_MAX_def)
     done
   
   */
\<close>

C_export_file  (* This exports the C code into a C file ready to be compiled by gcc. *)

(* checking the effect of the C-command above: *)
find_theorems name:is_prime

text\<open> The global effect on the logical context is to define 
\<^enum> the invariant @{thm is_prime_linear_inv_def}
\<^enum> the high-level semantic presentation of the @{term "is_prime.is_prime'"}-function:
  @{thm is_prime.is_prime_linear'_def}
\<^enum> the high-level semantic presentation of the proof-obligation for the correctness statement:
  @{thm "is_prime.is_prime_faster_correct"}

\<close>


end
