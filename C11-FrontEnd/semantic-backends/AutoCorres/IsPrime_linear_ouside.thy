(*
 * Copyright 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

chapter\<open>Linear Prime Sample Proof\<close>

text\<open>This example is used to demonstrate Isabelle/C/Autocorres in a version that keeps
annotations completely \<^emph>\<open>outside\<close> the C source. \<close>

theory IsPrime_linear_ouside
imports
  "AutoCorres.AutoCorres"
  "HOL-Computational_Algebra.Primes"
begin


section\<open>The Theory of the linear Primality Test Algorithm\<close>
text\<open>This theory part develops the concepts of the invariant. This bit presented before
the actual code, but could also be after or even inside (* as annotation *) of the source.\<close>

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



definition [simp]:
  "is_prime_linear_inv n i s \<equiv> (1 < i \<and> 1 < n \<and> i \<le> n \<and> partial_prime n i)"


section\<open>The Gory C Code --- pure without annutations\<close>
text\<open>... except just one : the invocation of autocorres.\<close>

C \<open>

/*
 * Copyright 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

//  Setup of autocorres for parsing and semantically representing this C element.
//@ install_autocorres is_prime [ ts_rules = nondet, unsigned_word_abs = is_prime_linear  ]


#define SQRT_UINT_MAX 65536

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
}
\<close>


text\<open>Autocorres produced internally the following definitions of this input:\<close>
find_theorems name:is_prime

text\<open>Of key importance:\<close>
thm is_prime_global_addresses.is_prime_linear_body_def
thm is_prime.is_prime_linear'_def 


section\<open>The Correctness-Proof of @{const "is_prime.is_prime_linear'"}\<close>

definition "SQRT_UINT_MAX \<equiv> 65536 :: nat"   (* a generer automatiquement *) 

lemma uint_max_factor [simp]: "UINT_MAX = SQRT_UINT_MAX * SQRT_UINT_MAX - 1"
  by (clarsimp simp: UINT_MAX_def SQRT_UINT_MAX_def)






(* imperative "red" style proof *)
theorem (in is_prime) is_prime_correct:
    "\<lbrace> \<lambda>s. n \<le> UINT_MAX \<rbrace> is_prime_linear' n \<lbrace> \<lambda>r s. (r \<noteq> 0) \<longleftrightarrow> prime n \<rbrace>!"
  apply (rule validNF_assume_pre)
  apply (case_tac "n = 0")
   apply (clarsimp simp: is_prime_linear'_def, wp, simp)[1]
  apply (case_tac "n = 1")
   apply (clarsimp simp: is_prime_linear'_def, wp, simp)[1]
  apply (unfold is_prime_linear'_def)
  apply (subst whileLoopE_add_inv [  where I="\<lambda>r s. is_prime_linear_inv n r s"
                                       and M="(\<lambda>(r, s). n - r)"])
  apply (wp, auto simp: mod_to_dvd [simplified])
  done



(* declarative "blue" style proof *)
theorem (in is_prime) is_prime_correct':
    "\<lbrace> \<lambda>s. n \<le> UINT_MAX \<rbrace> is_prime_linear' n \<lbrace> \<lambda>r s. (r \<noteq> 0) \<longleftrightarrow> prime n \<rbrace>!"
proof (rule validNF_assume_pre, cases "n = 0")
  case True
  then show ?thesis by (clarsimp simp: is_prime_linear'_def, wp, simp)[1] 
next
  case False
  then show ?thesis 
       proof(cases "n = 1")
         case True
         then show ?thesis by (clarsimp simp: is_prime_linear'_def, wp, simp)[1] 
       next
         case False
         then show ?thesis
           apply (unfold is_prime_linear'_def)
           apply (rule validNF_assume_pre)
           apply (subst whileLoopE_add_inv [ where I="\<lambda>r s. is_prime_linear_inv n r s"
                                               and M="(\<lambda>(r, s). n - r)"])
           apply (wp, auto simp: mod_to_dvd [simplified])
           using less_2_cases prime_gt_0_nat by blast
       qed
qed
 

end
