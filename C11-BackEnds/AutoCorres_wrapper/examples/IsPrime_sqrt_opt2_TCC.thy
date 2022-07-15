(******************************************************************************
 * Isabelle/C/AutoCorres
 *
 * Copyright (c) 2018-2022 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * Author: Burkhart Wolff
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
(* For the original C-example:
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

chapter \<open>Example: An even more optimized 0(sqrt(n)) Prime-Number Checking Algorithm and its Verification\<close>

text\<open>This example is used to demonstrate Isabelle/C/AutoCorres in a version that keeps
the theory development of the background theory completely \<^emph>\<open>separate\<close> from the C source. 
The example is chosen to demonstrate the impact of low-level optimisations on verification.\<close>

theory IsPrime_sqrt_opt2_TCC
imports
  Isabelle_C_AutoCorres.AutoCorres_Wrapper
  "HOL-Computational_Algebra.Primes"
begin

section\<open>The C code for \<open>O(sqrt(n))\<close> Primality Test Algorithm based on a 6-Sieve\<close>

text \<open>The invocation of AutoCorres and the Setup of AutoCorres 
      for representing the following C text-element semantically:\<close> 
declare [[AutoCorres]]
declare_autocorres is_prime [ts_rules = nondet,unsigned_word_abs = is_prime]

text\<open> 
  This C code contains a function that determines if the given number @{term n} is prime.
  It returns 0 if @{term n}  is composite, or non-zero if @{term n}  is prime.
  This is a faster version than a linear primality test; runs in O(sqrt(n)). 
  The algorithm avoids divisability tests for 2 and 3 (thus implicitely applying a 
  Erasthostenes sieve of size 6.

  Hypothesis: This algorithm, if applied in its domain till \<open>UINT_MAX\<close> and compiled 
  efficiently in C, runs faster than OCaml implementations using a full sieve. \<close>




C \<open>
#define SQRT_UINT_MAX 65536
#define TRUE  1
#define FALSE 0

unsigned int is_prime(unsigned int n)
   {
       if (n < 2) return FALSE;
       if (n < 4) return TRUE;
       if (n % 2 == 0 || n % 3 == 0) return FALSE;
   
       for (unsigned i = 5; i < SQRT_UINT_MAX - 5 && i * i <= n; i+=6) {
           if (n % i == 0 || n % (i+2) == 0)
               return FALSE; 
       }
   
       return TRUE;
   }\<close>

C_export_file  (* This exports the C code into a C file ready to be compiled by gcc. *)




section\<open>The Verification\<close>

subsection\<open>Background\<close>

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
     " n * n > p  \<Longrightarrow> partial_prime p n = prime p" 
proof (cases "n \<ge> p")
  case True
  then show "p < n * n \<Longrightarrow> p \<le> n \<Longrightarrow> partial_prime p n = prime p" by clarsimp
next
  case False
  assume 1 : "p < n * n" and 2 : "\<not> p \<le> n"
  show "partial_prime p n = prime p"
  proof(cases "partial_prime p n")
    case True
    then show ?thesis apply(clarsimp, insert 1)   apply (erule sqrt_prime)
    apply (clarsimp simp: partial_prime_def)
     apply (metis False One_nat_def Suc_1 atLeastLessThan_iff dvd_1_left dvd_pos_nat le_def 
                    less_Suc_eq min.commute min.strict_order_iff not_less_eq)
      by(metis  One_nat_def   True  partial_prime_def)
  next
    case False
    then show ?thesis apply(clarsimp) 
      using partial_prime_def prime_nat_iff' by auto
  qed
qed

lemma prime_dvd:
    "\<lbrakk> prime (p::nat) \<rbrakk> \<Longrightarrow> (r dvd p) = (r = 1 \<or> r = p)"
  by (fastforce simp: prime_nat_iff)


lemma three_is_prime_nat: "prime (3::nat)"
  by (metis One_nat_def atLeastLessThan_iff dvd_triv_left even_Suc le_Suc_eq le_def 
            nat_mult_1_right not_less_eq numeral_2_eq_2 numeral_3_eq_3 prime_nat_numeral_eq set_upt)


lemma partial_prime_Suc':"\<not> r dvd n \<Longrightarrow> partial_prime n r = partial_prime n (Suc r)" 
  using partial_prime_Suc by blast

lemma partial_prime_Suc'' : 
  "k dvd r \<Longrightarrow> partial_prime n r \<Longrightarrow> 1 < k \<Longrightarrow> k < r \<Longrightarrow> partial_prime n (Suc r)"
  apply( subst partial_prime_Suc'[symmetric], simp_all add: partial_prime_def)
  by (metis One_nat_def Suc_1 Suc_le_eq atLeastLessThan_iff gcd_nat.trans gr0_conv_Suc
            min.absorb4 min_less_iff_conj nat_dvd_not_less nat_neq_iff)

lemma five_is_prime_nat: "prime (5::nat)"
  apply(rule_tac  t= "5" and s="Suc(Suc(Suc(Suc(Suc 0))))" in subst,simp)
  apply(auto simp: Primes.prime_nat_iff')
  by (smt Suc_lessI diff_Suc_Suc diff_zero dvd_minus_self linorder_not_le nat_dvd_not_less 
          not_less_eq_eq numeral_2_eq_2)

lemma three_and_divides : "prime (p::nat) \<Longrightarrow> 3 < p \<Longrightarrow> \<not>(3 dvd p)"
  using primes_dvd_imp_eq three_is_prime_nat by blast


lemma five_and_divides : "prime (p::nat) \<Longrightarrow> 5 < p \<Longrightarrow> \<not>(5 dvd p)"
  using primes_dvd_imp_eq three_is_prime_nat 
  by (simp add: prime_nat_not_dvd)


subsection\<open>The Results of the AutoCorres Evaluation\<close>

text\<open>AutoCorres produced internally the following definitions of this input:\<close>
find_theorems name:is_prime

text\<open>The following definitions are key importance: they represent the C program
     as a HOL function over a state modeling modeled by AutoCorres for the given 
     C program.\<close>
thm is_prime_global_addresses.is_prime_body_def
thm is_prime.is_prime'_def   
thm SQRT_UINT_MAX_def

text\<open>Note that the pre-processor macro has been converted into a definition in HOL.
     It induces the following semantic (!) properties:\<close>
  
lemma uint_max_factor [simp]:  "UINT_MAX = SQRT_UINT_MAX * SQRT_UINT_MAX - 1"
  by (clarsimp simp: UINT_MAX_def SQRT_UINT_MAX_def)

lemma uint_max_factor_even [simp]: "(2::nat) dvd SQRT_UINT_MAX "
  by (clarsimp simp:  SQRT_UINT_MAX_def) 

lemma uint_max_factor_min1_dvd3 [simp]: "(3::nat) dvd (SQRT_UINT_MAX-1) "
  by (clarsimp simp:  SQRT_UINT_MAX_def) 

lemma uint_max_factor_min1_dvd4 [simp]: "(4::nat) dvd (SQRT_UINT_MAX) "
  by (clarsimp simp:  SQRT_UINT_MAX_def) 



subsection\<open>The Specification, the Invariant and Some Corrollaries\<close>

text\<open>This section contains the auxilliary definitions and lemmas for the
     final correctness proof; in particular, the loop invariant is stated here.\<close>

definition is_prime_inv
  where [simp]: "is_prime_inv n i s \<equiv> (5 \<le> i \<and> i \<le> SQRT_UINT_MAX - 1 \<and> i \<le> n \<and> 
                                       (i mod 6) = 5 \<and> partial_prime n i)"

lemma inv_preserved0: "is_prime_inv n i s 
                       \<Longrightarrow> \<not> i dvd n \<Longrightarrow>  \<not> (i+2) dvd n 
                       \<Longrightarrow> odd n \<Longrightarrow> \<not> (3 dvd n) \<Longrightarrow> 4 < n 
                       \<Longrightarrow> partial_prime n (i + 6)"
  unfolding  is_prime_inv_def partial_prime_def
proof(elim conjE)
  fix i :: nat
  assume 1: "odd n"         and    2: "\<not> (3 dvd n)"
  and    6: "5 \<le> i"         and    7: "\<forall>i\<in>{2..<min n i}. \<not> i dvd n"
  and    8 :"\<not> i dvd n"     and    9 :"\<not> (i + 2) dvd n"
  and   10 :  "i mod 6 = 5" and   11: "4 < n"
  and   12: "i \<le> n"
  have  * : "\<exists> m::nat. i= m*6+5"
             by (metis "6" "10" add.commute mod_mod_trivial mult.commute nat_mod_eq_lemma)
  have  ** : "odd i"  
             using "10" by presburger
  have  ***: "\<not>(3 dvd i)"
    apply(simp add: Rings.semidom_modulo_class.dvd_eq_mod_eq_0)
    apply(insert *, erule_tac exE, rename_tac m)
    by (metis "10" One_nat_def add_Suc_shift gr0I le_add1 le_add_same_cancel1 mod_double_modulus 
              mult_2  numeral_3_eq_3 numeral_Bit0 numeral_eq_iff plus_1_eq_Suc semiring_norm(83) 
              semiring_norm(90) zero_less_numeral )
  have  ****: "\<forall>i\<in>{2..<i}. \<not> i dvd n"
    by (simp add: "12" "7")
  show "1 < n \<and> (\<forall>i\<in>{2..<min n (i + 6)}. \<not> i dvd n)"
     proof(cases "n=5", simp_all)
       case True
       then show "\<forall>i\<in>{2..<5}. \<not> i dvd 5" 
         by (metis **** "6" "8" atLeastLessThan_iff dvd_refl five_is_prime_nat 
                   le_neq_implies_less prime_ge_2_nat)
     next
       case False
       assume ** : "n \<noteq> 5"
       show "Suc 0 < n \<and> (\<forall>i\<in>{2..<min n (i + 6)}. \<not> i dvd n)"
         apply auto
         using "11" apply linarith
       proof (erule contrapos_pp)
         fix j :: nat
         assume "2 \<le> j" and "j < n" and "j < i + 6" show "\<not> j dvd n"
         proof(cases "j < i")
           case True
           then show ?thesis  
             by (simp add: **** \<open>2 \<le> j\<close>)
         next
           case False
             have *:"j = i+5 \<or> j = i+4 \<or> j = i+3 \<or> j = i+2 \<or> j = i+1 \<or> j = i " 
               using False \<open>j < i + 6\<close> by linarith
     
           then show ?thesis
           proof(insert *,elim disjE, simp_all)
             show "\<not> i + 5 dvd n" 
                using "1" \<open>\<exists> m::nat. i= m*6+5\<close> by auto
           next 
             show "\<not> i + 4 dvd n" 
               by (smt \<open>\<exists> m::nat. i= m*6+5\<close> "2" Suc_numeral add.assoc add_Suc_right  
                       dvd_add_times_triv_left_iff dvd_add_triv_right_iff dvd_refl dvd_trans 
                       numeral_3_eq_3 numeral_Bit0 numeral_eqs(3) plus_1_eq_Suc semiring_norm(5))
           next 
             show "\<not> i + 3 dvd n"       using "1" \<open>\<exists> m::nat. i= m*6+5\<close> by auto
           next 
             show "\<not> Suc (Suc i) dvd n" using "9" by auto
           next
             show "\<not> Suc i dvd n"       using 1 \<open>\<exists> m::nat. i= m*6+5\<close> by auto
           next 
             show "\<not> i dvd n"           by (simp add: "8")
           qed
         qed
       qed
     qed
qed


text\<open>A few non-linear properites on inequalities come in handy:\<close>
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


subsection\<open>The Correctness Proof \<close>

text\<open>Note that the proof \<^emph>\<open>injects\<close> the loop invariant at the point where the proof treats the loop.\<close>

theorem (in is_prime) is_prime_correct':
    "\<lbrace> \<lambda>\<sigma>. n \<le> UINT_MAX \<rbrace> is_prime' n \<lbrace> \<lambda>res \<sigma>. (res \<noteq> 0) \<longleftrightarrow> prime n \<rbrace>!"
proof (rule validNF_assume_pre)
  assume 1 : "n \<le> UINT_MAX"
  have   2 : "n=0 \<or> n=1 \<or> n=2 \<or> n=3 \<or> n=4 \<or> n > 4" by linarith
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
      assume *: "4 < n" 
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
          then show ?thesis  by (clarsimp simp:  is_prime'_def, wp, insert *, 
                                 auto simp: prime_odd_nat three_and_divides) 
        next
          case False
          assume *** :"\<not> 3 dvd n"
          then show ?thesis
            apply (unfold is_prime'_def dvd_eq_mod_eq_0 [symmetric] SQRT_UINT_MAX_def [symmetric], 
                   insert 1 * **)
            text\<open>... we annotate the loop with the invariant
                 by instancing @{thm whileLoopE_add_inv}. \<close>
            apply (subst whileLoopE_add_inv 
                         [  where I = "\<lambda>r s. is_prime_inv n r s"
                            and   M = "\<lambda>(r, s). (Suc n) * (Suc n) - r * r"])
            text\<open>... applying vcg and splitting the result: \<close>
            proof(wp, clarsimp)
              text\<open>@{term is_prime_inv} holds for loop exits via @{term "return"}.\<close>
              show "\<lbrace>\<lambda>s. is_prime_inv n 5 s\<rbrace> return (even n \<or> 3 dvd n) 
                    \<lbrace>\<lambda>ret s.  if ret then (0 \<noteq> 0) = prime n 
                                     else is_prime_inv n 5 s\<rbrace>!"
                by(wp, auto simp: ** ***) 
            next
              text\<open>@{term is_prime_inv} initially holds when entering the loop.\<close>
              fix s::lifted_globals 
              have **** : "\<not> n < 4 \<Longrightarrow> partial_prime n 5"
                by (metis "*" "**" False One_nat_def eq_numeral_Suc even_numeral  less_trans_Suc 
                          numeral_eqs(4) numerals(2) partial_prime_2 partial_prime_Suc' lessI
                          partial_prime_Suc'' pred_numeral_simps(3) zero_less_numeral) 
              show "if n < 2 then (0 \<noteq> 0) = prime n
                             else if n < 4 then (1 \<noteq> 0) = prime n
                                  else is_prime_inv n 5 s"
                apply(auto simp: * ****) 
                using not_le prime_ge_2_nat apply auto[1]
                using "*" less_or_eq_imp_le not_le apply blast
                using "*" apply linarith
                  apply (simp add: SQRT_UINT_MAX_def) 
                using "*" by linarith                
            next
              text\<open>@{term is_prime_inv} preserved.\<close>
              fix r::nat
              assume "5 \<le> r"  and "r \<le> SQRT_UINT_MAX - Suc 0"
                     "r \<le> n"  and "r mod 6 = 5" and "partial_prime n r" and 
                     "r < 65531" and "r * r \<le> n"
              show "(r dvd n \<longrightarrow> \<not> prime n) \<and>
                     (Suc (Suc r) dvd n \<longrightarrow> \<not> prime n) \<and>
                     (\<not> r dvd n \<and> \<not> Suc (Suc r) dvd n \<longrightarrow>
                      r + 6 \<le> SQRT_UINT_MAX - Suc 0 \<and>
                      r + 6 \<le> n \<and> partial_prime n (r + 6) \<and> (r < 65525 \<longrightarrow> r + 6 < SQRT_UINT_MAX))"
              proof(intro conjI impI)
                show "r dvd n \<Longrightarrow> \<not> prime n" 
                  using \<open>5 \<le> r\<close> \<open>r * r \<le> n\<close> prime_dvd by auto
              next
                show "Suc (Suc r) dvd n \<Longrightarrow> \<not> prime n" 
                  by (smt One_nat_def Suc_leD \<open>5 \<le> r\<close> \<open>r * r \<le> n\<close> dvd_triv_left even_Suc 
                          even_mult_iff le_SucE le_antisym le_square less_numeral_extra(3) 
                          mult_eq_self_implies_10 nat.inject numeral_eqs(4) prime_dvd zero_less_Suc)
              next 
                show " r < 65525 \<Longrightarrow> r + 6 < SQRT_UINT_MAX " by(simp add:  SQRT_UINT_MAX_def)
              next
                assume "\<not> r dvd n \<and> \<not> Suc (Suc r) dvd n"
                show "partial_prime n (r + 6)"
                 apply(rule inv_preserved0)
                       apply (simp add: \<open>5 \<le> r\<close>  \<open>r \<le> n\<close> \<open>r mod 6 = 5\<close> 
                                        \<open>partial_prime n r\<close> \<open>r \<le> SQRT_UINT_MAX - Suc 0\<close>)
                  apply (simp add: \<open>\<not> r dvd n \<and> \<not> Suc (Suc r) dvd n\<close>)
                  apply (simp add: \<open>\<not> r dvd n \<and> \<not> Suc (Suc r) dvd n\<close>)
                  apply (simp add: "**")
                  apply (simp add: False)
                  by (simp add: "*")
              next
                 assume "\<not> r dvd n \<and> \<not> Suc (Suc r) dvd n"
                 show "r + 6 \<le> SQRT_UINT_MAX - Suc 0"
                   apply(simp add: SQRT_UINT_MAX_def)
                   apply(insert \<open>r < 65531\<close> \<open>r mod 6 = 5\<close>)
                   apply(cases "r=65530", simp)
                   by(linarith)
              next
                 show "r + 6 \<le> n"
                   apply(insert \<open>r * r \<le> n\<close> \<open>5 \<le> r\<close>)
                   apply(auto simp: le_iff_add)
                   apply(rule_tac x = "14 + ca * ca + 9 * ca + c" in exI,simp)
                   by(simp add:ring_distribs(1) ring_distribs(2))
              qed
            next
              text\<open>@{term is_prime_inv} implies postcond when leaving the loop.\<close>
              fix r::nat fix s::lifted_globals
              assume * :"\<not> (r < 65531 \<and> r * r \<le> n)"
                have  ** : "r\<ge>65531 \<or> r * r>n"  using "*" leI by blast
              assume  ***: "is_prime_inv n r s"
              show "((1::nat) \<noteq> 0) = prime n"
                apply simp
                apply(case_tac "r\<ge>65531") defer 1
                using "*" "***" apply auto[1]                
                using "**" partial_prime_sqr apply blast
                apply(insert ***) 
                proof - 
                  have ** : "(19::nat) dvd 65531" by simp
                  have *** : "even 65532" by simp
                  have **** : "(13::nat) dvd 65533" by simp
                  have ***** : "even 65534" by simp
                  have  ****** : "(5::nat) dvd 65535" by simp
                  show " 65531 \<le> r \<Longrightarrow> is_prime_inv n r s \<Longrightarrow> prime n"
                   apply(insert *, simp add:  SQRT_UINT_MAX_def, elim conjE)
                   apply(subst partial_prime_sqr[where p = "n" and n = "SQRT_UINT_MAX",symmetric])
                   using "1" uint_max_factor apply linarith
                   apply(cases "r = 65531", simp_all)
                    apply(drule partial_prime_Suc''[OF **], simp_all)
                    apply(drule partial_prime_Suc''[OF ***], simp_all)
                    apply(drule partial_prime_Suc''[OF ****], simp_all)
                    apply(drule partial_prime_Suc''[OF *****], simp_all)
                    apply(drule partial_prime_Suc''[OF ******], simp_all add: SQRT_UINT_MAX_def)
                    apply(subst (asm) le_less,simp)
                   apply(cases "r = 65532", simp_all)
                   apply(cases "r = 65533", simp_all)
                   apply(cases "r = 65534", simp_all)
                   by(cases "r = 65535", simp_all)
               qed
            qed
        qed
      qed
    qed
  qed

subsection\<open>Rationale:\<close>

text\<open>I suppose that  this algorithm is more efficient than implementations based on:

   \<^item> linear lists containing the full sieve upto \<^term>\<open>SQRT_UINT_MAX\<close>, so \<^term>\<open>2^32\<close> in C.
   \<^item> clever data-structures in OCaml implementations (Jean-Christophe Filiâtres suggestion.)

According to the prime number theorem, the number of divisors for prime numbers close to
\<^term>\<open>2^64\<close> is \<open>\<pi>(sqrt(n)) \<simeq> sqrt n / ln(sqrt n)\<close>, so approximatively 5900. The algorithm checks 
in the worst-case "\<open>n\<close> is indeed a prime number" \<open>2^32 / 3 \<simeq> 21850\<close> candidates. It is thus a 
factor 4 slower. On the other hand, the probability to run in such a worst case is in the interval
of \<^term>\<open>2^63\<close>  to  \<^term>\<open>2^64\<close> just \<open>2%\<close> ! Given the fact that the above loop should fit 
in the TLB of any modern processor, there is a good chance that the above algorithm is
the fastest in the average and in the considered interval up to  \<^term>\<open>2^64\<close> for \<open>n\<close>. 

And compared to an efficient general implementation in another platform such as OCaml I would
bet my hat that the above code wins again. 

\<^bold>\<open>Morale\<close> The pudding comes with the verification: while the program is optimized  to the 
input interval and the concrete implementation platform, the verification complexity increases
substantially for justifying the gains in efficiency ! As a consequence, there is a market
in highly-optimized, strongly taylored programs tweaked for a particular platform, in particular
if the latter has only limited resources.

\<close>

end
