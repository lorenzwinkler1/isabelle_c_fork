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
(* For the original C-example:
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

chapter \<open>Example: A slightly optimized Sqrt Prime Sample Proof\<close>

text\<open>This example is used to demonstrate Isabelle/C/AutoCorres in a version that keeps
the theory development of the background theory as well as the program annotations completely 
\<^emph>\<open>outside\<close> the C source. This particular development style that keeps the program
separate from its theory we call TCC (\<^emph>\<open>Theories Carrying Code\<close>). It has the 
advantage that developers of development and verification teams can be separated,
as is required by many certification standards.
Note that the opposite style that we call CCT (\<^emph>\<open>Code-carrying Theories\<close>) is also 
supported by Isabelle/C. In CCT style, Programs become a kind of ``proof-carrying (high-level) code''.
Exports of the C-sources will contain their theory (not only their annotations) as comments
\<^emph>\<open>inside\<close> which might be also useful in certification as well as advanced  
``proof-carrying code'' securization schemes of server platforms. 

Of course, since developments can mix C code and HOL developments in an arbitrary manner,
these two style have to be thought of as extremes in a continuum. \<close>

theory IsPrime_sqrt_opt_TCC
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
  In our example, everything is proven, the trust of this verification only relies
  on:
  \<^item> The logical consistency of HOL and its correct implementation in Isabelle/HOL, and
  \<^item> that the assumptions of AutoCorres wrt. to the underlying C-semantics
    are valid, in an ARM processor model. 

The main optimisation compared to the theory \<^verbatim>\<open>IsPrime_sqrt\<close> is that in a reasonably
large interval, it suffices to check only for odd divisors smaller the integer
squareroot of \<open>n\<close>.\<close>

section\<open>Background\<close>

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

lemma three_and_divides : "prime (p::nat) \<Longrightarrow> 3 < p \<Longrightarrow> \<not>(3 dvd p)"
  using primes_dvd_imp_eq three_is_prime_nat by blast





section\<open>The C code for \<open>O(sqrt(n))\<close> Primality Test Algorithm\<close>

text \<open>The invocation of AutoCorres:\<close>

declare [[AutoCorres]]

text \<open>Setup of AutoCorres for semantically representing this C element:\<close>
declare_autocorres is_prime [ ts_rules = nondet, unsigned_word_abs = is_prime ]

text\<open> This C code contains a function that determines if the given number
      @{term n} is prime.

      It returns 0 if @{term n}  is composite, or non-zero if @{term n}  is prime.
 
      This is a faster version than a linear primality test; runs in O(sqrt(n)). \<close>

C \<open>
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

    for (unsigned i = 3; i < SQRT_UINT_MAX - 1 && i * i <= n; i+=2) {
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


section\<open>The Specification and Some Corrollaries\<close>
text\<open>This section contains the auxilliary definitions and lemmas for the 
     final correctness proof; in particular, the loop invariant is stated here.\<close>


definition is_prime_inv
  where [simp]: "is_prime_inv n i s \<equiv> (2 < i \<and> odd i \<and> 
                                       i \<le> SQRT_UINT_MAX + 1 \<and> i < n \<and>   
                                       partial_prime n i)"


lemma "\<not> 2 dvd i = (i mod 2 = (1::nat))"
  using odd_iff_mod_2_eq_one by blast


lemma inv_preserved0: "is_prime_inv n i s \<Longrightarrow> \<not> i dvd n \<Longrightarrow> partial_prime n (Suc(Suc i))"
  unfolding  is_prime_inv_def partial_prime_def
(* sledgehammer finds proofs, reconstructions fail *)
proof(simp, elim conjE)
  fix i :: nat
  assume 1: "odd i"
  and    2: "i < n"
  and    3: "2 < i"
  and    6: "\<forall>i\<in>{2..<min n i}. \<not> i dvd n"
  and    7 :"\<not> i dvd n"
  have   *: "even(Suc i)" by(simp add:1)
  have  **: "\<forall>i\<in>{2..<i}. \<not> i dvd n" 
    by (simp add: "2" "6" order_le_less)
  show "\<forall>i\<in>{2..<min n (Suc(Suc i))}. \<not> i dvd n"
  proof (rule ballI, simp, elim conjE) 
    fix j :: nat
    assume 8:"j < (Suc(Suc i))"
    and 9 :"2 \<le> j"
    have *** : "j < i \<or> j = i \<or> j = Suc i"  
      using "8" less_antisym by blast    
    show "\<not> (j dvd n)" 
    proof(insert ***, elim disjE)
      assume "j < i" show "\<not> j dvd n" 
        by (simp add: "**" "9" \<open>j < i\<close>)
    next
      assume "j = i" show "\<not> j dvd n"
        by (simp add: "7" \<open>j = i\<close>)
    next
      assume "j = Suc i" show "\<not> j dvd n"
        by (metis "*" "**" "3" Suc_1 \<open>j = Suc i\<close> atLeastLessThan_iff dvd_trans less_or_eq_imp_le 
                  less_trans_Suc one_less_numeral_iff semiring_norm(76))
    qed
  qed
qed



  
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

lemma aux95 : "r * r \<le> SQRT_UINT_MAX * SQRT_UINT_MAX - Suc 0 \<Longrightarrow> r < SQRT_UINT_MAX"
  by (metis SQRT_UINT_MAX_def rel_simps(76) sqr_le_sqr_minus_1)

lemma aux96 :  "r < SQRT_UINT_MAX - (1::nat) \<Longrightarrow> r \<le> 65534"
  unfolding SQRT_UINT_MAX_def by simp

lemma aux97 : "even 65534" by simp
lemma aux98 : "(13::nat) dvd 65533" by simp
lemma aux99 : "even 65532" by simp
lemma aux100 : "(19::nat) dvd 65531" by simp
lemma aux101 : "even 65530" by simp
lemma aux102 : "(3::nat) dvd 65529" by simp
lemma aux104 : "(7::nat) dvd 65527" by simp
lemma aux106 : "(3::nat) dvd 65523" by simp
(*  65521 is prime. Largest prime number smaller SQRT_UINT_MAX. *)


section\<open>The Correctness Proof \<close>

text\<open>Note that the proof \<^emph>\<open>injects\<close> the loop invariant at the point where the proof
     treats the loop.\<close>


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
            apply (unfold is_prime'_def dvd_eq_mod_eq_0 [symmetric] SQRT_UINT_MAX_def [symmetric], 
                   insert 1 * **)
            text\<open>... and here happens the annotation with the invariant:
                 by instancing @{thm whileLoopE_add_inv}.
                 One can say that the while loop is spiced up with the
                 invariant and the measure by a rewrite step. \<close>
            apply (subst whileLoopE_add_inv 
                         [  where I = "\<lambda>r s. is_prime_inv n r s"
                            and   M = "\<lambda>(r, s). (Suc n) * (Suc n) - r * r"])
         proof (wp,clarsimp, intro conjI) (* split proof obligations *)
           text\<open>prelude-condition: returns false for even n and 3 dvd n respect inv\<close>   
           assume 2: "\<not> 3 dvd n "
              and  3: "odd n"
              and  4: "8 < n"
           show "\<lbrace>\<lambda>s. is_prime_inv n 3 s\<rbrace> return (even n \<or> 3 dvd n) 
                 \<lbrace>\<lambda>ret s.  if ret then (0 \<noteq> 0) = prime n
                           else if n < 9 then (1 \<noteq> 0) = prime n 
                                else is_prime_inv n 3 s\<rbrace>!"
             apply(wp) using 1 2 3 4 by auto
         next
           text\<open>Invariant initially true\<close>
           fix s::lifted_globals
           assume 2: "\<not> 3 dvd n "
             and  3: "odd n"
             and  4: "8 < n"
           show "if n < 2 then (0 \<noteq> 0) = prime n
                 else if n < 4 then (1 \<noteq> 0) = prime n 
                      else is_prime_inv n 3 s"
             using 1 2 3 4 apply(simp del:is_prime_inv_def)
             unfolding is_prime_inv_def SQRT_UINT_MAX_def UINT_MAX_def
             apply(simp add: UINT_MAX_def)
             unfolding partial_prime_def
             apply auto
             by(case_tac "i=2", auto) 
         next
           text\<open>Case : Exit loop since divisor found\<close>
           fix r 
           assume 1 : "2 < r"  and 2 : " r * r \<le> n"
           show       "r dvd n \<longrightarrow> \<not> prime n"
             using "1" "2" prime_dvd by auto
         next
           text\<open>All sorts of non-linear boundary conditions at the end\<close>
           fix r::nat
           assume "\<not> 3 dvd n "
             and "odd n"
             and "odd r"
             and "2 < r"
             and "n \<le> SQRT_UINT_MAX * SQRT_UINT_MAX - Suc 0"
             and "r \<le> Suc SQRT_UINT_MAX"
             and "r < 65535"
             and "partial_prime n r"
             and "r < n"
             and "r * r \<le> n"
           have ** : "r \<le> n" 
             by (simp add: \<open>r < n\<close> less_or_eq_imp_le)  
           have *** : "r \<le> 65534" 
             using \<open>r < 65535\<close> by linarith  
           have ****: "Suc (Suc (Suc (Suc (r + (r + (r + (r + r * r))))))) = (r+2) * (r+2)"
             by simp
           have ***** : "(r + (r + (r + (r + r * r))) \<le> 4294967291) = 
                         ((r + 2) * (r + 2) \<le> SQRT_UINT_MAX * SQRT_UINT_MAX - Suc 0)"
             by (simp add: SQRT_UINT_MAX_def)
           have 66 : "(Suc r) dvd n \<Longrightarrow> even n" 
             using \<open>odd r\<close> by auto
           show "\<not> r dvd n \<longrightarrow>  Suc r \<le> SQRT_UINT_MAX \<and>
                                Suc (Suc r) < n \<and>
                                (Suc (Suc r) < n \<longrightarrow> \<not> Suc r dvd n) \<and>
                                n + (n + n * n) - Suc (Suc (Suc (r + (r + (r + (r + r * r))))))
                                < Suc (n + (n + n * n)) - r * r \<and>
                 (r < 65533 \<longrightarrow> Suc (Suc (Suc (Suc (r + (r + (r + (r + r * r)))))))
                                \<le> SQRT_UINT_MAX * SQRT_UINT_MAX - Suc 0)"
             unfolding SQRT_UINT_MAX_def
             apply(auto)
                 using \<open>r < 65535\<close> apply linarith
                apply (smt One_nat_def Suc_leI \<open>odd r\<close> \<open>r * r \<le> n\<close> dvdI even_Suc even_mult_iff 
                           leD le_trans n_less_n_mult_m odd_pos order_le_less unit_imp_dvd)
               using "66" \<open>odd n\<close> apply blast
              apply (metis \<open>r < n\<close> diff_Suc_Suc diff_less_mono2 le_def less_Suc_eq mult_Suc_right 
                           mult_le_mono not_less_eq_eq sqr_bla sqr_less_mono)
             apply(subst *****)
             by (smt SQRT_UINT_MAX_def Suc_less_eq Suc_numeral add_2_eq_Suc' less_Suc_eq rel_simps(76) 
                     semiring_norm(2) semiring_norm(5) semiring_norm(8) sqr_le_sqr_minus_1)
             
         next
           text\<open>Invariant finally established post-condition. Nontrivial.\<close>
           fix r::nat and s::lifted_globals
           assume 2: "\<not> 3 dvd n "
              and  3: "odd n"
             and  4: "8 < n"
             and  5: "is_prime_inv n r s "
             and  6: "\<not> (r < 65535 \<and> r * r \<le> n) "
           have **: "r * r > n  \<or> r \<ge> 65535 " 
             using "6" le_def by blast
           have ***: "partial_prime n r" 
             using "5" by auto
           have ****: "partial_prime n 65535 \<Longrightarrow> partial_prime n SQRT_UINT_MAX" 
             apply(rule subst[of "Suc 65535" "SQRT_UINT_MAX"])
              apply(simp add: SQRT_UINT_MAX_def)
             apply(subst partial_prime_Suc,simp) 
             unfolding partial_prime_def  
             apply auto
             using False by fastforce
           have ***** : "Suc 65535 = SQRT_UINT_MAX" unfolding SQRT_UINT_MAX_def by simp
           show "(1 \<noteq> (0::nat)) = prime n" 
             apply(simp,insert **, erule disjE)
             using "5" partial_prime_sqr apply auto[1]
             apply(insert 1 ***,case_tac "r = 65535", auto)
             using "****" aux95 nat_le_Suc_less partial_prime_sqr apply auto[1]
             apply(subst (asm) Nat.le_eq_less_or_eq, auto)
             apply(subst (asm) Nat.less_eq_Suc_le)
             apply(subst (asm) *****)
             by (meson aux95 le_trans not_less partial_prime_sqr)
         qed
        qed
      qed
    qed
qed


end
