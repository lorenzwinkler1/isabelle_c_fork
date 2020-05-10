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

theory IsPrime_sqrt_opt2_TCC
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
#define TRUE 1
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
  where [simp]: "is_prime_inv n i s \<equiv> (5 \<le> i \<and> i \<le> SQRT_UINT_MAX - 1 \<and> i * i \<le> n \<and> 
                                       (i mod 6) = 5 \<and> partial_prime n i)"


lemma "\<not> 2 dvd i = (i mod 2 = (1::nat))"
  using odd_iff_mod_2_eq_one by blast


lemma inv_preserved0: "is_prime_inv n i s \<Longrightarrow> 
                       \<not> i dvd n \<Longrightarrow>  \<not> (i+2) dvd n \<Longrightarrow> 
                       odd n \<Longrightarrow> \<not> (3 dvd n) \<Longrightarrow>
                       partial_prime n (i + 6)"
  unfolding  is_prime_inv_def partial_prime_def
proof(simp, elim conjE)
  fix i :: nat
  assume 1: "odd n"
  and    2: "\<not> (3 dvd n)"
  and    2: "i * i \<le> n"
  and    3: "5 \<le> i"
  and    6: "\<forall>i\<in>{2..<min n i}. \<not> i dvd n"
  and    7 :"\<not> i dvd n"
  and    8 :"\<not> (Suc(Suc i)) dvd n"
  and    9:  "i mod 6 = 5"
  have  00 :"5 \<le> n" 
    by (meson "2" "3" le_square order.trans)
  have  *: "\<forall>i\<in>{2..<i}. \<not> i dvd n"
    by (metis "2" "6" le_antisym le_square min_absorb2 min_def order.trans)
  have  **: "odd i"  
    using "9" by presburger
  have  ***: "\<not>(3 dvd i)" sorry
  have  ****: "i \<noteq> 0 \<Longrightarrow> \<not>(5 dvd i)" sorry
  have a : "5 * 5 \<le> n" 
    by (metis "2" "9" mod_less_eq_dividend mod_mult_mult2 mult_le_mono2 order.trans) 
  have  *****: "i + 6 < n" sorry
  show "\<forall>i\<in>{2..<min n (i + 6)}. \<not> i dvd n"
  proof (rule ballI, simp, elim conjE) 
    fix j :: nat
    assume 10:"j < i + 6"
    and 11 :"2 \<le> j"
    and 12: "j < n"
    show "\<not>(j dvd n)" 
    proof(cases "j < i")
      case True
      then show ?thesis 
        by (simp add: "*" "11")
    next
      case False
      have "j\<ge>i" 
        by (simp add: False le_def)
      have *:"j = i+5 \<or> j = i+4 \<or> j = i+3 \<or> j = i+2 \<or> j = i+1 \<or> j = i "
        using "10" False by linarith
      then show ?thesis
      proof(insert *,elim disjE, simp_all)
        show "\<not> i + 5 dvd n" 
          using "**" "1" by auto
      next 
        show "\<not> i + 4 dvd n" sledgehammer sorry
      next 
        show "\<not> i + 3 dvd n" 
          using "**" "1" by auto
      next
        show "\<not> (Suc(Suc i)) dvd n" 
          by (simp add: "8")
      next
        show "\<not> (Suc i) dvd n" 
          using "**" "1" by auto
      next
        show "\<not> i dvd n" 
          by (simp add: "7")
    qed
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
          then show ?thesis  by (clarsimp simp:  is_prime'_def, wp, insert *, auto simp: prime_odd_nat three_and_divides) 
        next
          case False
          assume *** :"\<not> 3 dvd n"
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
            apply(wp, clarsimp)
            sorry
        qed
      qed
    qed
qed


end
