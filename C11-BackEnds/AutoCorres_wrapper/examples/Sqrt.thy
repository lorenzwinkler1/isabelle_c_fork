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

theory Sqrt
imports
  Isabelle_C_AutoCorres.AutoCorres_Wrapper
  "HOL-Computational_Algebra.Primes"
begin
\<comment> \<open>Derived from: \<^file>\<open>../../../src_ext/l4v/src/tools/autocorres/tests/examples/IsPrime.thy\<close>\<close>

section\<open>The Theory of the \<open>O(sqrt(n))\<close> Primality Test Algorithm\<close>

text\<open>This section develops basic concepts of the invariant. This bit is presented here \<^emph>\<open>before\<close>
the actual code, but could also be after or even inside the \<^theory_text>\<open>C\<close> command as comment-annotation of 
the source.\<close>



section\<open>Background\<close>




section\<open>The C code for \<open>O(sqrt(n))\<close> Primality Test Algorithm\<close>

text \<open>The invocation of AutoCorres:\<close>


declare [[AutoCorres]]

text \<open>Setup of AutoCorres for semantically representing this C element:\<close>
declare_autocorres sqrt [ ts_rules = nondet, unsigned_word_abs = sqrt ]

C \<open>

unsigned int sqrt(unsigned int n)
{
    unsigned int i = 0;
    unsigned long long tm = 1;
    unsigned long long  sum = 1;
    while(sum < n) {
      i++;
      tm+=2;
      sum += tm;
    }
    return(i); 
}\<close>

thm sqrt.sqrt'_def

theorem (in sqrt) sqrt_correct':
    "\<lbrace> \<lambda>\<sigma>. n \<le> UINT_MAX \<rbrace> sqrt' n \<lbrace> \<lambda>res \<sigma>. res * res \<le> n \<and> (res+1)*(res+1) > n \<rbrace>!"
proof (rule validNF_assume_pre)
  fix s
  assume 1 : "n \<le> UINT_MAX"
  have 2 : "\<And>a. Suc (a + (a + a * a)) = (a+1)*(a+1)" by simp
  have 3 : "\<And>a. Suc (Suc (Suc (Suc (4 * a + a * a)))) =  (a+2)*(a+2)" by simp
  show ?thesis
    apply(clarsimp simp: sqrt'_def, wp, auto)
    apply (subst whileLoop_add_inv 
                  [where I = "\<lambda>(i, sum, tm)(s:: lifted_globals). 
                                     0\<le>i  
                                     \<and> tm = 2*i+1 
                                     \<and> sum=(i+1)*(i+1) 
                                     \<and> sum < ULONG_MAX "
                   and M = "\<lambda>((i, sum, tm),s). n - i " ])
    apply(insert 1, wp,clarify)
      apply(auto, simp_all only:  2 3)
          prefer 6  apply(simp add: UWORD_MAX_def UWORD_MAX_simps(1) ULONG_MAX_def)
    prefer 5 apply(insert 1) 

    
    sorry
qed