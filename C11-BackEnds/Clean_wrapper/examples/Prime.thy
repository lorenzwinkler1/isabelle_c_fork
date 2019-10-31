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

chapter \<open>Example: Prime\<close>

text\<open>This example shows how to use nested C-commands in as cascade syntax. 
Note that the innermost "n" inside the \<open>\<^C>\<open>n\<close>\<close> in the pre-condition binds to 
the parameter of the C function across the syntax barriers. Note that
the exported C code does not necessarily respect the lexical conventions of C
(a better implementation of the exporter may solve this.).


\<close>

theory Prime imports Isabelle_C_Clean.Clean_Wrapper
                  \<comment> \<open>Clean back-end is imported\<close>  
                     "../../../C11-FrontEnd/archive/Clean_backend_old" 
                      "HOL-Computational_Algebra.Primes" 
                  
begin                
                     no_syntax "_C" :: \<open>cartouche_position \<Rightarrow> _\<close> ("\<^C> _")

declare [[Clean]]


C \<open>
//@ definition \<open>prime\<^sub>H\<^sub>O\<^sub>L (p :: nat) =          \
          (1 < p \<and> (\<forall> n \<in> {2..<p}. \<not> n dvd p))\<close>
#   define SQRT_UINT_MAX 65536
unsigned int k = 0;
unsigned int prime\<^sub>C(unsigned int n) {
//@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<open>n\<close> \<le> UINT_MAX\<close>
//@ post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n \<open>\<^C>\<open>prime\<^sub>C(n)\<close> \<noteq> 0 \<longleftrightarrow> prime\<^sub>H\<^sub>O\<^sub>L \<^C>\<open>n\<close>\<close>
    if (n < 2) return 0;
    for (unsigned i = 2; i < SQRT_UINT_MAX
                         && i * i <= n; i++) {
      if (n % i == 0) return 0;
      k++;
    }
    return 1;
}\<close>

(*<*)
text\<open>
\begin{isar}
is_prime_core_def: "is_prime_core n \<equiv>
  if$_{\text{Clean}}$ \<Open> (n < 2) \<Close> then return 0 else skip;-
  \<Open> i := 2 \<Close>;-
  while$_{\text{Clean}}$ \<Open> i < SQRT_UINT_MAX \<and> i * i \<le> n\<Close>
    (if$_{\text{Clean}}$ \<Open>n mod i = 0\<Close>
      then return 0 else skip;
     \<Open>k:=k+1\<Close>; assert \<Open> k\<le>UINT_MAX \<Close>
     \<Open>i:=i+1\<Close>; assert \<Open> i\<le>UINT_MAX \<Close>) ;-
  return 1"

is_prime_def: "is_prime n \<equiv>
  block$_{\text{Clean}}$ push_local_is_prime_state
             (is_prime_core n)
             pop_local_is_prime_state"
\end{isar}
\<close>
(*>*)

lemma "prime\<^sub>H\<^sub>O\<^sub>L p = prime p"
by (simp add: prime\<^sub>H\<^sub>O\<^sub>L_def prime_nat_iff')

text_raw \<open>
\begin{figure}
  \centering
  \includegraphics[width=0.96\textwidth]{figures/A-C-Source7}
  \caption{Activating the Isabelle/C/Clean back-end}
  \label{fig:clean}
\end{figure}
\<close>

text \<open>
See \autoref{fig:clean}.
\<close>

end
