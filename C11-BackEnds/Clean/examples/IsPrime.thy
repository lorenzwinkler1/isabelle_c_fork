(******************************************************************************
 * Clean
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
 * IsPrime-Test 
 *
 * Authors : Burkhart Wolff, Frédéric Tuong
 *)

chapter \<open> Clean Semantics : Another Clean Example\<close>


theory IsPrime
  imports Clean.Clean
          Clean.Hoare_Clean
          Clean.Clean_Symbex
          "HOL-Computational_Algebra.Primes"
begin

section\<open>The Primality-Test Example at a Glance\<close>

definition "SQRT_UINT_MAX = (65536::nat)"


function_spec isPrime(n :: nat) returns bool
pre "\<open>True\<close>" 
post"\<open>\<lambda>res. res \<longleftrightarrow> prime n \<close>"
local_vars   i :: nat
defines " if\<^sub>C \<open>n < 2\<close>  
            then return\<^bsub>local_isPrime_state.result_value_update\<^esub> \<open>False\<close>
            else skip\<^sub>S\<^sub>E 
          fi ;-
          \<open>i := 2\<close> ;- 
          while\<^sub>C \<open>i < SQRT_UINT_MAX \<and> i*i \<le> n  \<close> 
            do if\<^sub>C \<open>n mod i = 0\<close>  
                  then return\<^bsub>local_isPrime_state.result_value_update\<^esub> \<open>False\<close>
                  else skip\<^sub>S\<^sub>E 
                fi ;-
                \<open>i := i + 1 \<close> 
            od ;-
         return\<^bsub>local_isPrime_state.result_value_update\<^esub> \<open>True\<close>"


lemma isPrime_correct : 
  "\<lbrace>\<lambda>\<sigma>.   \<triangleright> \<sigma> \<and> isPrime_pre (n)(\<sigma>) \<and> \<sigma> = \<sigma>\<^sub>p\<^sub>r\<^sub>e \<rbrace> 
     quicksort (lo, hi) 
   \<lbrace>\<lambda>r \<sigma>. \<triangleright> \<sigma> \<and> isPrime_post(n) (\<sigma>\<^sub>p\<^sub>r\<^sub>e)(\<sigma>)(r) \<rbrace>"
   oops



end
