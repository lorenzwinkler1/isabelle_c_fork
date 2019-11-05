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

chapter \<open>Example: A Sqrt Prime Sample Proof\<close>

text\<open>This example is used to demonstrate Isabelle/C/Clean in a version that keeps
annotations completely \<^emph>\<open>outside\<close> the C source. \<close>

theory IsPrime_sqrt_outside
  imports Isabelle_C_Clean.Clean_Wrapper
begin
\<comment> \<open>Derived from: \<^file>\<open>../../../l4v/src/tools/autocorres/tests/examples/IsPrime.thy\<close>\<close>

section\<open>The C code for \<open>O(sqrt(n))\<close> Primality Test Algorithm\<close>

text\<open> This C code contains a function that determines if the given number 
      @{term n} is prime.

      It returns 0 if @{term n}  is composite, or non-zero if @{term n}  is prime.
 
      This is a faster version than a linear primality test; runs in O(sqrt(n)). \<close>

declare [[Clean]]

C \<open>

/*
\<comment> \<open>It is possible to activate the Clean back-end at the command level or via an annotation command.\<close>
//@ declare [[Clean]]
*/

#define SQRT_UINT_MAX 65536

unsigned int is_prime(unsigned int n)
{
    /* Numbers less than 2 are not primes. */
    if (n < 2)
        return 0;

    /* Find the first non-trivial factor of 'n' or sqrt(UINT_MAX), whichever comes first. */
    /* Find the first non-trivial factor of 'n' less than sqrt(n). */

    for (unsigned i = 2; i < SQRT_UINT_MAX && i * i <= n; i++) {
        if (n % i == 0)
            return 0; 
    }

    /* No factors. */
    return 1;
}\<close>
find_theorems (100) name:is_prime name:core   (* this shows that the Clean package does not generate yet the expected theorems *)



end
