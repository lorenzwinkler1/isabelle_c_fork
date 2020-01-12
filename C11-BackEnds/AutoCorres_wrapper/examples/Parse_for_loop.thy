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

chapter \<open>Example: Miscellaneous\<close>

text \<open> This example is used to demonstrate Isabelle/C/AutoCorres in a version that uses
AutoCorres Annotations addressed to AutoCorres. The example annotation is found in the C function
\<open>g\<close>. Note that this proceeding is not necessarily recommended --- since AutoCorres does
not support semantic PIDE support, editing feedback is limited and the workflow somewhat
clumpsy. \<close>

theory Parse_for_loop
imports
  Isabelle_C_AutoCorres.AutoCorres_Wrapper
  "HOL-Computational_Algebra.Primes"
begin

text \<open>The invocation of AutoCorres:\<close>
declare [[AutoCorres]]

text \<open>Setup of AutoCorres for semantically representing this C element:\<close>
declare_autocorres parse_for_loop [ ts_rules = nondet, unsigned_word_abs = f g h f2 ]

C\<open>
/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* It also tests
   - post-increment and decrement (which are common for loops)
   - arrays on the heap and stack (treated differently in VCG-land)
*/

int *f(int *i, int c)
{
  unsigned j;
  for (j = 0; j < 4; j++) i[j] = i[j] + c;
  i[0]++;
  return i;
}

int g(int c)
{ /** +@ INVARIANT: "\<lbrace> 0 <= \<acute>j \<and> \<acute>j <= 10 \<rbrace>"
      +@ highlight */
  for (unsigned int j = 10; 0 < j; j--)
    // This is where the above invariant gets ultimately attached:
    /** INVARIANT: "\<lbrace> 0 <= \<acute>j \<and> \<acute>j <= 10 \<rbrace>" */
    {
      c = c + j;
    }
  return c;
}

int h(int c)
{
  int a[10];
  for (unsigned int j = 0; j < 10; j++) a[j] = j;
  a[0] = a[1] + a[2];
  return a[0];
}

int f2(int *a)
{
  int j, res;
  for (j=0,res=0; j < 32; j += 4) { res += a[j]; }
  return res;
}

\<close>

find_theorems name:"parse_for_loop"

thm parse_for_loop.g'_def[simp]
thm parse_for_loop_global_addresses.g_body_def  (* The invariant has been transmitted to AutoCorres *)

end
