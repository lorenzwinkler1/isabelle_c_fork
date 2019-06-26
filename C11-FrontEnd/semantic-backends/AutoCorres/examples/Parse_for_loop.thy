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

chapter\<open>Example \<close>

text \<open> This example is used to demonstrate Isabelle/C/AutoCorres in a version that uses
AutoCorres Annotations addressed to AutoCorres. The example annotation is found in the C function
\<open>g\<close>. Note that this proceeding is not necessarily recommended --- since AutoCorres does
not support semantic PIDE support, editing feedback is limited and the workflow somewhat
clumpsy. \<close>

theory Parse_for_loop
imports
  AutoCorres_backend.Backend
  "HOL-Computational_Algebra.Primes"
begin

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

//  Setup of AutoCorres for parsing and semantically representing this C element.
//@  install_autocorres parse_for_loop [ ts_rules = nondet, unsigned_word_abs = f g h f2 ]


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
