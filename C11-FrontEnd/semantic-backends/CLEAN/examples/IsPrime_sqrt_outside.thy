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

chapter\<open>A Sqrt Prime Sample Proof\<close>

text\<open>This example is used to demonstrate Isabelle/C/CLEAN in a version that keeps
annotations completely \<^emph>\<open>outside\<close> the C source. \<close>

theory IsPrime_sqrt_outside
imports
  "../src/compiler/C_CLEAN"
begin
\<comment> \<open>Derived from: \<^file>\<open>../../../../l4v/src/tools/autocorres/tests/examples/IsPrime.thy\<close>\<close>

section\<open>The C code for \<open>O(sqrt(n))\<close> Primality Test Algorithm\<close>

text\<open> This C code contains a function that determines if the given number 
      @{term n} is prime.

      It returns 0 if @{term n}  is composite, or non-zero if @{term n}  is prime.
 
      This is a faster version than a linear primality test; runs in O(sqrt(n)). \<close>



C \<open>
// @ CLEAN

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

end
