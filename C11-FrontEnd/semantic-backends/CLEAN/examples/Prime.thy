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

theory Prime imports Isabelle_C_CLEAN.Backend
begin
declare[[CLEAN_on]]
C \<open>
#define SQRT_UINT_MAX 65536
int k = 0;

unsigned int is_prime(unsigned int n)
//@ PRE_CLEAN True
//@ POST_CLEAN \<open>if \<forall>i. n mod i \<noteq> 0         \
                then result=0 else result=1\<close>
{ if (n < 2) return 0;
  for (unsigned i = 2; i < SQRT_UINT_MAX
                       && i * i <= n; i++) {
    if (n % i == 0) return 0;
    k++;
  }
  return 1;
}\<close>

end
