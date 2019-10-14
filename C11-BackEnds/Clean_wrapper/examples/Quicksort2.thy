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

theory Quicksort2
  imports Isabelle_C_Clean.Backend
begin
\<comment> \<open>Derived from: \<^file>\<open>../../../l4v/src/tools/autocorres/tests/examples/Quicksort.thy\<close>\<close>

C \<open>
//@ declare [[Clean_C99]]

#define MAXSIZE 100

unsigned int A[MAXSIZE];

void swap (unsigned long i, unsigned long j) {
  unsigned long tmp = A[i]; A[i] = A[j]; A[j] = tmp;
}

unsigned long partition (unsigned long lo, unsigned long hi) { 
  unsigned long pivot = A[hi];
  unsigned long i = lo;
  for (unsigned long j = lo; j < hi; j++) { 
     if (A[j] < pivot) { swap(i, j); i++; }
     swap(i, j);
  }
  return i;
}

void quicksort (unsigned long lo, unsigned long hi) {
    if( lo < hi) {
        unsigned long p = partition(lo, hi);
        quicksort(lo, p - 1);
        quicksort(p + 1, hi);
     }
}
\<close>

find_theorems (100) name:quick name:"inv"

end
