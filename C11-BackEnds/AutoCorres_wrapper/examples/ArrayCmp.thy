(******************************************************************************
 * Isabelle/C/AutoCorres
 *
 * Copyright (c) 2019-2020 Université Paris-Saclay, France
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

theory ArrayCmp imports
  Isabelle_C_AutoCorres.AutoCorres_Wrapper
begin


section\<open>Description\<close>

text\<open>
The program compares (with respect to the lexicographic order) the subarrays
with the first n elements of given arrays t1 and t2. The return values are
\<^enum>   0 if the subarrays are equal,
\<^enum>   1 if the subarray in t1 is greater than in t2,
\<^enum>  -1 if the subarray in t2 is greater than in t1 \<close>

declare [[AutoCorres]]

C\<open>
//@ install_autocorres ArrayCmp [heap_abs_syntax]

int ArrayCmp(int n, int* t1, int* t2) {
  int i;
  for (i = 0; i < n; i++) {   
    if (t1[i] > t2[i])         
      return -1;
    else if (t1[i] < t2[i])    
      return 1;
  }
  return 0;
}

\<close>

section\<open>The Proofs (YET TO DO)\<close>


end
