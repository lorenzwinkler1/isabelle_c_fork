(******************************************************************************
 * Isabelle/C/Clean
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * Authors : F. Tuong, B. Wolff
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

chapter \<open>Example: Mergesort.  \<close>

theory PCMergeError2
  imports Isabelle_C_Clean.Clean_Wrapper
begin
\<comment> \<open>Derived from: \<^url>\<open>http://pathcrawler-online.com:8080\<close>\<close>

declare [[Clean]]

text\<open>Merge of two given ordered arrays t1 and t2 of length l1 and l2 resp.
   into a ordered array t3

   This example is the same as Merge except that it contains an error at line 35
   which means that the index of t3 is not incremented
   and the same element of t3 is overwritten.
   This causes some test-cases to give a "failure" verdict.
   By examining the outputs of these test-cases,
   the user will see that not all elements of t3 are written
   (an error that cannot be directly detected by the oracle).
   This information can be used to locate the bug. \<close>

C \<open>

void Merge (int t1[], int t2[], int t3[], int l1, int l2) {

        int i = 0;
        int j = 0;
        int k = 0;
       
        while (i < l1 && j < l2) {     /* line 21 */
          if (t1[i] < t2[j]) {     /* line 22 */
            t3[k] = t1[i];
            i++;
            }
          else {
            t3[k] = t2[j];
            j++;
            }
          k++;
          }
        while (i < l1) {     /* line 32 */
          t3[k] = t1[i];
          i++;
          /* error : missing instruction k++; here */
          }
        while (j < l2) {     /* line 37 */
          t3[k] = t2[j];
          j++;
          k++;
          }
}      

\<close>

end