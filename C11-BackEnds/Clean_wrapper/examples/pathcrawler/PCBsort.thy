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

chapter \<open>Example: Bubblesort.  \<close>

theory PCBsort
  imports Isabelle_C_Clean.Clean_Wrapper
begin
\<comment> \<open>Derived from: \<^url>\<open>http://pathcrawler-online.com:8080\<close>\<close>

declare [[Clean]]

text\<open>Bubble sort of a given array 'table' of  a given length 'l' in descending order.

   This example is interesting because of its
   \<^enum> variable dimension input array
   \<^enum> loop with a variable number of iterations,
     which is limited by limiting the array dimension
   \<^enum> oracle which does not sort but checks the result is ordered  \<close>

C \<open>

    void bsort (int * table, int l) 
    {
      int i, temp, nb;
      char fini;
      fini = 0;
      nb = 0;
      while ( !fini && (nb < l-1)){      /* line 16 */
        fini = 1;
        for (i=0 ; i<l-1 ; i++)          /* line 18 */
          if (table[i] < table[i+1]){    /* line 19 */
           	fini = 0;
           	temp = table[i];
           	table[i] = table[i + 1];
           	table[i + 1] = temp;
           }
       nb++;
      }
    }
\<close>

end