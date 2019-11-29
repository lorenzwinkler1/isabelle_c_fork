(******************************************************************************
 * Isabelle/C/Clean
 * 
 * Authors: F. Tuong, B. Wolff
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


chapter \<open>Example: Triangle Type \<close>
text\<open>
   A classic example from test generation literature
   which contains no loops or arrays
   but is interesting for its simple example of an oracle.
   This implementation does not handle negative inputs correctly 

   Determines the type of a triangle given its three edges i,j,k 
   \<^enum>   4 = Not a triangle        
   \<^enum>   3 = Equilateral triangle 
   \<^enum>   2 = Isosceles triangle   
   \<^enum>   1 = Any other triangle 
\<close>

theory PCTritype
  imports Isabelle_C_Clean.Clean_Wrapper
begin
\<comment> \<open>Derived from: \<^url>\<open>http://pathcrawler-online.com:8080\<close>\<close>

C \<open>
//@ declare [[Clean]]

int tritype(int i, int j, int k){
  int type_code;
  if ((i == 0) || (j == 0) || (k == 0)) type_code = 4;     /* line 14 */
  else {
    type_code = 0;
    if (i == j) type_code = type_code + 1;                 /* line 17 */
    if (i == k) type_code = type_code + 2;                 /* line 18 */
    if (j == k) type_code = type_code + 3;                 /* line 19 */
    if (type_code == 0){                                   /* line 20 */
      if ((i+j <= k) || (j+k <= i) || (i+k <= j))          /* line 21 */
	type_code = 4;
      else
	type_code = 1;
      }
    else if (type_code > 3) type_code = 3;                 /* line 26 */
    else if ((type_code == 1) && (i+j > k)) type_code = 2; /* line 27 */
    else if ((type_code == 2) && (i+k > j)) type_code = 2; /* line 28 */
    else if ((type_code == 3) && (j+k > i)) type_code = 2; /* line 29 */
    else type_code = 4;
    }
  return type_code;
}
           
\<close>

end
