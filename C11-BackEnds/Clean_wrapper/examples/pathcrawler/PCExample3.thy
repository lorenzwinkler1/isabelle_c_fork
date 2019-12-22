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

chapter \<open>Example: Tritype (version 3) \<close>

theory PCExample3
  imports Isabelle_C_Clean.Clean_Wrapper
begin
\<comment> \<open>Derived from: \<^url>\<open>http://pathcrawler-online.com:8080\<close>\<close>

declare [[Clean]]

text\<open> This program should return the type of the triangle which has sides of these lengths.
\<^enum>   3 = not a triangle
\<^enum>   2 = equilateral triangle
\<^enum>   1 = isoceles triangle
\<^enum>   0 = other triangle
\<close>

C \<open>
int Tritype(double i, double j, double k){
  int trityp = 0;
//  if (i < 0.0 || j < 0.0 || k < 0.0)        // line 10  
//    return 3;
//  if (i + j <= k || j + k <= i || k + i <= j)//line 12 
//    return 3; 
  if (i == j) trityp = trityp + 1;            // line 14
  if (i == k) trityp = trityp + 1;            // line 15
  if (j == k) trityp = trityp + 1;            // line 16
  if (trityp >= 2)                            // line 17
      trityp = 2;
  return trityp;
}
\<close>

end
