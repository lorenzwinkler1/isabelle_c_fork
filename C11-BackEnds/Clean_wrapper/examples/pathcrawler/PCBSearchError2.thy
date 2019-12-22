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

chapter \<open>Example: Access to uninitialized variables.  \<close>

theory PCBSearchError2
  imports Isabelle_C_Clean.Clean_Wrapper
begin
\<comment> \<open>Derived from: \<^url>\<open>http://pathcrawler-online.com:8080\<close>\<close>

declare [[Clean]]

text\<open> Binary search of a given element in a given ordered array
      returning 1 if the element is present and 0 if not.
     
      This example is like Bsearch but contains an error at line 30
      which causes several cases to have a "failure" verdict.
      
      The failed test cases are exactly those which cover the paths
      in which the 1st subcondition of line 30 is satisfied,
      which indicates the location of the error.  \<close>

C \<open>

int Bsearch( int A[10], int elem)
{
  int low, high, mid, found ;

  low = 0 ;
  high = 9 ;
  found = 0 ;
  while( ( high > low ) )                     /* line 18 */
    { 
      mid = (low + high) / 2 ;
      if( elem == A[mid] )                    /* line 21 */ 
	found = 1;
      if( elem > A[mid] )                     /* line 23 */
        low = mid + 1 ;
      else
        high = mid - 1;
    }  
  mid = (low + high) / 2 ;
  /* error, next line should be : if( ( found != 1)  && ( elem == A[mid]) ) */
  if( ( found != 1)  && ( elem != A[mid]) )    /* line 30 */
    found = 1; 

  return found ;
}


\<close>

end