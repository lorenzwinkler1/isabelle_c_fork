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

theory PCExample12
  imports Isabelle_C_Clean.Clean_Wrapper
begin
\<comment> \<open>Derived from: \<^url>\<open>http://pathcrawler-online.com:8080\<close>\<close>

declare [[Clean]]

text\<open> Should return 1 if x is an element of ordered array A \<close>

C \<open>
int Bsearch( int A[8], int x) 
{
  int low, high, mid, found ;
  
  low = 1 ;
  high = 7 ;
  found = 0 ;
  while( high > low )                    // line 09
    { mid = (low + high) / 2 ;
    
      if( x == A[mid] )                  // line 12
         found = 1;

      if( x > A[mid] )                   // line 15
        low = mid + 1 ;
      else
        high = mid - 1;
    }  
  mid = (low + high) / 2 ;

  if( ( found != 1)  && ( x == A[mid]) ) // line 22
    found = 1; 
  
  return found ;
}


int spec_Bsearch(
  int *Pre_A, int *A, 
  int Pre_x, int x, 
  int result_implementation)
{
  int i;
  int present = 0;
  int modif = 8;
  
  for(i=0; i<8; i++)                     // line 38
    {
      if(A[i] != Pre_A[i])               // line 40
        modif = i;
      if(Pre_A[i] == Pre_x)              // line 42
	present = 1;
    }
  if(present==0 && present != result_implementation) {
    return 0; } /* implementation wrongly found x in A */
  else {
    if(present==1 && present != result_implementation) {
      return 0; } /* implementation wrongly said x was not in A */
    else {
      if(modif < 8) {                    // line 51
	return 0; } /* implementation modified A */
      else return 1;
    }
  }
  return 0;
}


int CompareBsearchSpec(int A[8], int x) // tested function
{
  int *Pre_A = (int *)malloc(8 * sizeof(int));
  int i;
  for (i = 0; i < 8; i++)                // line 64
    Pre_A[i] = A[i];
  int result_implementation=Bsearch(A,x);
  return(spec_Bsearch(Pre_A,A,x,x,result_implementation));
}

\<close>

end