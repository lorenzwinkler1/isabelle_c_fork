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

chapter \<open>Example: Lexer Stress Test\<close>

theory C0
  imports Isabelle_C_Advance.C_Main
begin

declare[[C_lexer_trace]]

section \<open>Regular C Code\<close>

subsection \<open>Comments, Keywords and Pragmas\<close>

C \<comment> \<open>Nesting of comments following the example suite of
      \<^url>\<open>https://gcc.gnu.org/onlinedocs/cpp/Initial-processing.html\<close>\<close> \<open>
/* inside /* inside */ int a = "outside";
// inside // inside until end of line
int a = "outside";
/* inside
  // inside
inside
*/ int a = "outside";
// inside /* inside until end of line
int a = "outside";
\<close>

C \<comment> \<open>Backslash newline\<close> \<open>
i\    
n\                
t a = "/* //  /\ 
*\
fff */\
";
\<close>

C \<comment> \<open>Backslash newline, Directive \<^url>\<open>https://gcc.gnu.org/onlinedocs/cpp/Initial-processing.html\<close>\<close> \<open>
/\
*
*/ # /*
*/ defi\
ne FO\
O 10\
20
int;\<close>

C \<comment> \<open>Directive: conditional\<close> \<open>
#ifdef a
#elif
#else
#if
#endif
#endif
int;\<close>
(*
C \<comment> \<open>Directive: pragma\<close> \<open># f # "/**/"
/**/
#     /**/ //  #

_Pragma /\
**/("a")
\<close>
*)
C \<comment> \<open>Directive: macro\<close> \<open>
#define a zz
#define a(x1,x2) z erz(( zz
#define a (x1,x2) z erz(( zz
#undef z
#if
#define a zz
#define a(x1,x2) z erz(( zz
#define a (x1,x2) z erz(( zz
#endif
int;\<close>

subsection \<open>Scala/jEdit Latency on Multiple Bindings\<close>

C \<comment> \<open>Example of obfuscated code \<^url>\<open>https://en.wikipedia.org/wiki/International_Obfuscated_C_Code_Contest\<close>\<close> \<open>
#define _ -F<00||--F-OO--;
int F=00,OO=00;void main(){F_OO();printf("%1.3f\n",4.*-F/OO/OO);}void F_OO()
{
            _-_-_-_
       _-_-_-_-_-_-_-_-_
    _-_-_-_-_-_-_-_-_-_-_-_
  _-_-_-_-_-_-_-_-_-_-_-_-_-_
 _-_-_-_-_-_-_-_-_-_-_-_-_-_-_
 _-_-_-_-_-_-_-_-_-_-_-_-_-_-_
_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_
_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_
_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_
_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_
 _-_-_-_-_-_-_-_-_-_-_-_-_-_-_
 _-_-_-_-_-_-_-_-_-_-_-_-_-_-_
  _-_-_-_-_-_-_-_-_-_-_-_-_-_
    _-_-_-_-_-_-_-_-_-_-_-_
        _-_-_-_-_-_-_-_
            _-_-_-_
}
\<close>

text \<open> Select inside the ball, experience the latency.
A special keyboard combination ``Ctrl-like key\<^footnote>\<open>on Apple: Cmd\<close> + Shift +
Enter'' lets Isabelle/Scala/jEdit enter in a mode where the selected bound occurrences can be all
simultaneously replaced by new input characters typed on the keyboard. (The ``select-entity'' action
exists since Isabelle2016-1, see the respective section ``Prover IDE -- Isabelle/Scala/jEdit'' in
the NEWS.)\<close>

subsection \<open>Lexing and Parsing Obfuscated Sources\<close>

text \<open>Another lexer/parser - stress test: parsing an obfuscated C source.\<close>

C \<comment> \<open>Example of obfuscated code \<^url>\<open>https://www.ioccc.org/2018/endoh1/prog.c\<close>\<close> \<open>
        #define/*__Int3rn^ti[]n/l_()I3fusc^t3|]_C_C<>I7E_C[]nt3st__*/L/*__MMXVIII__*/for
    #include/*!"'()*+,-./12357:;<=>?CEFGHIJKLMNSTUVWXYZ[]^_`cfhijklmnrstuvwxyz{|}*/<stdio.h>
  char*r,F[1<<21]="~T/}3(|+G{>/zUhy;Jx+5wG<v>>u55t.?sIZrC]n.;m+:l+Hk]WjNJi/Sh+2f1>c2H`)(_2(^L\
 -]=([1/Z<2Y7/X12W:.VFFU1,T77S+;N?;M/>L..K1+JCCI<<H:(G*5F--E11C=5?.(>+(=3)Z-;*(:*.Y/5(-=)2*-U,\
/+-?5'(,+++***''EE>T,215IEUF:N`2`:?GK;+^`+?>)5?>U>_)5GxG).2K.2};}_235(]:5,S7E1(vTSS,-SSTvU(<-HG\
-2E2/2L2/EE->E:?EE,2XMMMM1Hy`)5rHK;+.T+?[n2/_2{LKN2/_|cK2+.2`;}:?{KL57?|cK:2{NrHKtMMMK2nrH;rH[n"
"CkM_E21-E,-1->E(_:mSE/LhLE/mm:2Ul;2M>,2KW-+.-u).5Lm?fM`2`2nZXjj?[n<YcK?2}yC}H[^7N7LX^7N7UN</:-\
ZWXI<^I2K?>T+?KH~-?f<;G_x2;;2XT7LXIuuVF2X(G(GVV-:-:KjJ]HKLyN7UjJ3.WXjNI2KN<l|cKt2~[IsHfI2w{[<VV"
"GIfZG>x#&#&&$#$;ZXIc###$&$$#>7[LMv{&&&&#&##L,l2TY.&$#$#&&$,(iiii,#&&&#$#$?TY2.$#$1(x###;2EE[t,\
SSEz.SW-k,T&&jC?E-.$##      &#&57+$$#      &&&W1-&$$7W  -J$#$kEN&#&      $##C^+$##W,h###n/+L2YE"
"2nJk/H;YNs#$[,:TU(#$   ,:   &&~H>&#   Y;   &&G_x&#2;   ,mT&$YE-#&   5G   $#VVF$#&zNs$$&Ej]HELy\
CN/U^Jk71<(#&:G7E+^&#  l|?1  $$Y.2$$  7lzs  WzZw>&$E    -<V-wE(2$$  G>x;  2zsW/$$#HKt&$$v>+t1(>"
"7>S7S,;TT,&$;S7S>7&#>E_::U  $$'",op  ,*G=  F,*I=957+F  ;int*t,k,O,  i,   j,T[+060<<+020];int M(
int m,int nop){;;;return+   m%(0+nop  );;}  int*tOo,w,  h,z,W;void(C)  (int n){n=putchar(n);}int
f,c,H=11,Y=64<<2,Z,pq,X   ;void(E/*d  */)(  int/*RP*/n  ){L(Z=k+00;  Z;  Z/=+2+000)G[000]=*G*!!f
|M(n,2)<<f,pq=2,f=+06   <f?++pq,++pq  ,G++  ,z:f+001,n  /=2;;}void  (V)(  int/*opqrstabd*/n){C(n
%Y);;C(n/Y+00);;}void  J(){L(pq--,pq   =j   =O=-1+0;++  j<240;I[6+   (h   +6+j/12/2*2+M(j/2,2))*
W+M(j/2/2,+06)*2+w*014      +00+M(00+      000+j,002      +00)]=000      +00+k)k=M(G[j/2/2+(*r-+
32)**"<nopqabdeg"],/*4649&96#*/3);/*&oaogoqo*/;}/*xD%P$Q#Rq*/int/*dbqpdbqpxyzzyboo3570OQ*/main()
{L(X=Y-1;i<21*3;i++,I++)L(r=G,G+=2;*G++;)*G>=13*3?*G-*r?*I++=*G:(*I++=r[1],*I++=r[2]):1;L(j=12,r
=I;(*I=i=getchar())>-1;I++)i-7-3?I-=i<32||127<=i,j+=12:(H+=17+3,W=W<j?j:W,j=12);L(;*r>-1;r++)*r-
7-3?J(),w++:(w=z,h+=17+3);C(71);C(73);V('*'*'1'*7);C(57);C(32*3+1);V(W);V(H);C(122*2);L(V(i=z);i
<32*3;)C(i++/3*X/31);C(33);C(X);C(11);L(G="SJYXHFUJ735";*G;)C(*G++-5);C(3);V(1);L(V(j=z);j<21*3;
 j++){k=257;V(63777);V(k<<2);V(M(j,32)?11:511);V(z);C(22*2);V(i=f=z);V(z);V(W);V(H);V(1<<11);r=
  G=I+W*H;L(t=T;i<1<<21;i++)T[i]=i<Y?i:-1;E(Y);L(i=-1;++i<W*H;t=T+Z*Y+Y)c=I[i]?I[i]*31-31:(31<
    j?j-31:31-j),Z=c[t[c]<z?E(Z),k<(1<<12)-2?t[c]=++k,T:T:t];E(Z);E(257);L(G++;k=G-r>X?X:G-r
        ,C(k),k;)L(;k--;C(*r++/*---#$%&04689@ABDOPQRabdegopq---*/));}C(53+6);return(z);}
\<close>

section \<open>Experiments with \<^dir>\<open>../../src_ext/parser_menhir\<close>\<close>

declare[[C_lexer_trace = false]]

subsection \<open>Expecting to succeed\<close>

C_file \<open>../../src_ext/parser_menhir/tests/aligned_struct_c18.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/argument_scope.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/atomic.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/atomic_parenthesis.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/bitfield_declaration_ambiguity.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/bitfield_declaration_ambiguity.ok.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/block_scope.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/c11-noreturn.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/c1x-alignas.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/char-literal-printing.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/c-namespace.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/control-scope.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/dangling_else.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/dangling_else_lookahead.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/dangling_else_lookahead.if.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/declaration_ambiguity.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/declarators.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/declarator_visibility.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/designator.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/enum.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/enum_constant_visibility.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/enum_shadows_typedef.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/enum-trick.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/expressions.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/function-decls.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/function_parameter_scope.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/function_parameter_scope_extends.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/if_scopes.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/local_scope.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/local_typedef.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/long-long-struct.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/loop_scopes.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/namespaces.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/no_local_scope.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/parameter_declaration_ambiguity.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/parameter_declaration_ambiguity.test.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/statements.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/struct-recursion.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/typedef_star.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/types.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/variable_star.c\<close>

subsection \<open>Expecting to fail\<close>

C_file \<open>../../src_ext/parser_menhir/tests/bitfield_declaration_ambiguity.fail.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/dangling_else_misleading.fail.c\<close>\<close>

subsection \<open>Miscellaneous\<close>

\<^cancel>\<open>C_file \<open>../../src_ext/l4v/generated/spec/cspec/c/build/ARM/kernel_all.c_pp\<close>\<close>

section \<open>Experiments with \<^dir>\<open>../../src_ext/l4v/src/tools/c-parser/testfiles\<close>\<close>

C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/analsignedoverflow.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/anonymous_block_locals.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/array_of_ptr.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/arrays.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/asm.c\<close>\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/automatic_modifies.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/bar.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/basic_char.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/bigstruct.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/bitfield.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/breakcontinue.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/bug20060707.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/bug_mvt20110302.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/bugzilla180.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/bugzilla181.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/bugzilla182.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/bugzilla213.c\<close>\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/builtins.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/charlit.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/dc_20081211.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/dc_embbug.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/decl_only.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/dont_translate.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/dupthms.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/emptystmt.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/extern_builtin.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/extern_dups.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/factorial.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/fncall.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/fnptr.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/gcc_attribs.c\<close>\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/ghoststate2.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/globals_fn.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/globals_in_record.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/globinits.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/globsall_addressed.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/guard_while.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/hard_struct.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/hexliteral.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/initialised_decls.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/inner_fncalls.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/int_promotion.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/isa2014.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver039.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver092.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver105.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver110.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver150.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver224.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver253.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver254.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jira ver307.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver310.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver313.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver315.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver332.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver336.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver337.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver344.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver345.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver384.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver400.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver422.c\<close>\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver426.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver429.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver432.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver434.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver439.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver440.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver443a.c\<close>\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver443.c\<close>\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver456.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver464.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver473.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver54.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/jiraver550.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/kmalloc.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/list_reverse.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/list_reverse_norm.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/locvarfncall.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/longlong.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/many_local_vars.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/modifies_assumptions.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/multi_deref.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/multidim_arrays.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/mutrec_modifies.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_addr.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_auxupd.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_c99block.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_complit.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_dowhile.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_enum.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_fncall.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_forloop.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_include.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_prepost.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_protos.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_retfncall.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_simple_struct.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_sizeof.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_someops.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_spec.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_struct_array.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_struct.c\<close>\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_switch.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_switch_failures.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_typecast.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/parse_voidfn.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/phantom_mstate.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/postfixOps.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/protoparamshadow.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/ptr_auxupd.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/ptr_diff.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/ptr_globals.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/ptr_locals.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/ptr_modifies.c\<close>\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/ptr_umm.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/really_simple.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/relspec.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/retprefix.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/selection_sort.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/shortcircuit.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/signed_div.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/signedoverflow.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/simple_annotated_fn.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/simple_constexpr_sizeof.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/simple_fn.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/simple_globals.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/simple_locals.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/sizeof_typedef.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/spec_annotated_fn.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/spec_annotated_voidfn.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/struct_globals.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/struct_locals.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/struct_ptr_fn.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/struct_ptr_globals.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/swap.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/switch_unsigned_signed.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/test_include.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/test_shifts.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/test_typedef.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/ummbug20100217.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/untouched_globals.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/variable_munge.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/varinit.c\<close>
C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/void_ptr_init.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/l4v/src/tools/c-parser/testfiles/volatile_asm.c\<close>\<close>

end
