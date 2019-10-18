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

theory README imports Main begin

section \<open>Global Structure of the Isabelle/C Project\<close>

text \<open>
The Isabelle/C project consists of several components, where some of them are published in the
Isabelle AFP, or represent AFP submissions.

\<^item> \<^dir>\<open>C11-FrontEnd\<close> (AFP)
\<^item> \<^dir>\<open>C18-FrontEnd\<close>
\<^item> \<^dir>\<open>C11-BackEnds\<close>
  \<^item> \<^dir>\<open>C11-BackEnds/Clean\<close>: (AFP) Clean Library
  \<^item> \<^dir>\<open>C11-BackEnds/Clean_wrapper\<close>: (AFP) adapter to \<^dir>\<open>C11-FrontEnd\<close>
  \<^item> \<^dir>\<open>C11-BackEnds/AutoCorres\<close>: slightly modified version of AutoCorres library
  \<^item> \<^dir>\<open>C11-BackEnds/AutoCorres_wrapper\<close>: adapter to \<^dir>\<open>C11-FrontEnd\<close>
\<^item> \<^dir>\<open>Citadelle\<close>: model-based framework generating the grammars and the AST of \<^dir>\<open>C11-FrontEnd\<close>
\<close>

section \<open>Isabelle/C\<close>

text \<open>
Isabelle/C contains a C99/C11/C18 front-end support for Isabelle. The front-end is actually composed
of two possibly interchangeable parsers (from two different projects):

\<^item> \<^dir>\<open>C11-FrontEnd\<close>: \<^url>\<open>https://hackage.haskell.org/package/language-c\<close>
\<^item> \<^dir>\<open>C18-FrontEnd\<close>: \<^url>\<open>https://github.com/jhjourdan/C11parser\<close>

Thus, one can select which parser(s) are better suitable to be enabled in front of a piece of C
code.

Isabelle/C requires Isabelle2019. For a first start, the following C examples or entry-points of
documentation can be executed:

\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>C11-FrontEnd\<close> \<^file>\<open>C11-FrontEnd/examples/C1.thy\<close>
\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>C11-FrontEnd\<close> \<^file>\<open>C11-FrontEnd/examples/C2.thy\<close>
\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>C18-FrontEnd\<close> \<^file>\<open>C18-FrontEnd/examples/C0.thy\<close>
\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>C11-FrontEnd\<close> \<^file>\<open>C11-FrontEnd/C_Appendices.thy\<close>
\<close>

text \<open>
Examples in \<^dir>\<open>C11-BackEnds\<close> require to change the initial directory provided to
\<^verbatim>\<open>isabelle jedit -d\<close>, because they depend on respective semantic back-ends.
\<close>

subsection \<open>Isabelle/C/Clean\<close>

text \<open>
\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^file>\<open>C11-BackEnds/Clean_wrapper/examples/Prime.thy\<close>
\<close>

subsection \<open>Isabelle/C/AutoCorres\<close>

text \<open>
Before using the \<^dir>\<open>C11-BackEnds/AutoCorres_wrapper\<close> back-end, the shell variable
\<open>L4V_ARCH\<close> must be additionally set to \<open>ARM\<close>.

\<^item> \<^verbatim>\<open>export L4V_ARCH = ARM\<close> \<^emph>\<open>\<open>#\<close> the same effect can be permanently made in \<^file>\<open>$ISABELLE_HOME_USER/etc/settings\<close>\<close>
\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l CParser\<close> \<^file>\<open>C11-BackEnds/AutoCorres_wrapper/examples/TestSEL4.thy\<close>
\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l AutoCorres\<close> \<^file>\<open>C11-BackEnds/AutoCorres_wrapper/examples/IsPrime_integrated.thy\<close>
\<close>

text \<open>
For the case of \<^dir>\<open>C11-BackEnds/AutoCorres_wrapper\<close>, we were used to see a
sub-window \<open>Bad session structure\<close> appearing just after starting Isabelle. This is
because the back-end normally requires to execute some initialization script (for example using
\<^file>\<open>l4v/src/run_tests\<close>) to generate specific Isabelle theory files. Instead, as
possible workaround, we have introduced by hand in \<^dir>\<open>l4v/src\<close> several symbolic
links pointing to the missing files, making the sub-window not supposed to appear
anymore. Nevertheless, if this ever happens again, the sub-window can be ignored by clicking on
\<open>OK\<close>.

Additionally, \<^file>\<open>l4v/src/run_tests\<close> can be executed in
\<^dir>\<open>l4v/src\<close>, and interrupted once the success of \<open>CBaseRefine\<close>
obtained. Then, to test the interactive version of AutoCorres, it would suffice to run the following
command:
\<^item> \<^verbatim>\<open>isabelle build -d\<close> \<^dir>\<open>l4v/src\<close> \<^verbatim>\<open>-b -v AutoCorresSEL4\<close>
\<close>

text \<open>
Note: The version of the \<open>l4v\<close> (\<^url>\<open>https://github.com/seL4/l4v/\<close>)
project used is \<open>e3352826893db4d00fc402fad2a0125307ebe45e\<close>.
\<close>

subsection \<open>Isabelle/C/README\<close>

text \<open>
\<^file>\<open>README.md\<close> is automatically generated from \<^file>\<open>README.thy\<close>
using:
\<^item> \<^verbatim>\<open>isabelle env\<close> \<^file>\<open>./README.sh\<close>
\<close>

section \<open>Authors\<close>

text \<open>
\<^item> Frédéric Tuong (\<^url>\<open>https://www.lri.fr/~ftuong\<close>)
\<^item> Burkhart Wolff (\<^url>\<open>https://www.lri.fr/~wolff\<close>)
\<close>

section \<open>License\<close>

text \<open>
Isabelle/C is licensed under a 3-clause BSD-style license (where certain files are in the HPND
license compatible with the 3-clause BSD).

In more details:
\<^item> The generated files \<^file>\<open>C11-FrontEnd/generated/c_ast.ML\<close> and
  \<^file>\<open>C11-FrontEnd/generated/c_grammar_fun.grm\<close> are mixing several source code of
    different projects:
  \<^item> In 3-clause BSD: the part representing the Haskell Language.C library.  
  \<^item> In 2-clause BSD: the C99 AST in HOL (before reflection to SML) adapted from the original
    one in the L4.verified project.
  \<^item> In 3-clause BSD: the HOL translation C11 to C99 from the Securify project.    
  \<^item> In 3-clause BSD: any other binding and translations of meta-models from the Citadelle
    project.
\<^item> In 3-clause BSD: the two combined generators generating
  \<^file>\<open>C11-FrontEnd/generated/c_ast.ML\<close> based on some modified version of Haskabelle
  and Citadelle.
\<^item> In 3-clause BSD: the Happy modified generator generating
  \<^file>\<open>C11-FrontEnd/generated/c_grammar_fun.grm\<close>
\<^item> In HPND: the ML-Yacc modified generator generating the two
  \<^file>\<open>C11-FrontEnd/generated/c_grammar_fun.grm.sig\<close> and
  \<^file>\<open>C11-FrontEnd/generated/c_grammar_fun.grm.sml\<close> (i.e., the ML-Yacc version of
  MLton).
\<^item> In HPND: the modified grammar library of ML-Yacc loaded in
  \<^file>\<open>C11-FrontEnd/src/C_Parser_Language.thy\<close>.
\<^item> In 3-clause BSD: the remaining files in \<^dir>\<open>C11-FrontEnd/src\<close> constituting
  Isabelle/C core implementation.
\<^item> Most examples in \<^dir>\<open>C11-FrontEnd/examples\<close> are in 3-clause BSD, some are
  used for quotation purposes to test the Isabelle/C lexer (hyperlinks around each example detail
  their provenance).
\<close>

end
