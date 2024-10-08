(******************************************************************************
 * Isabelle/C
 *
 * Authors: Frédéric Tuong, Burkhart Wolff
 *
 * Copyright (c) 2018-2022 Université Paris-Saclay, Univ. Paris-Sud, France
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
  \<^item> \<^dir>\<open>C11-BackEnds/Clean_wrapper\<close>: adapter to \<^dir>\<open>C11-FrontEnd\<close>
  \<^item> \<^dir>\<open>C11-BackEnds/AutoCorres\<close>: slightly modified version of AutoCorres library.   
  \<^item> \<^dir>\<open>C11-BackEnds/AutoCorres_wrapper\<close>: adapter to \<^dir>\<open>C11-FrontEnd\<close>
\<^item> \<^dir>\<open>Citadelle\<close>: model-based framework generating the grammars and the AST of \<^dir>\<open>C11-FrontEnd\<close>

Public releases of this bundle of Isabelle/C, Isabelle/C/Clean and 
Isabelle/C/AutoCorres were distributed via the ZENODO website 
\<^url>\<open>https://zenodo.org/record/6827097#.YtEzROxBxUM\<close>, the read access to our development 
repository is public as well \<^url>\<open>https://gitlab.lisn.upsaclay.fr/burkhart.wolff/Isabelle_C\<close>.

\<close>

section \<open>Isabelle/C\<close>

text \<open>
Isabelle/C contains a C99/C11/C18 front-end support for Isabelle. The front-end is actually composed
of two possibly interchangeable parsers (from two different projects):

\<^item> \<^dir>\<open>C11-FrontEnd\<close>: \<^url>\<open>https://hackage.haskell.org/package/language-c\<close>
\<^item> \<^dir>\<open>C18-FrontEnd\<close>: \<^url>\<open>https://github.com/jhjourdan/C11parser\<close>

At present, the recommended and default version is C11.

Isabelle/C requires Isabelle2021-1. (This is following the latest version currently supported by
AutoCorres.)
\<close>

section \<open>Getting started (quickstart for users)\<close>

text \<open>
In the sequel, with \<^verbatim>\<open>isabelle\<close> we refer to your local Isabelle2021-1
installation, and assume your current working directory is at the root of \<^verbatim>\<open>Isabelle_C\<close>
(i.e. the directory that contains this \<^file>\<open>./README.md\<close> file).

It is recommended to set
  \<^verbatim>\<open>export L4V_ARCH=ARM\<close>
before most configurations of  \<^verbatim>\<open>Isabelle_C\<close>; this feature is relevant for \<^verbatim>\<open>AutoCorres\<close>
configurations can be made effective permanently by appropriate \<^verbatim>\<open>$ISABELLE_HOME_USER/etc/settings\<close>.


   \<^item> Building Isabelle_C : 
     \<^verbatim>\<open>isabelle build -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-b Isabelle_C\<close>
   \<^item> Building Isabelle_C_AutoCorres : 
     \<^verbatim>\<open>isabelle build -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-b Isabelle_C_AutoCorres\<close>
   \<^item> Running an example: 
     \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l Isabelle_C_AutoCorres\<close> \<^file>\<open>C11-BackEnds/AutoCorres_wrapper/examples/IsPrime_linear_CCT.thy\<close>
\<close>

section \<open>Getting started (for developers)\<close>

text \<open>
A first installation step of Isabelle/C without back-ends is:

\<^item> \<^verbatim>\<open>isabelle build -D\<close> \<^dir>\<open>C11-FrontEnd\<close>

which should work out of the box.
\<close>

(* WAS (and does not work any longer: )
\<^item> \<^verbatim>\<open>isabelle build -D\<close> \<^dir>\<open>C11-FrontEnd\<close> \<^verbatim>\<open>-D\<close> \<^dir>\<open>C18-FrontEnd\<close>   

*)

text \<open>
Alternatively, the full build of the \<^emph>\<open>developer repository\<close> of Isabelle/C with
all back-ends enabled is performed with:

\<^item> \<^verbatim>\<open>isabelle build -b -v -d\<close> \<^dir>\<open>.\<close> 
\<^verbatim>\<open>\<^verbatim>\<open>isabelle build -b -v -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>Isabelle_C Isabelle_C_examples Isabelle_C_document Clean_document Isabelle_C_AutoCorres_document Isabelle_C_Clean_document  Isabelle_C_archive
Isabelle_C_README\<close>\<close>
\<close>

(* Was : (DOES NOT WORK ANY LONGER: )
\<^item> \<^verbatim>\<open>isabelle build -b -v -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>Isabelle_C_all Isabelle_C_Advance_examples Clean_document Isabelle_C_AutoCorres_document Isabelle_C_Clean_document Isabelle_C_README Isabelle_C_archive\<close>

*)

text \<open>
The following C examples or entry-points of documentation can be executed:

   \<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l Isabelle_C\<close> \<^file>\<open>C11-FrontEnd/examples/C0.thy\<close>
   \<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l Isabelle_C\<close> \<^file>\<open>C11-FrontEnd/examples/C1.thy\<close>
   \<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l Isabelle_C\<close> \<^file>\<open>C11-FrontEnd/examples/C2.thy\<close>
   \<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l Isabelle_C\<close> \<^file>\<open>C11-FrontEnd/examples/C3.thy\<close>
   \<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l Isabelle_C\<close> \<^file>\<open>C11-FrontEnd/examples/C4.thy\<close>
   \<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l Isabelle_C\<close> \<^file>\<open>C11-FrontEnd/examples/C_paper.thy\<close>
   \<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l Isabelle_C\<close> \<^file>\<open>C11-FrontEnd/appendices/C_Appendices.thy\<close>
   \<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l Isabelle_C\<close> \<^file>\<open>C18-FrontEnd/examples/C0.thy\<close>

The option \<^verbatim>\<open>-l Isabelle_C\<close> can be omitted; it instructs Isabelle to use a
binary-built version of the \<^verbatim>\<open>Isabelle_C\<close> session. In case of omission,
Isabelle automatically loads all \<^verbatim>\<open>Isabelle_C\<close> sources, such that the user
might browse in there or modify any files.
\<close>

text \<open>
\<^item> The example \<^file>\<open>C11-FrontEnd/examples/C0.thy\<close> is basically used to
demonstrate the robustness and faithfulness of the C11 parser implementation.
\<^item> The example \<^file>\<open>C11-FrontEnd/examples/C1.thy\<close> shows examples for C_AST11 programming and
translation as well as C editing support in PIDE; 
it also contains coding-examples for C annotation commands without any semantics.
\<^item> The example \<^file>\<open>C11-FrontEnd/examples/C2.thy\<close> is a show-case for markup
generation and the use of bindings resulting from the static C environment.
\<^item> The example \<^file>\<open>C11-FrontEnd/examples/C3.thy\<close> is a show-case for markup
generation and and navigation in the C11 AST's via C-Antiquotations as well as 
serialization examples for C-Antiquotation execution.
\<^item> The example \<^file>\<open>C11-FrontEnd/examples/C4.thy\<close> is a show-case for a simplistic 
parse-and-store amd a CAS-oriented setup for C-Antiquotations.
\<^item> The example \<^file>\<open>C11-FrontEnd/appendices/C_Appendices.thy\<close> shows the use of
Isabelle/C documentation facilities.
\<^item> The example \<^file>\<open>C18-FrontEnd/examples/C0.thy\<close> is basically used to
demonstrate the faithfulness of the C18 parser implementation.
\<close>

text \<open>
The AFP version of Isabelle/C does not include semantic back-ends (these are distributed by other
AFP submissions or available via the web; see below). The structure of \<^dir>\<open>.\<close> has
been designed to create a directory \<^dir>\<open>C11-BackEnds\<close> into which back-ends can be
installed. The structure of \<^dir>\<open>.\<close> is actually similar as
\<^url>\<open>https://gitlab.lisn.upsaclay.fr/burkhart.wolff/Isabelle_C\<close>: see for example
\<^url>\<open>https://gitlab.lisn.upsaclay.fr/burkhart.wolff/Isabelle_C/-/tree/C/C11-BackEnds\<close> where several
back-ends can be copied and tried.
\<close>


subsection \<open>Isabelle/C/Clean\<close>

text \<open> Isabelle/C/Clean is under development and the release has the status: experimental.
A first installation step of Isabelle/C/Clean is:

\<^item> \<^verbatim>\<open>isabelle build -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-D\<close> \<^dir>\<open>C11-BackEnds/Clean_wrapper\<close>

which should work out of the box.
\<close>

text \<open>
\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^file>\<open>C11-BackEnds/Clean_wrapper/examples/Prime.thy\<close>
\<close>

subsection \<open>Isabelle/C/AutoCorres\<close>
text\<open>
The integration Isabelle/C/AutoCorres of l4v into Isabelle/C is based on 
revision \<^verbatim>\<open>e3352826893db4d00fc402fad2a0125307ebe45e\<close> in the 
seL4-project (cf.: \<^url>\<open>https://zenodo.org/record/1168016#.YtEm7OxByjg\<close>).
Note that the AutoCorres component is currently restricted to Linux-  and MacOS
platforms.

Before using the \<^dir>\<open>C11-BackEnds/AutoCorres_wrapper\<close> back-end, the shell variable
\<open>L4V_ARCH\<close> must be additionally set to \<open>ARM\<close>.

   \<^item> \<^verbatim>\<open>export L4V_ARCH=ARM\<close> \<^emph>\<open>\<open>#\<close> the same effect can be permanently made in \<^verbatim>\<open>$ISABELLE_HOME_USER/etc/settings\<close>\<close>
   \<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l CParser\<close> \<^file>\<open>C11-BackEnds/AutoCorres_wrapper/examples/TestSEL4.thy\<close>
   \<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l AutoCorres\<close> \<^file>\<open>C11-BackEnds/AutoCorres_wrapper/examples/IsPrime_linear_CCT.thy\<close>

For the case of \<^dir>\<open>C11-BackEnds/AutoCorres_wrapper\<close>, we were used to see a
sub-window \<open>Bad session structure\<close> appearing just after starting Isabelle. This is
because the back-end normally requires to execute some initialization script (for example using
\<^file>\<open>src_ext/l4v/src/run_tests\<close>) to generate specific Isabelle theory
files. Instead, as possible workaround, we have introduced by hand in
\<^dir>\<open>src_ext/l4v/src\<close> several symbolic links pointing to the missing files, making
the sub-window not supposed to appear anymore. Nevertheless, if this ever happens again, the
sub-window can be ignored by clicking on \<open>OK\<close>.

Additionally, \<^file>\<open>src_ext/l4v/src/run_tests\<close> can be executed in
\<^dir>\<open>src_ext/l4v/src\<close>, and interrupted once the success of
\<open>CBaseRefine\<close> obtained. Then, to test the interactive version of AutoCorres, it would
suffice to run the following command:
\<^item> \<^verbatim>\<open>isabelle build -d\<close> \<^dir>\<open>src_ext/l4v/src\<close> \<^verbatim>\<open>-b -v AutoCorresSEL4\<close>
\<close>

text \<open>
Note: The version of the \<open>l4v\<close> (\<^url>\<open>https://github.com/seL4/l4v/\<close>)
project used is \<open>e3352826893db4d00fc402fad2a0125307ebe45e\<close>.
\<close>

subsection \<open>Isabelle/C/README\<close>

text \<open>
\<^file>\<open>README.md\<close> is automatically generated from \<^file>\<open>README.thy\<close>
using:
\<^item> \<^verbatim>\<open>isabelle env\<close> \<^file>\<open>README.sh\<close>
\<close>

text \<open> Note that this shell-script requires the prior installation of
\<^verbatim>\<open>pandoc\<close> (\<^url>\<open>https://github.com/jgm/pandoc\<close>).
\<close>

section \<open>Authors\<close>

text \<open>
\<^item> Frédéric Tuong (\<^url>\<open>https://gitlab.lisn.upsaclay.fr/frederictuong/isabelle_contrib\<close>)
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
