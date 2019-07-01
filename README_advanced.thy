(******************************************************************************
 * Generation of Language.C Grammar with ML Interface Binding
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

theory README_advanced imports Main begin

section \<open>Isabelle/C\<close>

text \<open>
Isabelle/C contains a C11 front-end support for Isabelle.

The code requires Isabelle2019. For a first start, the following C examples or entry-points of
documentation can be executed:

\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>C11-FrontEnd\<close> \<^file>\<open>C11-FrontEnd/examples/C1.thy\<close>
\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>C11-FrontEnd\<close> \<^file>\<open>C11-FrontEnd/examples/C2.thy\<close>
\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>C11-FrontEnd\<close> \<^file>\<open>C11-FrontEnd/examples/C3.thy\<close>
\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>C11-FrontEnd\<close> \<^file>\<open>C11-FrontEnd/C_Appendices.thy\<close>
\<close>

text \<open>
Certain examples in \<^dir>\<open>C11-FrontEnd\<close> actually require to change the initial
directory provided to \<^verbatim>\<open>isabelle jedit -d\<close>, because they might depend on
other projects (such as \<open>l4v\<close>):

\<^item> \<^verbatim>\<open>export L4V_ARCH = ARM\<close> \<^emph>\<open>\<open>#\<close> the same effect can be made in \<^file>\<open>~/.isabelle/etc/settings\<close>\<close>
\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l CParser\<close> \<^file>\<open>C11-FrontEnd/semantic-backends/AutoCorres/examples/TestSEL4.thy\<close>
\<^item> \<^verbatim>\<open>isabelle jedit -d\<close> \<^dir>\<open>.\<close> \<^verbatim>\<open>-l AutoCorres\<close> \<^file>\<open>C11-FrontEnd/semantic-backends/AutoCorres/examples/IsPrime_integrated.thy\<close>
\<close>

text \<open>
For the last examples, we were used to see a sub-window \<open>Bad session structure\<close>
appearing just after starting Isabelle. Nevertheless, if this ever happens again, the sub-window can
be ignored by clicking on \<open>OK\<close>.

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

subsection \<open>Authors\<close>

text \<open>
\<^item> Frédéric Tuong (\<^url>\<open>https://www.lri.fr/~ftuong\<close>)
\<^item> Burkhart Wolff (\<^url>\<open>https://www.lri.fr/~wolff\<close>)
\<close>

subsection \<open>License\<close>

text \<open>
This project is licensed under a 3-clause BSD-style license.
\<close>

end