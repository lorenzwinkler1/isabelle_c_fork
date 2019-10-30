(******************************************************************************
 * Isabelle/C/Clean
 *
 * Authors: Frederic Tuong, Burkhart Wolff
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

chapter\<open>The Isabelle/C/Clean Demonstrator\<close>

theory Clean_Wrapper
  imports Clean.Clean
          "compiler/Generator_dynamic_sequential"
begin

text \<open>
Isabelle/C~\cite{TuongWolff19} is a C front-end for Isabelle/PIDE providing generic support for C
parsing, editing, and highlighting. Isabelle/C also provides a generic interface for semantic
interpretations of C11 programs and program fragments. In particular, Isabelle/C also offers the
generic framework to define \emph{annotation commands} and \emph{C antiquotations} that can be
custumized to a specific semantic back-end.

The purpose of this session is to provide a substantial show-case demonstrating how this can be done
with Isabelle/C, \ie{} how it can actually be instantiated with a concrete semantic interpretation
(called: semantic back-end theory in this context). For this purpose, we chose the Clean language
which is available via the Isabelle AFP~\cite{journals/afp/TuongW19}.

We show how the translation process from C11-AST's via a C99-AST and its library can be done for
similar semantic back-ends such as AutoCorres (see @{url
  "https://gitlri.lri.fr/ftuong/isabelle_c/tree/C/C11-BackEnds"}) or IMP2.

Isabelle/C as a framework offers:
\<^enum> a C11 AST definition in SML
\<^enum> a C99 AST definition as well as an AST support library in SML
\<^enum> a translator from C11 to C99 AST in SML
\<^enum> an c-environment data-structure managed by Isabelle/C in SML
\<^enum> a generic interface to define \<^emph>\<open>annotation commands\<close>, \ie{} specific pragmas
  of the form \<^verbatim>\<open>/*@ <command> <arg> ... <arg> */\<close> which were executed in the
  logical and C-AST context. 
\<close>

text \<open> The task of constructing a wrapper, \ie{} an instantiation of Isabelle/C with a
specific semantic back-end can be decomposed in essentially three tasks:
\<^enum> Constructing the translation of C11-AST into the terms in the terms provided by
  the Isabelle structure @{ML_structure "Term"}; an intermediate solution is to generate
  string's and to let them parse by the Isabelle parsers. 
\<^enum> Constructing a semantics for the usual C pragmas \<^verbatim>\<open>#define ...\<close>,
  \<^verbatim>\<open>#include ...\<close> and friends; an alternative is to consider only files
  expanded by the C preprocessor. (This solution is disadvised since cpp's tend to be very platform
  specific and expansions might lead to very lengthy sources without modularization
  information. Wasting structural information is a capital sin in an interactive environment.)
\<^enum> Defining control-attributes suitable for the wrapper.
\<^enum> Defining semantic annotation commands yielding specific support for automation.
\<close>

text\<open>Such semantic annotation commands may yield support for:
\<^enum> Classics in verification:
  pre- and post-conditions, rely-guarantees, flags for arithmetic interpretation, 
  assertions, assumptions, invariants. 
\<^enum> Classics in program-based tests such as:
  unfolding-depths, coverage criteria to be applied, hints feasibility-checking.
\<^enum> Isabelle inline proofs establishing properties of local C elements or configuration data
  (Isabelle/C supports proof-carrying code in a sense, see @{cite "TuongWolff19"} page 9).
\<^enum> Pragmas for code-generation.
\<^enum> Ontological information used to assure tracability of requirements or tests down to
  specific spots in the code (cf. @{cite "brucker.wolff:isadof-design-impl:2019"}). 
\<close>

text\<open>In the sequel, we will present some aspects of the translation, the handling of pragmas
and semantic annotation commands giving specific support for Clean.\<close>

generation_syntax [ deep [in self], shallow ]
end
