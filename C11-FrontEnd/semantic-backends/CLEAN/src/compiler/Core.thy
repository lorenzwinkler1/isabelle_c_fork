(******************************************************************************
 * Citadelle
 *
 * Copyright (c) 2011-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
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

theory Core
  imports Meta_C
begin
\<comment> \<open>Derived from: \<^file>\<open>../../../../../Citadelle/src/compiler/Core.thy\<close>\<close>

ML\<open>
structure CLEAN_Core =
struct
open C_Ast

fun compile ast env_lang =
  IsarInstall.install_C_file0 ast env_lang
  |> rev
  |> map
     (fn function =>
       [ META_semi_theories (Theories_one (Theory_definition (Definitiona (Term_rewrite (Term_basic [SS_base (ST ("pop_" ^ #fname function))], SS_base (ST "\<equiv>"), Term_basic [SS_base (ST "()")])))))
       , META_semi_theories (Theories_one (Theory_definition (Definitiona (Term_rewrite (Term_basic [SS_base (ST ("push_" ^ #fname function))], SS_base (ST "\<equiv>"), Term_basic [SS_base (ST "()")])))))
       , META_semi_theories (Theories_one (Theory_definition (Definitiona (Term_rewrite (Term_basic [SS_base (ST ("core_" ^ #fname function))], SS_base (ST "\<equiv>"), Term_basic [SS_base (ST "()")])))))])
  |> concat
end
\<close>

end
