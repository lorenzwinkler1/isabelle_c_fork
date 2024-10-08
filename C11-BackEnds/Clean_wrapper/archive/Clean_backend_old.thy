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

chapter \<open>Appendix: Miscellaneous (Example Preparation)\<close>

theory Clean_backend_old
  imports Isabelle_C_Clean.Generator_dynamic_sequential
begin

text\<open>A Mockup Logical Context for the \<^file>\<open>../examples/Prime.thy\<close> - example. 
Will disappear in the final distribution. \<close>

section \<open>\<close>

consts "UINT_MAX" :: "nat"

section \<open>\<close>

no_syntax "_C" :: \<open>cartouche_position \<Rightarrow> _\<close> ("\<^C> _")
syntax "_C'" :: \<open>cartouche_position \<Rightarrow> _\<close> ("\<^C> _")

setup \<open>C_Module.C_Term.map_expression (fn _ => fn _ => fn _ => @{term "1 :: nat"})\<close>

parse_translation \<open>
C_Module.C_Term'.parse_translation [ (\<^syntax_const>\<open>_C'\<close>, SOME C_Module.C_Term.tok_expression) ]
\<close>

end
