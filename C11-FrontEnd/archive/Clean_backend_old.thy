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

theory Clean_backend_old
  imports Isabelle_C_Clean.Generator_dynamic_sequential
begin

no_notation unit_SE ("(result _)" 8)
definition "UINT_MAX = 0"

section \<open>User Defined Commands in the Semantic Verification Space\<close>

ML \<comment> \<open>\<^theory>\<open>Isabelle_C.C_Command\<close>\<close> \<open>
type text_range = Symbol_Pos.text * Position.T

datatype antiq_hol = Invariant of string (* term *)
                   | Fnspec of text_range (* ident *) * string (* term *)
                   | Relspec of string (* term *)
                   | Modifies of (bool (* true: [*] *) * text_range) list
                   | Dont_translate
                   | Auxupd of string (* term *)
                   | Ghostupd of string (* term *)
                   | Spec of string (* term *)
                   | End_spec of string (* term *)
                   | Calls of text_range list
                   | Owned_by of text_range

fun toplevel _ = C_Inner_Toplevel.keep''

fun bind scan _ ((stack1, (to_delay, stack2)), _) =
  C_Parse.range scan
  >> (fn (src, range) =>
      C_Transition.Parsing
        ( (stack1, stack2)
        , ( range
          , C_Transition.Bottom_up
          , Symtab.empty
          , to_delay
          , fn _ => fn context =>
              ML_Context.exec
                (tap (fn _ => Syntax.read_term (Context.proof_of context) (Token.inner_syntax_of src)))
                context)))

infix 3 >>>;
fun scan >>> f = bind scan f
\<close>

ML \<open>fun command keyword f =
  C_Annotation.command' keyword ""
    (C_Token.syntax' (Parse.token Parse.cartouche)
     >>> toplevel f)\<close>
setup \<open>command ("pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n", \<^here>) Spec
    #> command ("post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n", \<^here>) End_spec
    #> command ("inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n", \<^here>) Invariant\<close>

section \<open>\<close>

no_syntax "_C" :: \<open>cartouche_position \<Rightarrow> _\<close> ("\<^C> _")
syntax "_C'" :: \<open>cartouche_position \<Rightarrow> _\<close> ("\<^C> _")

setup \<open>C_Module.C_Term.map_expression (fn _ => fn _ => fn _ => @{term "1 :: nat"})\<close>

parse_translation \<open>
C_Module.C_Term'.parse_translation [ (\<^syntax_const>\<open>_C'\<close>, SOME C_Module.C_Term.tok_expression) ]
\<close>

end
