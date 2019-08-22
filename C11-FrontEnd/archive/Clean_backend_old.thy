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
  imports "../../C11-BackEnds/Clean/src/compiler/Generator_dynamic_sequential"
begin
no_notation unit_SE ("(result _)" 8)
definition "UINT_MAX = 0"
definition "n = 0"
definition "result = 0"

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

val scan_ident = Scan.one (C_Token.is_kind Token.Ident) >> (fn tok => (C_Token.content_of tok, C_Token.pos_of tok))
val scan_brack_star = C_Parse.position (C_Parse.$$$ "[") -- C_Parse.star -- C_Parse.range (C_Parse.$$$ "]")
                      >> (fn (((s1, pos1), s2), (s3, (_, pos3))) => (s1 ^ s2 ^ s3, Position.range_position (pos1, pos3)))
val scan_opt_colon = Scan.option (C_Parse.$$$ ":")
val scan_colon = C_Parse.$$$ ":" >> SOME
val show = tap (fn s => Syntax.read_term @{context} s)

val opt_modes =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

fun toplevel _ = C_Inner_Toplevel.keep''
\<close>


ML \<open>fun command keyword f =
  C_Inner_Syntax.command0
    (toplevel f o C_Inner_Isar_Cmd.print_term)
    (C_Token.syntax' (opt_modes -- Parse.term))
    C_Transition.Bottom_up
    keyword\<close>
setup \<open>command ("pre\<^sub>C\<^sub>L\<^sub>E\<^sub>A\<^sub>N", \<^here>) Spec
    #> command ("post\<^sub>C\<^sub>L\<^sub>E\<^sub>A\<^sub>N", \<^here>) End_spec
    #> command ("inv\<^sub>C\<^sub>L\<^sub>E\<^sub>A\<^sub>N", \<^here>) Invariant\<close>


ML\<open>
val lexer_trace = Attrib.setup_config_bool @{binding Clean_on} (K false);
\<close>
end
