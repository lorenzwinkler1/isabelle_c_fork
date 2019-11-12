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
  imports CParser.CTranslation
begin

section \<open>Experiments with \<^dir>\<open>../../../parser_menhir\<close>\<close>

subsection \<open>Expecting to succeed\<close>

\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/aligned_struct_c18.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/argument_scope.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/atomic.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/atomic_parenthesis.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/bitfield_declaration_ambiguity.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/bitfield_declaration_ambiguity.ok.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/block_scope.c\<close>\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/c11-noreturn.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/c1x-alignas.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/char-literal-printing.c\<close>\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/c-namespace.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/control-scope.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/dangling_else.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/dangling_else_lookahead.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/dangling_else_lookahead.if.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/declaration_ambiguity.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/declarators.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/declarator_visibility.c\<close>\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/designator.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/enum.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/enum_constant_visibility.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/enum_shadows_typedef.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/enum-trick.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/expressions.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/function-decls.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/function_parameter_scope.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/function_parameter_scope_extends.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/if_scopes.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/local_scope.c\<close>\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/local_typedef.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/long-long-struct.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/loop_scopes.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/namespaces.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/no_local_scope.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/parameter_declaration_ambiguity.c\<close>\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/parameter_declaration_ambiguity.test.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/statements.c\<close>\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/struct-recursion.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/typedef_star.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/types.c\<close>\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/variable_star.c\<close>

subsection \<open>Expecting to fail\<close>

\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/bitfield_declaration_ambiguity.fail.c\<close>\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../parser_menhir/tests/dangling_else_misleading.fail.c\<close>\<close>

end
