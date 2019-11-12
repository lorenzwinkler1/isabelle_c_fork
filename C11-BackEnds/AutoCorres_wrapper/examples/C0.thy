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

section \<open>Experiments with \<^dir>\<open>../../../l4v/src/tools/c-parser/testfiles\<close>\<close>

install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/analsignedoverflow.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/anonymous_block_locals.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/array_of_ptr.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/arrays.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/asm.c\<close> \<comment> \<open>asm not implemented\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/automatic_modifies.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/bar.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/basic_char.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/bigstruct.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/bitfield.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/breakcontinue.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/bug20060707.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/bug_mvt20110302.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/bugzilla180.c\<close>\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/bugzilla181.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/bugzilla182.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/bugzilla213.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/builtins.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/charlit.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/dc_20081211.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/dc_embbug.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/decl_only.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/dont_translate.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/dupthms.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/emptystmt.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/extern_builtin.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/extern_dups.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/factorial.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/fncall.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/fnptr.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/gcc_attribs.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/ghoststate2.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/globals_fn.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/globals_in_record.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/globinits.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/globsall_addressed.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/guard_while.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/hard_struct.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/hexliteral.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/initialised_decls.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/inner_fncalls.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/int_promotion.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/isa2014.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver039.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver092.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver105.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver110.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver150.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver224.c\<close>\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver253.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver254.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jira ver307.c\<close>\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver310.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver313.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver315.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver332.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver336.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver337.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver344.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver345.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver384.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver400.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver422.c\<close> \<comment> \<open>specific parsing format of ML_parser vs HS_parser\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver426.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver429.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver432.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver434.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver439.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver440.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver443a.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver443.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver456.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver464.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver473.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver54.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/jiraver550.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/kmalloc.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/list_reverse.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/list_reverse_norm.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/locvarfncall.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/longlong.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/many_local_vars.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/modifies_assumptions.c\<close> \<comment> \<open>sorted order of MODIFIES\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/multi_deref.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/multidim_arrays.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/mutrec_modifies.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_addr.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_auxupd.c\<close>\<close> \<comment> \<open>error ML_parser\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_c99block.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_complit.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_dowhile.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_enum.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_fncall.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_forloop.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_include.c\<close>\<close> \<comment> \<open>error cpp\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_prepost.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_protos.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_retfncall.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_simple_struct.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_sizeof.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_someops.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_spec.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_struct_array.c\<close>\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_struct.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_switch.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_switch_failures.c\<close>\<close> \<comment> \<open>error ML_parser\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_typecast.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/parse_voidfn.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/phantom_mstate.c\<close> \<comment> \<open>sorted order of MODIFIES\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/postfixOps.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/protoparamshadow.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/ptr_auxupd.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/ptr_diff.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/ptr_globals.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/ptr_locals.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/ptr_modifies.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/ptr_umm.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/really_simple.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/relspec.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/retprefix.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/selection_sort.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/shortcircuit.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/signed_div.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/signedoverflow.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/simple_annotated_fn.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/simple_constexpr_sizeof.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/simple_fn.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/simple_globals.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/simple_locals.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/sizeof_typedef.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/spec_annotated_fn.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/spec_annotated_voidfn.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/struct_globals.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/struct_locals.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/struct_ptr_fn.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/struct_ptr_globals.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/swap.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/switch_unsigned_signed.c\<close>
\<^cancel>\<open>install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/test_include.c\<close>\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/test_shifts.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/test_typedef.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/ummbug20100217.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/untouched_globals.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/variable_munge.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/varinit.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/void_ptr_init.c\<close>
install_C_file no_C11_parsing no_cpp parse_then_stop \<open>../../../l4v/src/tools/c-parser/testfiles/volatile_asm.c\<close>

end
