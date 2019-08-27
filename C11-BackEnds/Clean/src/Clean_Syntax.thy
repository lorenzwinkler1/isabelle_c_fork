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

theory Clean_Syntax
  imports Clean.Clean
          Isabelle_C.C_Main
begin

ML \<open>
val _ =
  (Theory.setup o C_Module.C_Term.map_expression)
    (fn expr => fn _ => fn ctxt =>
      let
        fun err () = error "syntax error"
        fun const var = case Proof_Context.read_const {proper = true, strict = false} ctxt var of
                          Const (c, _) => Syntax.const c
                        | _ => err ()
        open C_Ast
        open Term
        val decode = fn CVar0 (Ident0 (_, x, _), _) => C_Grammar_Rule_Lib.ident_decode x
                      | _ => err ()
        val const' = const o decode
      in
        case expr of
          CAssign0 (CAssignOp0, var_x, CIndex0 (var_y, var_z, _), _) =>
            Syntax.const @{const_name assign_local}
            $ const (decode var_x ^ "_update")
            $ Clean_Syntax_Lift.transform_term
                (Syntax.const @{const_name nth} $ const' var_y $ const' var_z)
                ctxt
        | _ => err ()
      end)\<close>

global_vars state
  A :: "int list"
  hi :: nat

local_vars_test swap "unit"
  tmp :: "int"

term \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>tmp = A [hi]\<close>\<close>

end
