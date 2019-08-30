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

theory Example3
  imports CParser.Init
begin

section \<open>\<close>

ML\<open>
local
val command = C_Inner_Syntax.command C_Inner_Isar_Cmd.setup' C_Parse.ML_source
in
val _ = Theory.setup (   command C_Transition.Bottom_up ("\<simeq>setup", \<^here>)
                      #> command C_Transition.Top_down ("\<simeq>setup\<Down>", \<^here>))
end

val C' = C_Module.C'

fun C opt = case opt of NONE => C' (C_Module.env (Context.the_generic_context ()))
                      | SOME env => C' env

fun C_def dir name _ _ =
  Context.map_theory 
    (C_Inner_Syntax.command0
      (fn src => fn context => C' (C_Stack.Data_Lang.get context |> #2) src context)
      C_Parse.C_source
      dir
      name)

local
in
val _ = Theory.setup
  (ML_Antiquotation.declaration
    @{binding "C_def"}
    (Scan.lift (Parse.sym_ident -- Parse.position Parse.name))
    (fn _ => fn (top_down, (name, pos)) =>
      tap (fn ctxt => Context_Position.reports ctxt [(pos, Markup.keyword1)]) #>
      C_Context.fun_decl
               "cmd" "x" ( "C_def "
                         ^ (case top_down of "\<Up>" => "C_Transition.Bottom_up"
                                           | "\<Down>" => "C_Transition.Top_down"
                                           | _ => error "Illegal symbol")
                         ^ " (\"" ^ name ^ "\", " ^ ML_Syntax.print_position pos ^ ")")))
end
\<close>

definition [simplified]: "UINT_MAX \<equiv> (2 :: nat) ^ 32 - 1"

section \<open>\<close>

C \<open>
int sum1(int a)
{
  while (a < 10)
    /*@ @ INV: \<open>\<dots>\<close>
        @ highlight */
    { a = a + 1; }
  return a;
}\<close>



C \<open>
int sum2(int a)
/*@ ++@ INV: \<open>\<dots>\<close>
    ++@ highlight */
{
  while (a < 10)
    { a = a + 1; }
  return a;
}\<close>



C (*NONE*) \<comment> \<open>starting environment = empty\<close> \<open>
int a (int b) { return &a + b + c; }
/*@ \<simeq>setup \<open>fn stack_top => fn env =>
            C (SOME env) \<open>int c = &a + b + c;\<close>\<close>
    \<simeq>setup \<open>fn stack_top => fn env =>
            C  NONE      \<open>int c = &a + b + c;\<close>\<close>
    declare [[C_starting_env = last]]
    C        (*SOME*)    \<open>int c = &a + b + c;\<close>
*/\<close>

section \<open>\<close>

C \<open>
#define SQRT_UINT_MAX 65536
/*@ lemma uint_max_factor [simp]:
      "UINT_MAX = SQRT_UINT_MAX * SQRT_UINT_MAX - 1"
    by (clarsimp simp: UINT_MAX_def SQRT_UINT_MAX_def)
*/\<close>

term SQRT_UINT_MAX

section \<open>\<close>

C \<open>int _;
/*@ @ C \<open>//@ C1 \<open>int _; //@ @ \<simeq>setup\<Down> \<open>@{C_def \<Up> C2}\<close> \
                            @ C1  \<open>//* C2 \<open>int _;\<close>\<close>   \
                            @ C1\<Down> \<open>//* C2 \<open>int _;\<close>\<close>    \<close>\<close>
    @ C \<open>//* C2 \<open>int _;\<close>                                \<close>
      \<simeq>setup \<open>@{C_def \<Up> (* bottom-up *)  C1  }\<close>
      \<simeq>setup \<open>@{C_def \<Down> (* top-down  *) "C1\<Down>"}\<close>
*/\<close>

end

