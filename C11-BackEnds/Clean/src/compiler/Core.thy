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
          Clean.Clean
begin

section \<open>Miscellaneous\<close>

ML \<comment> \<open>\<^file>\<open>../../../../l4v/src/tools/c-parser/MString.ML\<close>\<close> \<open>
(*
 * Copyright 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure MString =
struct
  type t = string
  fun mk s = s
  fun dest s = s
  fun destPP s = "MV(" ^ s ^ ")"
  val compare = String.compare
end
\<close>

ML \<comment> \<open>\<^file>\<open>../../../../l4v/src/tools/c-parser/name_generation.ML\<close>\<close> \<open>
(*
 * Copyright 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure NameGeneration =
struct

fun embret_var_name (f,i) =
    if i < 1 then raise Fail "embret_var_name: i < 1"
    else if i = 1 then MString.mk ("ret__" ^ f)
    else MString.mk (f ^ "_eret_" ^ Int.toString i)

fun dest_embret s0 =
  let
    val s = MString.dest s0
  in
    if String.isPrefix "ret__" s then
      SOME (String.extract(s,5,NONE), 1)
    else let
        open Substring
        val (pfx, digsfx) = splitr Char.isDigit (full s)
      in
        if isEmpty digsfx then NONE
        else if isSuffix "_eret_" pfx then
          SOME (string (trimr 6 pfx), Option.valOf (Int.fromString (string digsfx)))
        else
          NONE
      end
  end
end
\<close>

section \<open>Conversion\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/ML/ml_syntax.ML\<close>\<close> \<open>
structure ML_Syntax' =
struct
fun make_pos s (theory_name, cmd) = theory_name ^ Int.toString cmd ^ "_" ^ s
fun print_pair3 f1 f2 f3 (x, y, z) = "(" ^ f1 x ^ ", " ^ f2 y ^ ", " ^ f3 z ^ ")";
fun print_binding b = ML_Syntax.make_binding (Binding.name_of b, Binding.pos_of b)
fun print_binding' pos b = ML_Syntax.make_binding (make_pos (Binding.name_of b) pos, Binding.pos_of b)
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/ML/ml_antiquotations.ML\<close>\<close>
   \<comment> \<open>\<^file>\<open>~~/src/Pure/Thy/document_antiquotations.ML\<close>\<close> \<open>
structure ML_Antiquotations' =
struct
fun ml_enclose bg en source =
  ML_Lex.read bg @ ML_Lex.read_source source @ ML_Lex.read en;

val _ = Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>ML'\<close>
    (Scan.peek (fn context => 
      Args.text_input >> (fn text =>
      let val _ = ML_Context.eval_in (SOME (Context.proof_of context))
                                     ML_Compiler.flags
                                     (Input.pos_of text)
                                     (ml_enclose "fn _ => (" ");" text)
      in #1 (Input.source_content text) end))
     >> ML_Syntax.print_string))
end
\<close>

ML \<comment> \<open>\<^file>\<open>../../../../C11-FrontEnd/generated/c_ast.ML\<close>\<close> \<open>
structure T =
struct
open C_Ast
local
val s = SS_base o ST
in
val setup = Theory_setup o Setup
fun definition v1 v2 v3 = Theory_definition (Definitiona (Term_rewrite (v1, s v2, v3)))
val one = META_semi_theories o Theories_one
val locale = META_semi_theories o Theories_locale
end
end
\<close>

ML \<comment> \<open>\<^file>\<open>../../../../Citadelle/src/compiler/Core.thy\<close>\<close> \<open>
structure Clean_Core =
struct
open C_Ast

local
val s = SS_base o ST
fun b x = Term_basic [x]
fun b' x = SML_basic [x]
val bs = b o s
val b's = b' o s

fun new_state_record pos b (rcd_name, flds) =
 T.setup
  (SML_top
   [SML_val_fun
    ( NONE
    , SML_apply ( b's \<^ML'>\<open>StateMgt.new_state_record'\<close>
                , [ b's (if b then \<^ML'>\<open>true\<close> else \<^ML'>\<open>false\<close>)
                  , b's (ML_Syntax.print_pair
                            (ML_Syntax.print_pair (ML_Syntax.print_pair (ML_Syntax.print_list (ML_Syntax.print_pair ML_Syntax.print_string (ML_Syntax.print_option ML_Syntax.print_string)))
                                                                          (ML_Syntax'.print_binding' pos))
                                                  (ML_Syntax.print_option ML_Syntax.print_typ))
                            (ML_Syntax.print_list (ML_Syntax'.print_pair3
                                                    ML_Syntax'.print_binding
                                                    ML_Syntax.print_typ
                                                    (fn NoSyn => \<^ML'>\<open>NoSyn\<close> | _ => error "Not implemented")))
                            ((([], rcd_name), NONE), flds))]))])

in

fun compile ast env_lang pos =
  let val (local_rcd, global_rcd, fninfo) = IsarInstall.install_C_file0 ast env_lang
      val _ = [ T.one (new_state_record pos true global_rcd)
              , T.one (new_state_record pos false local_rcd) ]
  in 
    [ T.locale ( Semi_locale_ext (s (ML_Syntax'.make_pos "C" pos), [], ())
               , [map (fn function =>
                        [ T.definition (bs ("pop_" ^ #fname function)) "\<equiv>" (bs "()")
                        , T.definition (bs ("push_" ^ #fname function)) "\<equiv>" (bs "()")
                        , T.definition (bs ("core_" ^ #fname function)) "\<equiv>" (bs "()")])
                      (rev fninfo)
                  |> flat])]
  end

end
end
\<close>

section \<open>Syntax\<close>

ML \<open>
structure Conversion_C11 =
struct
fun expression expr _ ctxt =
  let
    fun warn msg = tap (fn _ => warning ("Syntax error: " ^ msg)) @{term "()"}
    fun const var = case Proof_Context.read_const {proper = true, strict = false} ctxt var of
                      Const (c, _) => Syntax.const c
                    | _ => warn "Expecting a constant"
    open C_Ast
    open Term
    val decode = fn CVar0 (Ident0 (_, x, _), _) => C_Grammar_Rule_Lib.ident_decode x
                  | _ => error "Expecting a variable"
    val const' = const o decode
  in
    case expr of
      CAssign0 (CAssignOp0, var_x, CIndex0 (var_y, var_z, _), _) =>
        Syntax.const @{const_name assign_local}
        $ const (decode var_x ^ "_update")
        $ Clean_Syntax_Lift.transform_term
            (Syntax.const @{const_name nth} $ const' var_y $ const' var_z)
            ctxt
    | _ => warn ("Case not yet treated for this element: " ^ @{make_string} expr)
  end
end
\<close>

ML \<open>
structure Conversion_C99 =
struct
fun statement stmt _ ctxt =
  let
    fun warn msg = tap (fn _ => warning ("Syntax error: " ^ msg)) @{term "()"}
    fun const var = case Proof_Context.read_const {proper = true, strict = false} ctxt var of
                      Const (c, _) => Syntax.const c
                    | _ => warn "Expecting a constant"
    open C_Ast
    open Term
    val decode = fn Expr.Var (x, _) => x
                  | _ => error "Expecting a variable"
    val const' = const o decode o Expr.enode
    val stmt = IsarPreInstall.of_statement (C_Ast.statement0 ([], C_Ast.Alist []) stmt)
  in
    case StmtDecl.snode stmt of
      StmtDecl.Assign (var_x, expr) =>
        (case Expr.enode expr of
           Expr.ArrayDeref (var_y, var_z) =>
             Syntax.const @{const_name assign_local}
             $ const (decode (Expr.enode var_x) ^ "_update")
             $ Clean_Syntax_Lift.transform_term
                 (Syntax.const @{const_name nth} $ const' var_y $ const' var_z)
                 ctxt
         | _ => warn ("Case not yet treated for this element: " ^ @{make_string} expr))
    | _ => warn ("Case not yet treated for this element: " ^ @{make_string} stmt)
  end
end

\<close>

ML\<open>
val _ = Theory.setup (C_Module.C_Term.map_expression Conversion_C11.expression)
val _ = Theory.setup (C_Module.C_Term.map_statement Conversion_C99.statement)
\<close>

subsection \<open>Test\<close>

global_vars state
  A :: "int list"
  hi :: nat

local_vars_test swap "unit"
  tmp :: "int"

term \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>tmp = A [hi]\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t\<open>tmp = A [hi];\<close>\<close>

end
