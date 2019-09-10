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

fun map_typ f = fn
    Term.Type (s, l) => f (s, map (map_typ f) l)
  | x => x

fun new_state_record pos b =
  apsnd
    (map_filter
      (fn (NONE, _) => NONE
        | (SOME {src_name, src_return_var, ...}, (b, typ, mixfix)) =>
            SOME ( Binding.map_name (K (if src_return_var then StateMgt.result_name else src_name)) b
                 , map_typ (fn ("Arrays.array", x :: _ :: []) => Term.Type ("List.list", [x])
                             | x => Term.Type x)
                           typ
                 , mixfix)))
 #>
 (fn (_, []) => NONE
   | (rcd_name, flds) =>
      (SOME o T.one o T.setup o SML_top)
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
  in 
    map_filter
      I
      [ new_state_record pos true global_rcd
      , new_state_record pos false local_rcd
      , SOME (T.locale ( Semi_locale_ext (s (ML_Syntax'.make_pos "C" pos), [], ())
                       , [map (fn function =>
                                [ T.definition (bs ("pop_" ^ #fname function)) "\<equiv>" (bs "()")
                                , T.definition (bs ("push_" ^ #fname function)) "\<equiv>" (bs "()")
                                , T.definition (bs ("core_" ^ #fname function)) "\<equiv>" (bs "()")])
                              (rev fninfo)
                          |> flat]))]
  end

end
end
\<close>

section \<open>Syntax\<close>

ML \<open>
structure Conversion_C11 =
struct
fun expression _ ctxt expr = expr |>
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
   fn CAssign0 (CAssignOp0, var_x, CIndex0 (var_y, var_z, _), _) =>
        Syntax.const @{const_name assign_local}
        $ const (decode var_x ^ "_update")
        $ Clean_Syntax_Lift.transform_term'
            ctxt
            (Syntax.const @{const_name nth} $ const' var_y $ const' var_z)
    | expr => warn ("Case not yet treated for this element: " ^ @{make_string} expr)
  end
end
\<close>

ML \<open>
structure Conversion_C99 =
struct

fun warn msg = tap (fn _ => warning ("Syntax error: " ^ msg)) @{term "()"}
fun const0 ctxt var = case Proof_Context.read_const {proper = true, strict = false} ctxt var of
                       Const (c, _) => SOME c
                     | _ => NONE
fun const ctxt var = case const0 ctxt var of
                       SOME c => Syntax.const c
                     | NONE => warn "Expecting a constant"
fun map_expr f exp =
  let val (res, exp_n) = f (Expr.enode exp)
  in (res, Expr.ewrap (exp_n, Expr.eleft exp, Expr.eright exp)) end

open C_Ast
open Term

local
open Expr
in
fun extract_deref acc exp = enode exp |>
  (fn Var _ => Left (fn f => map_expr f exp, acc)
    | ArrayDeref (exp1, exp2) => extract_deref (exp2 :: acc) exp1
    | exp => Right exp)

fun expr_node env_lang ctxt exp = exp |>
  let val expr = expr env_lang ctxt
  in
   fn BinOp (ope, exp1, exp2) =>
        Syntax.const (case ope of Plus => @{const_name plus}
                                | Lt => @{const_name less}
                                | _ => error ("Case not yet treated for this element: " ^ @{make_string} ope))
        $ expr exp1
        $ expr exp2
    | ArrayDeref (exp1, exp2) =>
        Syntax.const @{const_name nth} $ expr exp1 $ expr exp2
    | Constant cst => Syntax.read_term ctxt (cst |> eval_litconst |> #1 |> Int.toString |> (fn s => s ^ " :: nat"))
    | Var (x, _) => const ctxt x
    | exp => warn ("Case not yet treated for this element: " ^ @{make_string} exp)
  end
and expr env_lang ctxt exp = exp |>
  expr_node env_lang ctxt o enode
end

fun expr_lift env_lang ctxt =
  Clean_Syntax_Lift.transform_term' ctxt o expr env_lang ctxt

fun expr_lift' env_lang ctxt db exp =
  Clean_Syntax_Lift.app_sigma db (expr env_lang ctxt exp) ctxt

local
open StmtDecl
in
fun statement_node env_lang ctxt stmt = stmt |>
  let
    val expr = expr env_lang ctxt
    val expr_lift' = expr_lift' env_lang ctxt
    val expr_lift = expr_lift env_lang ctxt
    val statement = statement env_lang ctxt
    val block_item = block_item env_lang ctxt
    (**)
    val skip = Syntax.const @{const_name skip\<^sub>S\<^sub>E}
  in
   fn Assign (exp1, exp2) =>
       (case extract_deref [] exp1 of
          Right exp => error ("Case not yet treated for this element: " ^ @{make_string} exp)
        | Left (map_var, exp_deref) =>
            Syntax.const @{const_name assign}
            $ Abs
              ( "\<sigma>"
              , dummyT
              , let
                  val (f, var) =
                      map_var
                        (fn Expr.Var (var, node) =>
                              ( case env_lang var of
                                  NONE => error ("Expecting to be in the environment: " ^ @{make_string} var)
                                | SOME true => I
                                | SOME false => fn var => Syntax.const @{const_name comp} $ var $ Syntax.const @{const_name map_hd}
                              , Expr.Var (Clean_Syntax_Lift.assign_update var, node))
                          | exp => error ("Case not yet treated for this element: " ^ @{make_string} exp))
                in f (expr var)
                end
                $ fold_rev (fn exp => fn acc => Syntax.const @{const_name map_nth} $ expr_lift' 0 exp $ acc) exp_deref (Abs ("_", dummyT, expr_lift' 1 exp2))
                $ Bound 0))
    | Block block => block |>
        (fn [] => skip
          | b :: bs =>
              fold (fn b => fn acc => Syntax.const @{const_name bind_SE'} $ acc $ block_item b) bs (block_item b))
    | Trap (BreakT, stmt) => snode stmt |>
        (fn While (exp, NONE, stmt) =>
              Syntax.const @{const_name while_C}
              $ expr_lift exp
              $ statement stmt
          | stmt => warn ("Case not yet treated for this element: " ^ @{make_string} stmt))
    | Trap (ContinueT, stmt) => statement stmt
    | IfStmt (exp, stmt1, stmt2) => Syntax.const @{const_name if_C}
                                    $ expr_lift exp
                                    $ statement stmt1
                                    $ statement stmt2
    | EmptyStmt => skip
    | stmt => warn ("Case not yet treated for this element: " ^ @{make_string} stmt)
  end
and statement env_lang ctxt stmt = stmt |>
  statement_node env_lang ctxt o snode
and block_item env_lang ctxt bi = bi |>
  let
    val statement = statement env_lang ctxt
  in
   fn BI_Stmt stmt => statement stmt
    | BI_Decl _ => tap (fn _ => warning "Skipping BI_Decl") (Syntax.const @{const_name skip\<^sub>S\<^sub>E})
  end
end

val statement = fn env_lang => fn ctxt =>
  statement env_lang ctxt o (IsarPreInstall.of_statement o C_Ast.statement0 ([], C_Ast.Alist []))

end
\<close>

ML \<open>
val _ = Theory.setup (C_Module.C_Term.map_expression (fn expr => fn _ => fn ctxt => Conversion_C11.expression () ctxt expr))
val _ = Theory.setup
          (C_Module.C_Term.map_statement
            (fn stmt => fn _ => fn ctxt =>
              Conversion_C99.statement
                (Conversion_C99.const0 ctxt
                  #> (fn SOME name => Clean_Syntax_Lift.scope_var name ctxt
                       | NONE => tap (fn _ => warning "Expecting a constant") NONE))
                ctxt
                stmt))
\<close>

subsection \<open>Test\<close>

global_vars state
  a :: "nat list"
  aa :: "nat list list"
  aaa :: "nat list list list"

local_vars_test swap unit
  a\<^sub>l :: "nat list"
  aa\<^sub>l :: "nat list list"
  aaa\<^sub>l :: "nat list list list"
  pivot :: nat
  pivot_idx :: nat
  i :: nat
  j :: nat
  nn :: nat

term \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r \<open>pivot = a[pivot_idx]\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>if (a[j] < a[i]) {}\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>pivot = a[pivot_idx];\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>a[pivot_idx] = a[i];\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>aa[j][pivot_idx] = a[i];\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>aaa[nn][j][pivot_idx] = a[i];\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>a\<^sub>l[pivot_idx] = a[i];\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>aa\<^sub>l[j][pivot_idx] = a[i];\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>aaa\<^sub>l[nn][j][pivot_idx] = a[i];\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>if (a[j] < a[i]) { pivot_idx++; }\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>for (i = 1; i < nn; i++) { pivot_idx++; }\<close>\<close>
term \<open>\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>a[pivot_idx] = a[i];\<close> ;-
      \<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>pivot_idx++;\<close> ;-
      \<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t \<open>a[i] = a[pivot_idx];\<close>\<close>

end
