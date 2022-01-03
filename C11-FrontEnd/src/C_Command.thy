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

section \<open>Interface: Inner and Outer Commands\<close>

theory C_Command
  imports C_Eval
  keywords "C" :: thy_decl % "ML"
       and "C_file" :: thy_load % "ML"
       and "C_export_boot" :: thy_decl % "ML"
       and "C_export_file" :: thy_decl
       and "C_prf" :: prf_decl % "proof"  (* FIXME % "ML" ?? *)
       and "C_val" :: diag % "ML"
begin

subsection \<open>Parsing Entry-Point: Error and Acceptance Cases\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Tools/ghc.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay
    Analogous to:
(*  Title:      Pure/Tools/ghc.ML
    Author:     Makarius

Support for GHC: Glasgow Haskell Compiler.
*)*)
\<open>
structure C_Serialize =
struct

(** string literals **)

fun print_codepoint c =
  (case c of
    10 => "\\n"
  | 9 => "\\t"
  | 11 => "\\v"
  | 8 => "\\b"
  | 13 => "\\r"
  | 12 => "\\f"
  | 7 => "\\a"
  | 27 => "\\e"
  | 92 => "\\\\"
  | 63 => "\\?"
  | 39 => "\\'"
  | 34 => "\\\""
  | c =>
      if c >= 32 andalso c < 127 then chr c
      else error "Not yet implemented");

fun print_symbol sym =
  (case Symbol.decode sym of
    Symbol.Char s => print_codepoint (ord s)
  | Symbol.UTF8 s => UTF8.decode_permissive s |> map print_codepoint |> implode
  | Symbol.Sym s => "\\092<" ^ s ^ ">"
  | Symbol.Control s => "\\092<^" ^ s ^ ">"
  | _ => translate_string (print_codepoint o ord) sym);

val print_string = quote o implode o map print_symbol o Symbol.explode;
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Tools/generated_files.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay
    Analogous to:
(*  Title:      Pure/Tools/generated_files.ML
    Author:     Makarius

Generated source files for other languages: with antiquotations, without Isabelle symbols.
*)*)
\<open>
structure C_Generated_Files =
struct

val c_dir = "C";
val c_ext = "c";
val c_make_comment = enclose "/*" "*/";

(** context data **)

(* file types *)

fun get_file_type ext =
  if ext = "" then error "Bad file extension"
  else if c_ext = ext then ()
  else error ("Unknown file type for extension " ^ quote ext);



(** Isar commands **)

(* generate_file *)

fun generate_file (binding, src_content) lthy =
  let
    val (path, pos) = Path.dest_binding binding;
    val () =
      get_file_type (#2 (Path.split_ext path))
        handle ERROR msg => error (msg ^ Position.here pos);
    val header = c_make_comment " generated by Isabelle ";
    val content = header ^ "\n" ^ src_content;
  in lthy |> (Local_Theory.background_theory o Generated_Files.add_files) (binding, content) end;



(** concrete file types **)

val _ =
  Theory.setup
    (Generated_Files.file_type \<^binding>\<open>C\<close>
      {ext = c_ext,
       make_comment = c_make_comment,
       make_string = C_Serialize.print_string});
end
\<close>

ML \<comment> \<open>\<^theory>\<open>Isabelle_C.C_Eval\<close>\<close> \<open>
structure C_Module =
struct

structure Data_In_Source = Generic_Data
(
  type T = Input.source list
  val empty = []
  val merge = K empty
)

structure Data_In_Env = Generic_Data
(
  type T = C_Env.env_lang
  val empty = C_Env.empty_env_lang
  val merge = K empty
)

structure Data_Accept = Generic_Data
(
  type T = C_Grammar_Rule.ast_generic -> C_Env.env_lang -> Context.generic -> Context.generic
  fun empty _ _ = I
  val merge = #2
)

structure Data_Term = Generic_Data
(
  type T = (C_Grammar_Rule.ast_generic -> C_Env.env_lang -> local_theory -> term) Symtab.table
  val empty = Symtab.empty
  val merge = #2
)

structure C_Term =
struct
val key_translation_unit = \<open>translation_unit\<close>
val key_external_declaration = \<open>external_declaration\<close>
val key_statement = \<open>statement\<close>
val key_expression = \<open>expression\<close>
val key_default = \<open>default\<close>

local
val source_content = Input.source_content #> #1
in
val key0_translation_unit = source_content key_translation_unit
val key0_external_declaration = source_content key_external_declaration
val key0_statement = source_content key_statement
val key0_expression = source_content key_expression
val key0_default = source_content key_default
end

val tok0_translation_unit = (key0_translation_unit, C_Grammar.Tokens.start_translation_unit)
val tok0_external_declaration = ( key0_external_declaration
                                , C_Grammar.Tokens.start_external_declaration)
val tok0_statement = (key0_statement, C_Grammar.Tokens.start_statement)
val tok0_expression = (key0_expression, C_Grammar.Tokens.start_expression)

val tok_translation_unit = (key_translation_unit, C_Grammar.Tokens.start_translation_unit)
val tok_external_declaration = ( key_external_declaration
                               , C_Grammar.Tokens.start_external_declaration)
val tok_statement = (key_statement, C_Grammar.Tokens.start_statement)
val tok_expression = (key_expression, C_Grammar.Tokens.start_expression)

val tokens = [ tok0_translation_unit
             , tok0_external_declaration
             , tok0_statement
             , tok0_expression ]

local
fun map_upd0 key v = Context.theory_map (Data_Term.map (Symtab.update (key, v)))
fun map_upd key start f = map_upd0 key (f o the o start)
in
val map_translation_unit = map_upd key0_translation_unit C_Grammar_Rule.get_CTranslUnit
val map_external_declaration = map_upd key0_external_declaration C_Grammar_Rule.get_CExtDecl
val map_statement = map_upd key0_statement C_Grammar_Rule.get_CStat
val map_expression = map_upd key0_expression C_Grammar_Rule.get_CExpr
val map_default = map_upd0 key0_default
end

end

fun env0 ctxt =
  case Config.get ctxt C_Options.starting_env of
    "last" => Data_In_Env.get (Context.Proof ctxt)
  | "empty" => C_Env.empty_env_lang
  | s => error ("Unknown option: " ^ s ^ Position.here (Config.pos_of C_Options.starting_env))

val env = env0 o Context.proof_of

fun start source context =
 Input.range_of source
 |>
  let val s = Config.get (Context.proof_of context) C_Options.starting_rule
  in case AList.lookup (op =) C_Term.tokens s of
       SOME tok => tok
     | NONE => error ("Unknown option: " ^ s
                                         ^ Position.here (Config.pos_of C_Options.starting_rule))
  end

fun err0 _ _ pos =
  C_Env.map_error_lines (cons ("Parser: No matching grammar rule" ^ Position.here pos))

val err = pair () oooo err0

fun accept0 f env_lang ast =
  Data_In_Env.put env_lang
  #> (fn context => f context ast env_lang (Data_Accept.get context ast env_lang context))

fun accept env_lang (_, (ast, _, _)) =
  pair () o C_Env.map_context (accept0 (K (K (K I))) env_lang ast)

val eval_source = C_Context.eval_source env start err accept

fun c_enclose bg en source =
  C_Lex.@@ ( C_Lex.@@ (C_Lex.read bg, C_Lex.read_source source)
           , C_Lex.read en);

structure C_Term' =
struct
val err = pair Term.dummy oooo err0

fun accept ctxt start_rule =
  let 
    val (key, start) =
      case start_rule of NONE => (C_Term.key_default, start)
                       | SOME (key, start_rule) =>
                           (key, fn source => fn _ => start_rule (Input.range_of source))
    val (key, pos) = Input.source_content key
  in
    ( start
    , fn env_lang => fn (_, (ast, _, _)) =>
        C_Env.map_context'
          (accept0
            (fn context =>
              pair oo (case Symtab.lookup (Data_Term.get context) key of
                         NONE => tap (fn _ => warning ("Representation function associated to\
                                                       \ \"" ^ key ^ "\"" ^ Position.here pos
                                                       ^ " not found (returning a dummy term)"))
                                     (fn _ => fn _ => @{term "()"})
                       | SOME f => fn ast => fn env_lang => f ast env_lang ctxt))
            env_lang
            ast))
  end

fun eval_in text context env start_rule =
  let 
    val (start, accept) = accept (Context.proof_of context) start_rule
  in
    C_Context.eval_in (SOME context) env (start text) err accept
  end

fun parse_translation l = l |>
  map
  (apsnd
    (fn start_rule => fn ctxt => fn args =>
      let val msg = (case start_rule of NONE => C_Term.key_default
                                      | SOME (key, _) => key)
                    |> Input.source_content |> #1
          fun err () = raise TERM (msg, args)
      in
       case args of
         [(c as Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ Free (s, _) $ p] =>
          (case Term_Position.decode_position p of
            SOME (pos, _) =>
            c
            $ let val src = 
                uncurry
                  (Input.source false)
                  let val s0 = Symbol_Pos.explode (s, pos)
                      val s = Symbol_Pos.cartouche_content s0
                  in
                    ( Symbol_Pos.implode s
                    , case s of [] => Position.no_range
                              | (_, pos0) :: _ => Position.range (pos0, s0 |> List.last |> snd))
                  end
              in
              eval_in
                src
                (case Context.get_generic_context () of
                   NONE => Context.Proof ctxt
                 | SOME context => Context.mapping I (K ctxt) context)
                (C_Stack.Data_Lang.get #> (fn NONE => env0 ctxt
                                            | SOME (_, env_lang) => env_lang))
                start_rule
                (c_enclose "" "" src)
              end
            $ p
          | NONE => err ())
       | _ => err ()
      end))
end

fun eval_in text ctxt = C_Context.eval_in ctxt env (start text) err accept

fun exec_eval source =
  Data_In_Source.map (cons source)
  #> ML_Context.exec (fn () => eval_source source)

fun C_prf source =
  Proof.map_context (Context.proof_map (exec_eval source))
  #> Proof.propagate_ml_env

fun C_export_boot source context =
  context
  |> Config.put_generic ML_Env.ML_environment ML_Env.Isabelle
  |> Config.put_generic ML_Env.ML_write_global true
  |> exec_eval source
  |> Config.restore_generic ML_Env.ML_write_global context
  |> Config.restore_generic ML_Env.ML_environment context
  |> Local_Theory.propagate_ml_env

fun C source =
  exec_eval source
  #> Local_Theory.propagate_ml_env

val C' =
  let
    fun C env_lang src context =
      context
      |> C_Env.empty_env_tree
      |> C_Context.eval_source'
           env_lang
           (fn src => start src context)
           err
           accept
           src
      |> (fn (_, {context, reports_text, error_lines}) => 
         tap (fn _ => case error_lines of [] => () | l => warning (cat_lines (rev l)))
             (C_Stack.Data_Tree.map (curry C_Stack.Data_Tree_Args.merge (reports_text, []))
                                    context))
  in
    fn NONE => (fn src => C (env (Context.the_generic_context ())) src)
     | SOME env_lang => C env_lang
  end

fun C_export_file (pos, _) lthy =
  let
    val c_sources = Data_In_Source.get (Context.Proof lthy)
    val binding =
      Path.binding
        ( Path.appends [ Path.basic C_Generated_Files.c_dir
                       , Path.basic (string_of_int (length c_sources))
                       , lthy |> Proof_Context.theory_of |> Context.theory_name |> Path.explode
                              |> Path.ext C_Generated_Files.c_ext ]
        , pos)
  in
    lthy
    |> C_Generated_Files.generate_file (binding, rev c_sources |> map (Input.source_content #> #1)
                                                               |> cat_lines)
    |> tap (Proof_Context.theory_of
            #> (fn thy => let val file = Generated_Files.get_file thy binding
                          in Generated_Files.export_file thy file;
                             writeln (Export.message thy Path.current);
                             writeln (prefix "  " (Generated_Files.print_file file))
                          end))
  end
end
\<close>

subsection \<open>Definitions of Inner Directive Commands\<close>

subsubsection \<open>Initialization\<close>

ML \<comment> \<open>\<^theory>\<open>Pure\<close>\<close> \<open>
structure C_Directive =
struct
local
fun directive_update keyword data = C_Context.directive_update keyword (data, K (K (K I)))
fun return f (env_cond, env) = ([], (env_cond, f env))
fun directive_update_define pos f_toks f_antiq =
  directive_update ("define", pos)
    (return
     o
      (fn C_Lex.Define (_, C_Lex.Group1 ([], [tok3]), NONE, C_Lex.Group1 ([], toks)) =>
          let val map_ctxt = 
              case (tok3, toks) of
                (C_Lex.Token ((pos, _), (C_Lex.Ident _, ident)),
                 [C_Lex.Token (_, (C_Lex.Integer (_, C_Lex.Repr_decimal, []), integer))]) =>
                  C_Env.map_context
                    (Context.map_theory
                      (Named_Target.theory_map
                        (Specification.definition_cmd
                          (SOME (Binding.make (ident, pos), NONE, NoSyn))
                          []
                          []
                          (Binding.empty_atts, ident ^ " \<equiv> " ^ integer)
                          true
                         #> tap (fn ((_, (_, t)), ctxt) =>
                                 Output.information
                                   ("Generating "
                                    ^ Pretty.string_of (Syntax.pretty_term ctxt (Thm.prop_of t))
                                    ^ Position.here
                                        (Position.range_position
                                          ( C_Lex.pos_of tok3
                                          , C_Lex.end_pos_of (List.last toks)))))
                         #> #2)))
              | _ => I
          in 
            fn (env_dir, env_tree) =>
              let val name = C_Lex.content_of tok3
                  val pos = [C_Lex.pos_of tok3]
                  val data = (pos, serial (), (C_Scan.Left (f_toks toks), f_antiq))
              in
                ( Symtab.update (name, data) env_dir
                , env_tree |> C_Context.markup_directive_define
                                false
                                (C_Ast.Left (data, C_Env_Ext.list_lookup env_dir name))
                                pos
                                name
                           |> map_ctxt)
              end
          end
        | C_Lex.Define (_, C_Lex.Group1 ([], [tok3]), SOME (C_Lex.Group1 (_ :: toks_bl, _)), _)
          =>
            tap (fn _ => (* not yet implemented *)
                   warning ("Ignored functional macro directive"
                            ^ Position.here
                                (Position.range_position
                                  (C_Lex.pos_of tok3, C_Lex.end_pos_of (List.last toks_bl)))))
        | _ => I))
in
val setup_define = Context.theory_map o C_Context0.Directives.map ooo directive_update_define

val _ =
  Theory.setup
  (Context.theory_map
    (C_Context0.Directives.map
      (directive_update_define \<^here> (K o pair) (K I)
       #>
       directive_update ("undef", \<^here>)
        (return
         o
          (fn C_Lex.Undef (C_Lex.Group2 (_, _, [tok])) =>
                (fn (env_dir, env_tree) =>
                  let val name = C_Lex.content_of tok
                      val pos1 = [C_Lex.pos_of tok]
                      val data = Symtab.lookup env_dir name
                  in ( (case data of NONE => env_dir | SOME _ => Symtab.delete name env_dir)
                     , C_Context.markup_directive_define true
                                                         (C_Ast.Right (pos1, data))
                                                         pos1
                                                         name
                                                         env_tree)
                  end)
            | _ => I)))))
end
end
\<close>

subsection \<open>Definitions of Inner Annotation Commands\<close>
subsubsection \<open>Library\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/toplevel.ML\<close>\<close> \<open>
structure C_Inner_Toplevel =
struct
val theory = Context.map_theory
fun local_theory' target f gthy =
  let
    val (finish, lthy) = Target_Context.switch_named_cmd target gthy;
    val lthy' = lthy
      |> Local_Theory.new_group
      |> f false
      |> Local_Theory.reset_group;
  in finish lthy' end
val generic_theory = I
fun keep'' f = tap (f o Context.proof_of)
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/isar_cmd.ML\<close>\<close> \<open>
structure C_Inner_Isar_Cmd = 
struct


(** theory declarations **)

(* generic setup *)

fun setup0 f_typ f_val src =
 fn NONE =>
    let val setup = "setup"
    in C_Context.expression
        "C_Ast"
        (Input.range_of src)
        setup
        (f_typ "C_Stack.stack_data"
               "C_Stack.stack_data_elem -> C_Env.env_lang -> Context.generic -> Context.generic")
        ("fn context => \
           \let val (stack, env_lang) = C_Stack.Data_Lang.get' context \
           \in " ^ f_val setup "stack" ^ " (stack |> hd) env_lang end context")
        (ML_Lex.read_source src) end
  | SOME rule => 
    let val hook = "hook"
    in C_Context.expression
        "C_Ast"
        (Input.range_of src)
        hook
        (f_typ "C_Stack.stack_data"
               (C_Grammar_Rule.type_reduce rule
                ^ " C_Stack.stack_elem -> C_Env.env_lang -> Context.generic -> Context.generic"))
        ("fn context => \
           \let val (stack, env_lang) = C_Stack.Data_Lang.get' context \
           \in " ^ f_val hook
                         "stack" ^ " "
                       ^ "(stack \
                           \|> hd \
                           \|> C_Stack.map_svalue0 C_Grammar_Rule.reduce" ^ Int.toString rule ^ ")\
                         \env_lang \
           \end \
           \  context")
        (ML_Lex.read_source src)
    end
val setup = setup0 (fn a => fn b => a ^ " -> " ^ b) (fn a => fn b => a ^ " " ^ b)
val setup' = setup0 (K I) K


(* print theorems, terms, types etc. *)

local

fun string_of_term ctxt s =
  let
    val t = Syntax.read_term ctxt s;
    val T = Term.type_of t;
    val ctxt' = Proof_Context.augment t ctxt;
  in
    Pretty.string_of
      (Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' T)])
  end;

fun print_item string_of (modes, arg) ctxt =
  Print_Mode.with_modes modes (fn () => writeln (string_of ctxt arg)) ();

in

val print_term = print_item string_of_term;

end;

end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/outer_syntax.ML\<close>\<close> \<open>
structure C_Inner_Syntax =
struct
val drop1 = fn C_Scan.Left f => C_Scan.Left (K o f)
             | C_Scan.Right (f, dir) => C_Scan.Right (K o f, dir)

val drop2 = fn C_Scan.Left f => C_Scan.Left (K o K o f)
             | C_Scan.Right (f, dir) => C_Scan.Right (K o K o f, dir)

val bottom_up = C_Env.Bottom_up o C_Env.Exec_annotation

(**)

fun pref_lex name = "#" ^ name
val pref_bot = I
fun pref_top name = name ^ "\<Down>"

(**)

fun command2' cmd f (pos_bot, pos_top) =
  let fun cmd' dir = cmd (C_Scan.Right (f, dir)) Keyword.thy_decl
  in   cmd' bottom_up (pref_bot, pos_bot)
    #> cmd' C_Env.Top_down (pref_top, pos_top)
  end

fun command3' cmd f (pos_lex, pos_bot, pos_top) =
     cmd (C_Scan.Left f) (pref_lex, pos_lex)
  #> command2' (K o cmd) f (pos_bot, pos_top)

fun command2 cmd f (name, pos_bot, pos_top) =
  command2' (fn f => fn kind => fn (name_pref, pos) => cmd f kind (name_pref name, pos))
            f
            (pos_bot, pos_top)

fun command3 cmd f (name, pos_lex, pos_bot, pos_top) =
  command3' (fn f => fn (name_pref, pos) => cmd f (name_pref name, pos))
            f
            (pos_lex, pos_bot, pos_top)

(**)

fun command00 f kind scan name =
  C_Annotation.command'' kind name ""
    (case f of
       C_Scan.Left f =>
        (fn _ =>
          C_Parse.range scan >>
            (fn (src, range) =>
              C_Env.Lexing (range, f src range)))
     | C_Scan.Right (f, dir) =>
         fn ((stack1, (to_delay, stack2)), _) =>
          C_Parse.range scan >>
            (fn (src, range) =>
              C_Env.Parsing ((stack1, stack2), (range, dir (f src range), Symtab.empty, to_delay))))

fun command00_no_range f kind name =
  C_Annotation.command'' kind name ""
    (case f of
       C_Scan.Left f =>
        (fn (_, range) =>
          Scan.succeed () >>
            K (C_Env.Lexing (range, f range)))
     | C_Scan.Right (f, dir) =>
         fn ((stack1, (to_delay, stack2)), range) =>
          Scan.succeed () >>
            K (C_Env.Parsing ((stack1, stack2), (range, dir (f range), Symtab.empty, to_delay))))

(**)

fun command' f = command00 (drop1 f) Keyword.thy_decl

fun command f scan = command2 (fn f => fn kind => command00 f kind scan) (K o f)

fun command_range f = command00_no_range f Keyword.thy_decl

val command_range' = command3 (command_range o drop1)

fun command_no_range' f = command00_no_range (drop1 f) Keyword.thy_decl

fun command_no_range f = command2 command00_no_range (K f)

fun command0 f scan = command3 (fn f => command' (drop1 f) scan) f

fun local_command' (name, pos_lex, pos_bot, pos_top) scan f =
  command3' (fn f => fn (name_pref, pos) =>
              command' (drop1 f)
                       (C_Token.syntax' (Parse.opt_target -- scan name_pref))
                       (name_pref name, pos))
            (fn (target, arg) => C_Inner_Toplevel.local_theory' target (f arg))
            (pos_lex, pos_bot, pos_top)

fun local_command'' spec = local_command' spec o K

val command0_no_range = command_no_range' o drop1

fun command0' f kind scan =
  command3 (fn f => command00 (drop2 f) kind scan) f
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/ML/ml_file.ML\<close>\<close> \<open>
structure C_Inner_File =
struct

fun command_c ({lines, pos, ...}: Token.file) =
  C_Module.C (Input.source true (cat_lines lines) (pos, pos));

fun C get_file gthy =
  command_c (get_file (Context.theory_of gthy)) gthy;

fun command_ml environment debug get_file gthy =
  let
    val file = get_file (Context.theory_of gthy);
    val source = Token.file_source file;

    val _ = Document_Output.check_comments (Context.proof_of gthy) (Input.source_explode source);

    val flags: ML_Compiler.flags =
      {environment = environment, redirect = true, verbose = true,
        debug = debug, writeln = writeln, warning = warning};
  in
    gthy
    |> ML_Context.exec (fn () => ML_Context.eval_source flags source)
    |> Local_Theory.propagate_ml_env
  end;

val ML = command_ml "";
val SML = command_ml ML_Env.SML;
end;
\<close>

subsubsection \<open>Initialization\<close>

setup \<comment> \<open>\<^theory>\<open>Pure\<close>\<close> \<open>
C_Thy_Header.add_keywords_minor
  (maps (fn ((name, pos_lex, pos_bot, pos_top), ty) =>
          [ ((C_Inner_Syntax.pref_lex name, pos_lex), ty)
          , ((C_Inner_Syntax.pref_bot name, pos_bot), ty)
          , ((C_Inner_Syntax.pref_top name, pos_top), ty) ])
        [ (("apply", \<^here>, \<^here>, \<^here>), Keyword.command_spec (Keyword.prf_script, ["proof"]))
        , (("by", \<^here>, \<^here>, \<^here>), Keyword.command_spec (Keyword.qed, ["proof"]))
        , (("done", \<^here>, \<^here>, \<^here>), Keyword.command_spec (Keyword.qed_script, ["proof"])) ])
\<close>

ML \<comment> \<open>\<^theory>\<open>Pure\<close>\<close> \<open>
local
val semi = Scan.option (C_Parse.$$$ ";");

structure C_Isar_Cmd = 
struct
fun ML source = ML_Context.exec (fn () =>
                   ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source) #>
                 Local_Theory.propagate_ml_env

fun theorem schematic ((long, binding, includes, elems, concl), (l_meth, o_meth)) int lthy =
     (if schematic then Specification.schematic_theorem_cmd else Specification.theorem_cmd)
       long Thm.theoremK NONE (K I) binding includes elems concl int lthy
  |> fold (fn m => tap (fn _ => Method.report m) #> Proof.apply m #> Seq.the_result "") l_meth
  |> (case o_meth of
        NONE => Proof.global_done_proof
      | SOME (m1, m2) =>
          tap (fn _ => (Method.report m1; Option.map Method.report m2))
          #> Proof.global_terminal_proof (m1, m2))

fun definition (((decl, spec), prems), params) =
  #2 oo Specification.definition_cmd decl params prems spec

fun declare (facts, fixes) =
  #2 oo Specification.theorems_cmd "" [(Binding.empty_atts, flat facts)] fixes
end

local
val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl));

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));
in
fun theorem spec schematic =
  C_Inner_Syntax.local_command'
    spec
    (fn name_pref =>
      (long_statement || short_statement)
      -- let val apply = Parse.$$$ (name_pref "apply") |-- Method.parse
         in Scan.repeat1 apply -- (Parse.$$$ (name_pref "done") >> K NONE)
         || Scan.repeat apply -- (Parse.$$$ (name_pref "by")
                                  |-- Method.parse -- Scan.option Method.parse >> SOME)
         end)
    (C_Isar_Cmd.theorem schematic)
end

val opt_modes =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

val _ = Theory.setup
 (   C_Inner_Syntax.command (C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup)
                            C_Parse.ML_source
                            ("\<approx>setup", \<^here>, \<^here>)
  #> C_Inner_Syntax.command0 (C_Inner_Toplevel.theory o Isar_Cmd.setup)
                             C_Parse.ML_source
                             ("setup", \<^here>, \<^here>, \<^here>)
  #> C_Inner_Syntax.command0 (C_Inner_Toplevel.generic_theory o C_Isar_Cmd.ML)
                             C_Parse.ML_source
                             ("ML", \<^here>, \<^here>, \<^here>)
  #> C_Inner_Syntax.command0 (C_Inner_Toplevel.generic_theory o C_Module.C)
                             C_Parse.C_source
                             ("C", \<^here>, \<^here>, \<^here>)
  #> C_Inner_Syntax.command0' (C_Inner_Toplevel.generic_theory o C_Inner_File.ML NONE)
                              Keyword.thy_load
                              (C_Resources.parse_file --| semi)
                              ("ML_file", \<^here>, \<^here>, \<^here>)
  #> C_Inner_Syntax.command0' (C_Inner_Toplevel.generic_theory o C_Inner_File.C)
                              Keyword.thy_load
                              (C_Resources.parse_file --| semi)
                              ("C_file", \<^here>, \<^here>, \<^here>)
  #> C_Inner_Syntax.command0 (C_Inner_Toplevel.generic_theory o C_Module.C_export_boot)
                             C_Parse.C_source
                             ("C_export_boot", \<^here>, \<^here>, \<^here>)
  #> C_Inner_Syntax.command_range'
                             (Context.map_theory o Named_Target.theory_map o C_Module.C_export_file)
                             ("C_export_file", \<^here>, \<^here>, \<^here>)
  #> C_Inner_Syntax.command_no_range
       (C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup
         \<open>fn ((_, (_, pos1, pos2)) :: _) =>
              (fn _ => fn _ =>
                tap (fn _ =>
                      Position.reports_text [((Position.range (pos1, pos2)
                                               |> Position.range_position, Markup.intensify), "")]))
           | _ => fn _ => fn _ => I\<close>)
       ("highlight", \<^here>, \<^here>)
  #> theorem ("theorem", \<^here>, \<^here>, \<^here>) false
  #> theorem ("lemma", \<^here>, \<^here>, \<^here>) false
  #> theorem ("corollary", \<^here>, \<^here>, \<^here>) false
  #> theorem ("proposition", \<^here>, \<^here>, \<^here>) false
  #> theorem ("schematic_goal", \<^here>, \<^here>, \<^here>) true
  #> C_Inner_Syntax.local_command''
      ("definition", \<^here>, \<^here>, \<^here>)
      (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
        Parse_Spec.if_assumes -- Parse.for_fixes)
      C_Isar_Cmd.definition
  #> C_Inner_Syntax.local_command''
      ("declare", \<^here>, \<^here>, \<^here>)
      (Parse.and_list1 Parse.thms1 -- Parse.for_fixes)
      C_Isar_Cmd.declare
  #> C_Inner_Syntax.command0
      (C_Inner_Toplevel.keep'' o C_Inner_Isar_Cmd.print_term)
      (C_Token.syntax' (opt_modes -- Parse.term))
      ("term", \<^here>, \<^here>, \<^here>))
in end
\<close>

subsection \<open>Definitions of Outer Classical Commands\<close>
subsubsection \<open>Library\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay
    Analogous to:
(*  Title:      Pure/Pure.thy
    Author:     Makarius

The Pure theory, with definitions of Isar commands and some lemmas.
*)*)

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/parse.ML\<close>\<close> \<open>
structure C_Outer_Parse =
struct
  val C_source = Parse.input (Parse.group (fn () => "C source") Parse.text)
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/outer_syntax.ML\<close>\<close> \<open>
structure C_Outer_Syntax =
struct
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C\<close> ""
    (C_Outer_Parse.C_source >> (Toplevel.generic_theory o C_Module.C));
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/isar_cmd.ML\<close>\<close> \<open>
structure C_Outer_Isar_Cmd =
struct
(* diagnostic ML evaluation *)

structure Diag_State = Proof_Data
(
  type T = Toplevel.state option;
  fun init _ = NONE;
);

fun C_diag source state =
  let
    val opt_ctxt =
      try Toplevel.generic_theory_of state
      |> Option.map (Context.proof_of #> Diag_State.put (SOME state));
  in Context.setmp_generic_context (Option.map Context.Proof opt_ctxt)
    (fn () => C_Module.eval_source source) () end;

fun diag_state ctxt =
  (case Diag_State.get ctxt of
    SOME st => st
  | NONE => Toplevel.init_toplevel ());

val diag_goal = Proof.goal o Toplevel.proof_of o diag_state;

val _ = Theory.setup
  (ML_Antiquotation.value (Binding.qualify true "Isar" \<^binding>\<open>C_state\<close>)
    (Scan.succeed "C_Outer_Isar_Cmd.diag_state ML_context") #>
   ML_Antiquotation.value (Binding.qualify true "Isar" \<^binding>\<open>C_goal\<close>)
    (Scan.succeed "C_Outer_Isar_Cmd.diag_goal ML_context"));

end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/ML/ml_file.ML\<close>\<close> \<open>
structure C_Outer_File =
struct

fun command_c ({src_path, lines, digest, pos}: Token.file) =
  let
    val provide = Resources.provide (src_path, digest);
  in I
    #> C_Module.C (Input.source true (cat_lines lines) (pos, pos))
    #> Context.mapping provide (Local_Theory.background_theory provide)
  end;

fun C get_file gthy =
  command_c (get_file (Context.theory_of gthy)) gthy;

end;
\<close>

subsubsection \<open>Initialization\<close>

ML \<comment> \<open>\<^theory>\<open>Pure\<close>\<close> \<open>
local

val semi = Scan.option \<^keyword>\<open>;\<close>;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C_file\<close> "read and evaluate Isabelle/C file"
    (Resources.parse_file --| semi >> (Toplevel.generic_theory o C_Outer_File.C));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C_export_boot\<close>
    "C text within theory or local theory, and export to bootstrap environment"
    (C_Outer_Parse.C_source >> (Toplevel.generic_theory o C_Module.C_export_boot));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C_prf\<close> "C text within proof"
    (C_Outer_Parse.C_source >> (Toplevel.proof o C_Module.C_prf));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>C_val\<close> "diagnostic C text"
    (C_Outer_Parse.C_source >> (Toplevel.keep o C_Outer_Isar_Cmd.C_diag));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>C_export_file\<close> "diagnostic C text"
    (Scan.succeed () >> K (C_Module.C_export_file Position.no_range));
in end\<close>

subsection \<open>Syntax for Pure Term\<close>

syntax "_C_translation_unit" :: \<open>cartouche_position \<Rightarrow> string\<close> ("\<^C>\<^sub>u\<^sub>n\<^sub>i\<^sub>t _")
syntax "_C_external_declaration" :: \<open>cartouche_position \<Rightarrow> string\<close> ("\<^C>\<^sub>d\<^sub>e\<^sub>c\<^sub>l _")
syntax "_C_expression" :: \<open>cartouche_position \<Rightarrow> string\<close> ("\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r _")
syntax "_C_statement" :: \<open>cartouche_position \<Rightarrow> string\<close> ("\<^C>\<^sub>s\<^sub>t\<^sub>m\<^sub>t _")
syntax "_C" :: \<open>cartouche_position \<Rightarrow> string\<close> ("\<^C> _")

parse_translation \<open>
C_Module.C_Term'.parse_translation
  [ (\<^syntax_const>\<open>_C_translation_unit\<close>, SOME C_Module.C_Term.tok_translation_unit)
  , (\<^syntax_const>\<open>_C_external_declaration\<close>, SOME C_Module.C_Term.tok_external_declaration)
  , (\<^syntax_const>\<open>_C_expression\<close>, SOME C_Module.C_Term.tok_expression)
  , (\<^syntax_const>\<open>_C_statement\<close>, SOME C_Module.C_Term.tok_statement)
  , (\<^syntax_const>\<open>_C\<close>, NONE) ]
\<close>

end
