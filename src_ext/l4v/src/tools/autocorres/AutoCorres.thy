(*
 * Portions Copyright 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Top-level AutoCorres theorem.
 *)

theory AutoCorres
imports
  SimplConv
  ExceptionRewrite
  L1Valid
  LocalVarExtract
  L2Peephole
  L2Opt
  TypeStrengthen
  Polish
  TypHeapSimple
  HeapLift
  WordAbstract
  "Lib.OptionMonadWP"
  "Lib.Apply_Trace"
  AutoCorresSimpset
  "Lib.MkTermAntiquote"
  "Lib.TermPatternAntiquote"
  keywords "autocorres"
           "autocorres'"
           "install_autocorres_file" :: thy_load % "ML"
  and      "install_autocorres" :: thy_decl % "ML"
  and      "declare_autocorres" :: thy_decl
begin

(* Remove various rules from the default simpset that don't really help. *)
declare word_neq_0_conv [simp del]
declare neq0_conv [simp del]
declare fun_upd_apply[simp del]
declare of_int_and_nat[simp del]

(* Remove wp combinators which are problematic for AutoCorres
   and restore some prior configuration. *)
declare hoare_wp_combsE [wp del, wp_comb del]
declare hoare_wp_combs [wp del, wp_comb del]
declare hoare_wp_state_combsE [wp del, wp_comb del]

lemmas hoare_wp_combsE_autocorres [wp_comb]
    = hoare_vcg_precond_impE hoare_vcg_precond_impE_R validE_validE_R
lemmas hoare_wp_combs_autocorres [wp_comb]
    = hoare_vcg_precond_imp
declare validNF_weaken_pre[wp_comb]
declare validE_NF_weaken_pre[wp_comb]
bundle nf_no_pre
    = validNF_weaken_pre[wp_pre del] validE_NF_weaken_pre[wp_pre del]



(* Machinery for generating final corres thm *)
lemma corresTA_trivial: "corresTA (\<lambda>_. True) (\<lambda>x. x) (\<lambda>x. x) A A"
  apply (auto intro: corresXF_I)
  done

(* Dummy preconditions for more convenient usage *)
lemma L2Tcorres_trivial_from_local_var_extract:
  "L2corres st rx ex P A C \<Longrightarrow> L2Tcorres id A A"
  by (rule L2Tcorres_id)

lemma corresTA_trivial_from_heap_lift:
  "L2Tcorres st A C \<Longrightarrow> corresTA (\<lambda>_. True) (\<lambda>x. x) (\<lambda>x. x) A A"
  by (rule corresTA_trivial)


lemma corresXF_from_L2_call:
  "L2_call c_WA = A \<Longrightarrow> corresXF (\<lambda>s. s) (\<lambda>rv s. rv) y (\<lambda>_. True) A c_WA"
  apply (clarsimp simp: corresXF_def L2_call_def L2_defs)
  apply (monad_eq split: sum.splits)
  apply force
  done

(* The final ac_corres theorem. *)
lemma ac_corres_chain:
"\<lbrakk> L1corres check_termination Gamma c_L1 c;
   L2corres st_L2 rx_L2 (\<lambda>_. ()) P_L2 c_L2 c_L1;
   L2Tcorres st_HL c_HL c_L2;
   corresTA P_WA rx_WA ex_WA c_WA c_HL;
   L2_call c_WA = A
 \<rbrakk> \<Longrightarrow>
  ac_corres (st_HL o st_L2) check_termination Gamma (rx_WA o rx_L2) (P_L2 and (P_WA o st_HL o st_L2)) A c"
  apply (rule ccorresE_corresXF_merge)
       apply (unfold L1corres_alt_def)
       apply assumption
      apply (unfold L2corres_def L2Tcorres_def corresTA_def)
      apply (drule corresXF_from_L2_call)
      apply ((drule (1) corresXF_corresXF_merge)+, assumption)
     apply (clarsimp simp: L2_call_def L2_defs)
     apply (rule handleE'_nothrow_rhs)
     apply simp
    apply clarsimp
   apply clarsimp
  apply clarsimp
  done

(*
 * Functions that don't have a body in the C file (i.e., they are
 * prototyped and called, but are never defined) will be abstracted
 * into a "fail" command by AutoCorres.
 *
 * More accurately, they will be abstracted into:
 *
 *     guard (\<lambda>s. INVALID_FUNCTION)
 *
 * where "INVALID_FUNCTION" is "False").
 *
 * We convert this above form into this alternative definition, so
 * users have a better idea what is going on.
 *)
definition "FUNCTION_BODY_NOT_IN_INPUT_C_FILE \<equiv> fail"

lemma [polish]:
  "guard (\<lambda>s. UNDEFINED_FUNCTION) \<equiv> FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "(FUNCTION_BODY_NOT_IN_INPUT_C_FILE >>= m) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "unknown >>= (\<lambda>x. FUNCTION_BODY_NOT_IN_INPUT_C_FILE) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  "unknown >>= (K_bind FUNCTION_BODY_NOT_IN_INPUT_C_FILE) = FUNCTION_BODY_NOT_IN_INPUT_C_FILE"
  by (monad_eq simp: UNDEFINED_FUNCTION_def FUNCTION_BODY_NOT_IN_INPUT_C_FILE_def)+

(* Rewrites that will be applied before collecting statistics. *)
lemmas ac_statistics_rewrites =
    (* Setup "L1_seq" to have a sane lines-of-spec measurement. *)
    L1_seq_def bindE_K_bind [THEN eq_reflection]
    (* Convert L2 to standard exception monads. *)
    L2_defs'

(* Utils *)
ML_file "../../lib/set.ML"
ML_file "trace_antiquote.ML"
ML_file "utils.ML"

(* Common data structures *)
ML_file "program_info.ML"
ML_file "function_info.ML"
ML_file "autocorres_trace.ML"
ML_file "autocorres_data.ML"

(* Common control code *)
ML_file "autocorres_util.ML"

(* L1 *)
ML_file "exception_rewrite.ML"
ML_file "simpl_conv.ML"
(* L2 *)
ML_file "prog.ML"
ML_file "l2_opt.ML"
ML_file "local_var_extract.ML"
(* HL *)
ML_file "record_utils.ML"
ML_file "heap_lift_base.ML"
ML_file "heap_lift.ML"
(* WA *)
ML_file "word_abstract.ML"
ML_file "pretty_bound_var_names.ML"
ML_file "monad_convert.ML"
(* TS *)
ML_file "type_strengthen.ML"

ML_file "autocorres.ML"

(* Setup "autocorres" keyword. *)
ML \<open>
val do_autocorres = 
  Toplevel.theory
  o (fn (opt, filename) => fn thy =>
      AutoCorres.do_autocorres opt (IsarPreInstall.mk_thy_relative' filename thy
                                    |> (fn (_, s) =>
                                         (Binding.make (#base (OS.Path.splitBaseExt (OS.Path.file s)), Position.none), s))) thy)

val do_install_autocorres =
  Toplevel.theory
    o (fn (opt, input) => IsarInstall.install_C_file input #-> AutoCorres.do_autocorres opt)

val _ =
  Outer_Syntax.command @{command_keyword "autocorres"}
    "Abstract the output of the C parser into a monadic representation."
    (AutoCorres.Parser_Outer.autocorres_parser >> do_autocorres)
val _ =
  Outer_Syntax.command @{command_keyword "autocorres'"}
    "Abstract the output of the C parser into a monadic representation."
    (AutoCorres.Parser_Outer.autocorres_parser' >> do_autocorres)
val _ =
  Outer_Syntax.command @{command_keyword "install_autocorres"}
    "Install the C code, and abstract the output of the C parser into a monadic representation."
    (AutoCorres.Parser_Outer.autocorres_parser'' (Parse.binding -- C_Outer_Parse.C_source >> C_Scan.Right) >> do_install_autocorres)
val _ =
  Outer_Syntax.command @{command_keyword "install_autocorres_file"}
    "Install the C file, and abstract the output of the C parser into a monadic representation."
    (AutoCorres.Parser_Outer.autocorres_parser'' (Resources.parse_file >> C_Scan.Left) >> do_install_autocorres)
\<close>

ML \<open>
datatype declare_autocorres =
    Decl_param of (binding * (AutoCorres.autocorres_options * unit IsarInstall.install_C0))
  | Decl_none
  | Decl_inner

structure Data_autocorres =
  Generic_Data
    (struct
      type T = declare_autocorres
      val empty = Decl_none
      val extend = I
      val merge = fn (x, Decl_none) => x
                   | (x, Decl_inner) => x
                   | (_, x) => x
     end)

local

fun bind scan f ((stack1, (to_delay, stack2)), _) =
  C_Parse.range scan
  >> (fn (src, range) =>
      C_Env.Parsing
        ( (stack1, stack2)
        , ( range
          , C_Inner_Syntax.bottom_up (f src)
          , Symtab.empty
          , to_delay)))

fun command f name =
  C_Annotation.command'
    name
    ""
    (bind (C_Parse.binding -- (AutoCorres.Parser_Inner.autocorres_parser'' (Scan.succeed ()))) f)

val cmd = ("install_autocorres", \<^here>)

val autocorres = Attrib.setup_config_bool @{binding AutoCorres} (K false)

fun exec_autocorres (name, (opt, input)) context =
  Context.setmp_generic_context (* Isabelle/C sub context parsing *)
    (SOME context)
    (Context.map_theory
      (C_Annotation.delete_command cmd
       #> IsarInstall.install_C_file
            (IsarInstall.make_install_C
              (C_Scan.Right (name, hd (C_Module.Data_In_Source.get context)))
              (case input of ((((((((SOME false, _), _), _), _), _), _), _), _) => input
               | ((((((((NONE,no_cpp),parse_stop),sub_decl),memsafe),ctyps),cdefs),files),statetylist_opt) =>
                   tap (fn _ => tracing "Disabling the second C11 parsing layer to avoid a double reporting of the source")
                       ((((((((SOME false,no_cpp),parse_stop),sub_decl),memsafe),ctyps),cdefs),files),statetylist_opt)
               | _ => tap (fn _ => warning "Potential double reporting of the source (by the outer C11 parser, and inner C11 one)") input))
       #-> AutoCorres.do_autocorres opt))
    context

fun warn_no_autocorres () =
  warning ("AutoCorres is not activated" ^ Position.here (Config.pos_of autocorres))

in

val () =
  Outer_Syntax.command @{command_keyword declare_autocorres} "declare AutoCorres arguments provided to C"
    (Parse.binding -- (AutoCorres.Parser_Outer.autocorres_parser'' (Scan.succeed ()))
      >> (Toplevel.generic_theory o
           (fn data =>
             tap (fn context =>
                   if Config.get (Context.proof_of context) autocorres
                   then ()
                   else warn_no_autocorres ())
             #>
             Data_autocorres.map (K (Decl_param data)))))

val _ =
  Theory.setup
    (command
      (fn data => fn _ => fn context =>
        context
        |> (if Config.get (Context.proof_of context) autocorres then
              exec_autocorres data
              #> Data_autocorres.put Decl_inner
            else
              tap (fn _ => warn_no_autocorres ())))
      cmd
     #> Context.theory_map
      (C_Module.Data_Accept.put
        (fn _ => fn _ => fn context =>
          if Config.get (Context.proof_of context) autocorres then
            case Data_autocorres.get context of
              Decl_none => tap (fn _ => warning let val (name, pos) = @{command_keyword declare_autocorres} in "AutoCorres not yet initialized with " ^ name ^ Position.here pos end) context
            | Decl_inner => Data_autocorres.put Decl_none context
            | Decl_param data => exec_autocorres data context
          else
            context)))

end
\<close>

end
