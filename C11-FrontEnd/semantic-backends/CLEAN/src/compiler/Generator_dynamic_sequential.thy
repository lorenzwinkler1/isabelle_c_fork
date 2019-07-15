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

theory Generator_dynamic_sequential
  imports Init
begin

section \<open>\<^dir>\<open>../../../../../l4v/src\<close>\<close>
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

subsection \<open>\<^file>\<open>~~/src/HOL/Word/Word.thy\<close>\<close>

datatype 'a word = W

subsection \<open>\<^file>\<open>../../../../../l4v/src/lib/Word_Lib/Signed_Words.thy\<close>\<close>

locale Signed_Words
begin
datatype 'a signed = S
end

subsection \<open>\<^file>\<open>../../../../../l4v/src/tools/c-parser/Simpl/Vcg.thy\<close>\<close>

ML \<comment> \<open>\<^file>\<open>../../../../../l4v/src/tools/c-parser/Simpl/hoare.ML\<close>\<close> \<open>
structure Hoare = struct

val specL = "_spec";

datatype par_kind = In | Out

val deco = "_'";
val proc_deco = "_'proc";

fun varname x = x ^ deco

datatype 'a bodykind = BodyTyp of 'a | BodyTerm of 'a

end
\<close>

subsection \<open>\<^file>\<open>../../../../../l4v/src/tools/c-parser/umm_heap/$L4V_ARCH/ArchArraysMemInstance.thy\<close>\<close>

(* introduce hackish handling of 8192 type by making a copy of the type
   under a constructor, and then manually showing that it is an instance of
   array_max_count *)
datatype array_max_count_ty = array_max_count_ty (*"8192"*)

(* ML c-parser code also needs to know at which array size to use this type *)
ML \<open>
  structure ArchArrayMaxCount = struct
    val array_max_count = 8192
  end
\<close>

subsection \<open>\<^file>\<open>../../../../../l4v/src/tools/c-parser/CProof.thy\<close>\<close>

ML_file "../../../../../l4v/src/tools/c-parser/General.ML"
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/openUnsynch.ML\<close>\<close>
ML_file "../../../../../l4v/src/tools/c-parser/SourcePos.ML"
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/SourceFile.ML\<close>\<close>
ML_file "../../../../../l4v/src/tools/c-parser/Region.ML"
ML_file "../../../../../l4v/src/tools/c-parser/Binaryset.ML"
ML_file "../../../../../l4v/src/tools/c-parser/Feedback.ML"
ML_file "../../../../../l4v/src/tools/c-parser/basics.ML"
ML_file "../../../../../l4v/src/tools/c-parser/MString.ML"

ML_file "../../../../../l4v/src/tools/c-parser/TargetNumbers-sig.ML"
ML_file "../../../../../l4v/src/tools/c-parser/umm_heap/$L4V_ARCH/TargetNumbers.ML"

ML_file "../../../../../l4v/src/tools/c-parser/RegionExtras.ML"
ML_file "../../../../../l4v/src/tools/c-parser/Absyn-CType.ML"
ML_file "../../../../../l4v/src/tools/c-parser/Absyn-Expr.ML"
ML_file "../../../../../l4v/src/tools/c-parser/Absyn-StmtDecl.ML"
ML_file "../../../../../l4v/src/tools/c-parser/Absyn.ML"
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/Absyn-Serial.ML\<close>\<close>
ML_file "../../../../../l4v/src/tools/c-parser/name_generation.ML"

subsection \<open>\<^file>\<open>../../../../../l4v/src/tools/c-parser/CTranslation.thy\<close>\<close>

\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/tools/mlyacc/mlyacclib/MLY_base-sig.ML\<close>\<close>
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/tools/mlyacc/mlyacclib/MLY_join.ML\<close>\<close>
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/tools/mlyacc/mlyacclib/MLY_lrtable.ML\<close>\<close>
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/tools/mlyacc/mlyacclib/MLY_stream.ML\<close>\<close>
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/tools/mlyacc/mlyacclib/MLY_parser2.ML\<close>\<close>
ML_file "../../../../../l4v/src/tools/c-parser/FunctionalRecordUpdate.ML"
ML_file "../../../../../l4v/src/tools/c-parser/topo_sort.ML"
ML_file "toolkit/isa_termstypes.ML"
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/generated/tools/c-parser/StrictC.grm.sig\<close>\<close>
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/generated/tools/c-parser/StrictC.grm.sml\<close>\<close>
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/generated/tools/c-parser/StrictC.lex.sml\<close>\<close>
ML_file "../../../../../l4v/src/tools/c-parser/isar_pre_install.ML"
ML \<comment> \<open>\<^file>\<open>../../../../../l4v/src/tools/c-parser/StrictCParser.ML\<close>\<close> \<open>
structure StrictCParser =
struct
fun parse ast (env_lang : C_Env.env_lang) =
  C_Ast.main (ast, ( map_filter (fn C_Scan.Left {body_begin, body, body_end, range, ...} =>
                                    SOME (C_Grammar_Rule_Lib.make_comment body_begin body body_end range)
                                  | _ => NONE)
                                (#stream_ignored env_lang |> rev)
                   , []))
  |> IsarPreInstall.of_c_ast
end
\<close>
ML_file "../../../../../l4v/src/tools/c-parser/complit.ML"
ML \<comment> \<open>\<^file>\<open>../../../../../l4v/src/tools/c-parser/hp_termstypes.ML\<close>\<close> \<open>
structure HP_TermsTypes =
struct
val c_exntype_ty = \<^typ>\<open>bool\<close>
end
\<close>
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/termstypes-sig.ML\<close>\<close>
ML \<comment> \<open>\<^file>\<open>../../../../../l4v/src/tools/c-parser/termstypes.ML\<close>\<close> \<open>
structure TermsTypes = struct
open IsabelleTermsTypes open HP_TermsTypes
val mk_ptr_ty = I 
val symbol_table = Free ("symbol_table", \<^typ>\<open>string => string word\<close>)
end
structure IntInfo = struct fun ity2wty _ = \<^typ>\<open>bool\<close> end
\<close>
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/UMM_termstypes.ML\<close>\<close>
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/recursive_records/recursive_record_pp.ML\<close>\<close>
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/recursive_records/recursive_record_package.ML\<close>\<close>
ML_file "../../../../../l4v/src/tools/c-parser/expression_typing.ML"
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/UMM_Proofs.ML\<close>\<close>
ML_file "../../../../../l4v/src/tools/c-parser/program_analysis.ML"
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/heapstatetype.ML\<close>\<close>
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/MemoryModelExtras-sig.ML\<close>\<close>
ML \<comment> \<open>\<^file>\<open>../../../../../l4v/src/tools/c-parser/MemoryModelExtras.ML\<close>\<close> \<open>
structure MemoryModelExtras =
struct
val extended_heap_ty = \<^typ>\<open>bool\<close>
end
\<close>
ML_file "toolkit/calculate_state.ML"
ML_file "../../../../../l4v/src/tools/c-parser/syntax_transforms.ML"
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/expression_translation.ML\<close>\<close>
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/modifies_proofs.ML\<close>\<close>
ML_file "toolkit/HPInter.ML"
\<comment> \<open>Not loaded: \<^file>\<open>../../../../../l4v/src/tools/c-parser/stmt_translation.ML\<close>\<close>
ML \<comment> \<open>\<^file>\<open>../../../../../l4v/src/tools/c-parser/isar_install.ML\<close>\<close> \<open>
structure IsarInstall =
struct
fun setup_feedback extra_output_filename = let
    val trace_extra = case extra_output_filename of
        NONE => K ()
      | SOME f => let
        val out = TextIO.openOut f
      in fn s => (TextIO.output (out, s); TextIO.flushOut out) end
    val add_extra = case extra_output_filename of
        NONE => (fn pfx => fn f => f)
      | SOME _ => (fn pfx => fn f => fn s => (trace_extra (pfx ^ s); f s))
  in
    Feedback.errorf := add_extra "ERROR: " (ignore o error);
    Feedback.warnf := add_extra "" warning;
    Feedback.informf := add_extra "" (Output.tracing o Feedback.timestamp)
  end

val _ = setup_feedback NONE

fun get_Csyntax ast env_lang =
     StrictCParser.parse ast env_lang
  |> SyntaxTransforms.remove_anonstructs
  |> SyntaxTransforms.remove_typedefs

fun print_addressed_vars cse = let
  open ProgramAnalysis Feedback
  val globs = get_globals cse
  val _ = informStr (0, "There are "^Int.toString (length globs)^" globals: "^
                        commas_quote (map srcname globs))
  val addressed = get_addressed cse
  val addr_vars = map MString.dest (MSymTab.keys addressed)
  val _ = informStr (0, "There are "^Int.toString (length addr_vars)^
                        " addressed variables: "^ commas_quote addr_vars)
in
  ()
end

fun install_C_file0 ast env_lang =
  get_Csyntax ast env_lang
  |> (fn ast =>
  let
  val owners =
      (* non-null if there are any globals that have owned_by annotations *)
      let
        open StmtDecl RegionExtras
        fun getowner d =
            case d of
                Decl d =>
                (case node d of
                     VarDecl (_, _, _, _, attrs) => get_owned_by attrs
                   | _ => NONE)
              | _ => NONE
      in
        List.mapPartial getowner ast
      end
  val ((ast, _ (* init_stmts *)), cse) = 
      ProgramAnalysis.process_decls {anon_vars=false, owners = owners,
                     allow_underscore_idents = false,
                     munge_info_fname = NONE}
                    ast

  val _ = print_addressed_vars cse
  val ecenv = ProgramAnalysis.cse2ecenv cse

  val state = CalculateState.create_state cse
  val (_, rcdinfo) = CalculateState.mk_thy_types cse false \<^theory>
  val ast = SyntaxTransforms.remove_embedded_fncalls cse ast
  (**)
      val (_, vdecls, globs) =
          CalculateState.mk_thy_decls
            state {owners=owners,gstate_ty= \<^typ>\<open>bool\<close>,mstate_ty= \<^typ>\<open>bool\<close>} \<^theory>
      val _ = Output.state ("Created locale for globals (" ^ "..." ^
                       ")- with " ^ Int.toString (length globs) ^
                       " globals elements")
      val _ = app (fn e => Output.state ("-- " ^ HPInter.asm_to_string (Syntax.string_of_term \<^context>) e))
                  globs

      val _ =
                Feedback.informStr (0,
                    "Ignoring initialisations of modified globals (if any)")
      val toTranslate = NONE
      val toTranslate_s =
          case toTranslate of
              NONE => "all functions"
            | SOME set => "functions " ^
                          String.concatWith ", " (Binaryset.listItems set) ^
                          " (derived from "^
                          "..." ^ ")"
      val _ =
          Feedback.informStr (0, "Beginning function translation for " ^
                    toTranslate_s)
      val toTranslateP =
          case toTranslate of
              NONE => (fn _ => true)
            | SOME set => (fn s => Binaryset.member(set,s))
      val fninfo : HPInter.fninfo list = HPInter.mk_fninfo \<^theory> cse toTranslateP ast
  in
    tap (fn _ => writeln (\<^make_string> (ast, cse, ecenv, state, rcdinfo, vdecls, globs, fninfo)))
  end)

end
\<close>

section \<open>Setup of \<^theory_text>\<open>C\<close> commands\<close>

ML \<comment> \<open>\<^theory>\<open>C.C_Command\<close>\<close> \<open>
val clean_C99 = Attrib.setup_config_bool @{binding CLEAN_C99} (K false)

val _ =
  Theory.setup
    (Context.theory_map
      (C_Module.Data_Accept.put
        (fn ast => fn env_lang => fn context =>
          if Config.get (Context.proof_of context) clean_C99 then
            IsarInstall.install_C_file0 ast env_lang context
          else
            context)))
\<close>

end
