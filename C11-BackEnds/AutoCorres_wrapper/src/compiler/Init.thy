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

chapter \<open>Appendix: Isabelle/C/AutoCorres Annotations\<close>

theory Init
  imports "HOL-Eisbach.Eisbach"
          Isabelle_C.C_Main
begin

section \<open>\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/args.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay
    Analogous to:
(*  Title:      Pure/Isar/args.ML
    Author:     Markus Wenzel, TU Muenchen

Quasi-inner syntax based on outer tokens: concrete argument syntax of
attributes, methods etc.
*)*)
\<open>
structure Args' =
struct
val var =
  (Parse.token Parse.term >> Token.content_of) :|-- (fn x =>
    (case Lexicon.read_variable x of SOME v => Scan.succeed v | NONE => Scan.fail));
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Tools/rule_insts.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay
    Analogous to:
(*  Title:      Pure/Tools/rule_insts.ML
    Author:     Makarius

Rule instantiations -- operations within implicit rule / subgoal context.
*)*)
\<open>
structure Rule_Insts' =
struct

(** read instantiations **)

local

fun error_var msg (xi, pos) =
  error (msg ^ quote (Term.string_of_vname xi) ^ Position.here pos);

fun the_sort tvars (ai, pos) : sort =
  (case TVars.get_first (fn ((bi, S), _) => if ai = bi then SOME S else NONE) tvars of
    SOME S => S
  | NONE => error_var "No such type variable in theorem: " (ai, pos));

fun the_type vars (xi, pos) : typ =
  (case Vartab.lookup vars xi of
    SOME T => T
  | NONE => error_var "No such variable in theorem: " (xi, pos));

fun read_type ctxt tvars ((xi, pos), s) =
  let
    val S = the_sort tvars (xi, pos);
    val T = Syntax.read_typ ctxt s;
  in
    if Sign.of_sort (Proof_Context.theory_of ctxt) (T, S) then ((xi, S), T)
    else error_var "Bad sort for instantiation of type variable: " (xi, pos)
  end;

fun make_instT f (tvars: TVars.set) =
  let
    fun add v =
      let
        val T = TVar v;
        val T' = f T;
      in if T = T' then I else cons (v, T') end;
  in TVars.fold (add o #1) tvars [] end;

fun make_inst f vars =
  let
    fun add v =
      let
        val t = Var v;
        val t' = f t;
      in if t aconv t' then I else cons (v, t') end;
  in fold add vars [] end;

fun read_terms ss Ts ctxt =
  let
    fun parse T = if T = propT then Syntax.parse_prop ctxt else Syntax.parse_term ctxt;
    val (ts, ctxt') = fold_map Variable.fix_dummy_patterns (map2 parse Ts ss) ctxt;
    val ts' =
      map2 (Type.constraint o Type_Infer.paramify_vars) Ts ts
      |> Syntax.check_terms ctxt'
      |> Variable.polymorphic ctxt';
    val Ts' = map Term.fastype_of ts';
    val tyenv = Vartab.build (fold (Sign.typ_match (Proof_Context.theory_of ctxt)) (Ts ~~ Ts'));
    val tyenv' = Vartab.fold (fn (xi, (S, T)) => cons ((xi, S), T)) tyenv [];
  in ((ts', tyenv'), ctxt') end;

in

fun read_term s ctxt =
  let
    val (t, ctxt') = Variable.fix_dummy_patterns (Syntax.parse_term ctxt s) ctxt;
    val t' = Syntax.check_term ctxt' t;
  in (t', ctxt') end;

fun read_insts thm raw_insts raw_fixes ctxt =
  let
    val (type_insts, term_insts) =
      List.partition (fn (((x, _), _), _) => String.isPrefix "'" x) raw_insts;

    val tvars = TVars.build (Thm.fold_terms {hyps = false} TVars.add_tvars thm);
    val vars = Vars.build (Thm.fold_terms {hyps = false} Vars.add_vars thm);

    (*eigen-context*)
    val (_, ctxt1) = ctxt
      |> TVars.fold (Variable.declare_internal o Logic.mk_type o TVar o #1) tvars
      |> Vars.fold (Variable.declare_internal o Var o #1) vars
      |> Proof_Context.add_fixes_cmd raw_fixes;

    (*explicit type instantiations*)
    val instT1 =
      Term_Subst.instantiateT (TVars.make (map (read_type ctxt1 tvars) type_insts));
    val vars1 =
      Vartab.build (vars |> Vars.fold (fn ((v, T), _) =>
        Vartab.insert (K true) (v, instT1 T)));

    (*term instantiations*)
    val (xs, ss) = split_list term_insts;
    val Ts = map (the_type vars1) xs;
    val ((ts, inferred), ctxt2) = read_terms ss Ts ctxt1;

    (*implicit type instantiations*)
    val instT2 = Term_Subst.instantiateT (TVars.make inferred);
    val vars2 = Vartab.fold (fn (v, T) => cons (v, instT2 T)) vars1 [];
    val inst2 =
      Term_Subst.instantiate (TVars.empty,
        Vars.build (fold2 (fn (xi, _) => fn t => Vars.add ((xi, Term.fastype_of t), t)) xs ts))
      #> Envir.beta_norm;

    val inst_tvars = make_instT (instT2 o instT1) tvars;
    val inst_vars = make_inst inst2 vars2;
  in ((inst_tvars, inst_vars), ctxt2) end;

end;



(** forward rules **)

fun where_rule ctxt raw_insts raw_fixes thm =
  let
    val ((inst_tvars, inst_vars), ctxt') = read_insts thm raw_insts raw_fixes ctxt;
  in
    thm
    |> Drule.instantiate_normalize
      (TVars.make (map (apsnd (Thm.ctyp_of ctxt')) inst_tvars),
       Vars.make (map (apsnd (Thm.cterm_of ctxt')) inst_vars))
    |> singleton (Variable.export ctxt' ctxt)
    |> Rule_Cases.save thm
  end;

fun of_rule ctxt (args, concl_args) fixes thm =
  let
    fun zip_vars _ [] = []
      | zip_vars (_ :: xs) (NONE :: rest) = zip_vars xs rest
      | zip_vars ((x, _) :: xs) (SOME t :: rest) = ((x, Position.none), t) :: zip_vars xs rest
      | zip_vars [] _ = error "More instantiations than variables in theorem";
    val insts =
      zip_vars (Vars.build (Vars.add_vars (Thm.full_prop_of thm)) |> Vars.list_set) args @
      zip_vars (Vars.build (Vars.add_vars (Thm.concl_of thm)) |> Vars.list_set) concl_args;
  in where_rule ctxt insts fixes thm end;

fun read_instantiate ctxt insts xs =
  where_rule ctxt insts (map (fn x => (Binding.name x, NONE, NoSyn)) xs);



(** attributes **)

(* where: named instantiation *)

val named_insts =
  Parse.and_list1
    (Parse.position Args'.var -- (Args.$$$ "=" |-- Parse.!!! Parse.embedded_inner_syntax))
    -- Parse.for_fixes;

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>where\<close>
    (Scan.lift named_insts >> (fn args =>
      Thm.rule_attribute [] (fn context => uncurry (where_rule (Context.proof_of context)) args)))
    "named instantiation of theorem");


(* of: positional instantiation (terms only) *)

local

val inst = Args.maybe Parse.embedded_inner_syntax;
val concl = Args.$$$ "concl" -- Args.colon;

val insts =
  Scan.repeat (Scan.unless concl inst) --
  Scan.optional (concl |-- Scan.repeat inst) [];

in

val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>of\<close>
    (Scan.lift (insts -- Parse.for_fixes) >> (fn args =>
      Thm.rule_attribute [] (fn context => uncurry (of_rule (Context.proof_of context)) args)))
    "positional instantiation of theorem");

end;



(** tactics **)

(* goal context *)

fun goal_context goal ctxt =
  let
    val ((_, params), ctxt') = ctxt
      |> Variable.declare_constraints goal
      |> Variable.improper_fixes
      |> Variable.focus_params NONE goal
      ||> Variable.restore_proper_fixes ctxt;
  in (params, ctxt') end;


(* resolution after lifting and instantiation; may refer to parameters of the subgoal *)

fun bires_inst_tac bires_flag ctxt raw_insts raw_fixes thm i st = CSUBGOAL (fn (cgoal, _) =>
  let
    (*goal context*)
    val (params, goal_ctxt) = goal_context (Thm.term_of cgoal) ctxt;
    val paramTs = map #2 params;

    (*instantiation context*)
    val ((inst_tvars, inst_vars), inst_ctxt) = read_insts thm raw_insts raw_fixes goal_ctxt;
    val fixed = map #1 (fold (Variable.add_newly_fixed inst_ctxt goal_ctxt o #2) inst_vars []);


    (* lift and instantiate rule *)

    val inc = Thm.maxidx_of st + 1;
    val lift_type = Logic.incr_tvar inc;
    fun lift_var ((a, j), T) = ((a, j + inc), paramTs ---> lift_type T);
    fun lift_term t = fold_rev Term.absfree params (Logic.incr_indexes (fixed, paramTs, inc) t);

    val inst_tvars' =
      TVars.build (inst_tvars |> fold (fn (((a, i), S), T) =>
        TVars.add (((a, i + inc), S), Thm.ctyp_of inst_ctxt (lift_type T))));
    val inst_vars' =
      Vars.build (inst_vars |> fold (fn (v, t) =>
        Vars.add (lift_var v, Thm.cterm_of inst_ctxt (lift_term t))));

    val thm' = Thm.lift_rule cgoal thm
      |> Drule.instantiate_normalize (inst_tvars', inst_vars')
      |> singleton (Variable.export inst_ctxt ctxt);
  in compose_tac ctxt (bires_flag, thm', Thm.nprems_of thm) i end) i st;

val res_inst_tac = bires_inst_tac false;
val eres_inst_tac = bires_inst_tac true;


(* forward resolution *)

fun make_elim_preserve ctxt rl =
  let
    val maxidx = Thm.maxidx_of rl;
    fun var x = ((x, 0), propT);
    fun cvar xi = Thm.cterm_of ctxt (Var (xi, propT));
    val revcut_rl' =
      Drule.revcut_rl |> Drule.instantiate_normalize
        (TVars.empty, Vars.make [(var "V", cvar ("V", maxidx + 1)), (var "W", cvar ("W", maxidx + 1))]);
  in
    (case Seq.list_of
      (Thm.bicompose (SOME ctxt) {flatten = true, match = false, incremented = false}
        (false, rl, Thm.nprems_of rl) 1 revcut_rl')
     of
      [th] => th
    | _ => raise THM ("make_elim_preserve", 1, [rl]))
  end;

(*instantiate and cut -- for atomic fact*)
fun cut_inst_tac ctxt insts fixes rule =
  res_inst_tac ctxt insts fixes (make_elim_preserve ctxt rule);

(*forward tactic applies a rule to an assumption without deleting it*)
fun forw_inst_tac ctxt insts fixes rule =
  cut_inst_tac ctxt insts fixes rule THEN' assume_tac ctxt;

(*dresolve tactic applies a rule to replace an assumption*)
fun dres_inst_tac ctxt insts fixes rule =
  eres_inst_tac ctxt insts fixes (make_elim_preserve ctxt rule);


(* derived tactics *)

(*deletion of an assumption*)
fun thin_tac ctxt s fixes =
  eres_inst_tac ctxt [((("V", 0), Position.none), s)] fixes Drule.thin_rl;

(*Introduce the given proposition as lemma and subgoal*)
fun subgoal_tac ctxt A fixes =
  DETERM o res_inst_tac ctxt [((("psi", 0), Position.none), A)] fixes cut_rl;


(* method wrapper *)

fun method inst_tac tac =
  Args.goal_spec -- Scan.optional (Scan.lift (named_insts --| Args.$$$ "in")) ([], []) --
  Attrib.thms >> (fn ((quant, (insts, fixes)), thms) => fn ctxt => METHOD (fn facts =>
    if null insts andalso null fixes
    then quant (Method.insert_tac ctxt facts THEN' tac ctxt thms)
    else
      (case thms of
        [thm] => quant (Method.insert_tac ctxt facts THEN' inst_tac ctxt insts fixes thm)
      | _ => error "Cannot have instantiations with multiple rules")));


(* setup *)

(*warning: rule_tac etc. refer to dynamic subgoal context!*)

val _ = Theory.setup
 (Method.setup \<^binding>\<open>rule_tac\<close> (method res_inst_tac resolve_tac)
    "apply rule (dynamic instantiation)" #>
  Method.setup \<^binding>\<open>erule_tac\<close> (method eres_inst_tac eresolve_tac)
    "apply rule in elimination manner (dynamic instantiation)" #>
  Method.setup \<^binding>\<open>drule_tac\<close> (method dres_inst_tac dresolve_tac)
    "apply rule in destruct manner (dynamic instantiation)" #>
  Method.setup \<^binding>\<open>frule_tac\<close> (method forw_inst_tac forward_tac)
    "apply rule in forward manner (dynamic instantiation)" #>
  Method.setup \<^binding>\<open>cut_tac\<close> (method cut_inst_tac (K cut_rules_tac))
    "cut rule (dynamic instantiation)" #>
  Method.setup \<^binding>\<open>subgoal_tac\<close>
    (Args.goal_spec -- Scan.lift (Scan.repeat1 Parse.embedded_inner_syntax -- Parse.for_fixes) >>
      (fn (quant, (props, fixes)) => fn ctxt =>
        SIMPLE_METHOD'' quant (EVERY' (map (fn prop => subgoal_tac ctxt prop fixes) props))))
    "insert subgoal (dynamic instantiation)" #>
  Method.setup \<^binding>\<open>thin_tac\<close>
    (Args.goal_spec -- Scan.lift (Parse.embedded_inner_syntax -- Parse.for_fixes) >>
      (fn (quant, (prop, fixes)) => fn ctxt => SIMPLE_METHOD'' quant (thin_tac ctxt prop fixes)))
    "remove premise (dynamic instantiation)");

end;
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/HOL/Eisbach/eisbach_rule_insts.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay
    Analogous to:
(*  Title:      HOL/Eisbach/eisbach_rule_insts.ML
    Author:     Daniel Matichuk, NICTA/UNSW

Eisbach-aware variants of the "where" and "of" attributes.

Alternate syntax for rule_insts.ML participates in token closures by
examining the behaviour of Rule_Insts.where_rule and instantiating token
values accordingly. Instantiations in re-interpretation are done with
infer_instantiate.
*)*)
\<open>
structure Eisbach_Rule_Insts' =
struct

fun restore_tags thm = Thm.map_tags (K (Thm.get_tags thm));

val mk_term_type_internal = Logic.protect o Logic.mk_term o Logic.mk_type;

fun term_type_cases f g t = 
  (case \<^try>\<open>Logic.dest_type (Logic.dest_term (Logic.unprotect t))\<close> of
    SOME T => f T
  | NONE =>
      (case \<^try>\<open>Logic.dest_term t\<close> of
        SOME t => g t
      | NONE => raise Fail "Lost encoded instantiation"))

fun add_thm_insts ctxt thm =
  let
    val tyvars = Thm.fold_terms {hyps = false} Term.add_tvars thm [];
    val tyvars' = tyvars |> map (mk_term_type_internal o TVar);

    val tvars = Thm.fold_terms {hyps = false} Term.add_vars thm [];
    val tvars' = tvars  |> map (Logic.mk_term o Var);

    val conj =
      Logic.mk_conjunction_list (tyvars' @ tvars') |> Thm.cterm_of ctxt |> Drule.mk_term;
  in
    ((tyvars, tvars), Conjunction.intr thm conj)
  end;

fun get_thm_insts thm =
  let
    val (thm', insts) = Conjunction.elim thm;

    val insts' = insts
      |> Drule.dest_term
      |> Thm.term_of
      |> Logic.dest_conjunction_list
      |> (fn f => fold (fn t => fn (tys, ts) =>
          term_type_cases (fn T => (T :: tys, ts)) (fn t => (tys, t :: ts)) t) f ([], []))
      ||> rev
      |>> rev;
  in
    (thm', insts')
  end;

fun instantiate_xis ctxt insts thm =
  let
    val tyvars = Thm.fold_terms {hyps = false} Term.add_tvars thm [];
    val tvars = Thm.fold_terms {hyps = false} Term.add_vars thm [];

    fun add_inst (xi, t) (Ts, ts) =
      (case AList.lookup (op =) tyvars xi of
        SOME S => (((xi, S), Thm.ctyp_of ctxt (Logic.dest_type t)) :: Ts, ts)
      | NONE =>
          (case AList.lookup (op =) tvars xi of
            SOME _ => (Ts, (xi, Thm.cterm_of ctxt t) :: ts)
          | NONE => error "indexname not found in thm"));

    val (instT, inst) = fold add_inst insts ([], []);
  in
    (Thm.instantiate (TVars.make instT, Vars.empty) thm
    |> infer_instantiate ctxt inst
    COMP_INCR asm_rl)
    |> Thm.adjust_maxidx_thm ~1
    |> restore_tags thm
  end;


datatype rule_inst =
  Named_Insts of ((indexname * string) * (term -> unit)) list * (binding * string option * mixfix) list
| Term_Insts of (indexname * term) list
| Unchecked_Term_Insts of term option list * term option list;

fun mk_pair (t, t') = Logic.mk_conjunction (Logic.mk_term t, Logic.mk_term t');

fun dest_pair t = apply2 Logic.dest_term (Logic.dest_conjunction t);

fun embed_indexname ((xi, s), f) =
  let fun wrap_xi xi t = mk_pair (Var (xi, fastype_of t), t);
  in ((xi, s), f o wrap_xi xi) end;

fun unembed_indexname t = dest_pair t |> apfst (Term.dest_Var #> fst);

fun read_where_insts (insts, fixes) =
  let
    val insts' =
      if forall (fn (_, v) => Parse_Tools.is_real_val v) insts
      then Term_Insts (map (unembed_indexname o Parse_Tools.the_real_val o snd) insts)
      else
        Named_Insts (map (fn (xi, p) => embed_indexname
          ((xi, Parse_Tools.the_parse_val p), Parse_Tools.the_parse_fun p)) insts, fixes);
  in insts' end;

fun of_rule thm  (args, concl_args) =
  let
    fun zip_vars _ [] = []
      | zip_vars (_ :: xs) (NONE :: rest) = zip_vars xs rest
      | zip_vars ((x, _) :: xs) (SOME t :: rest) = (x, t) :: zip_vars xs rest
      | zip_vars [] _ = error "More instantiations than variables in theorem";
    val insts =
      zip_vars (rev (Term.add_vars (Thm.full_prop_of thm) [])) args @
      zip_vars (rev (Term.add_vars (Thm.concl_of thm) [])) concl_args;
  in insts end;

val inst =  Args.maybe Parse_Tools.name_term;
val concl = Args.$$$ "concl" -- Args.colon;

fun close_unchecked_insts context ((insts, concl_inst), fixes) =
  let
    val ctxt = Context.proof_of context;
    val ctxt1 = ctxt |> Proof_Context.add_fixes_cmd fixes |> #2;

    val insts' = insts @ concl_inst;

    val term_insts =
      map (the_list o (Option.map Parse_Tools.the_parse_val)) insts'
      |> burrow (Syntax.read_terms ctxt1 #> Variable.export_terms ctxt1 ctxt)
      |> map (try the_single);

    val _ =
      (insts', term_insts)
      |> ListPair.app (fn (SOME p, SOME t) => Parse_Tools.the_parse_fun p t | _ => ());
    val (insts'', concl_insts'') = chop (length insts) term_insts;
   in Unchecked_Term_Insts (insts'', concl_insts'') end;

fun read_of_insts checked context ((insts, concl_insts), fixes) =
  if forall (fn SOME t => Parse_Tools.is_real_val t | NONE => true) (insts @ concl_insts)
  then
    if checked
    then
      (fn _ =>
       Term_Insts
        (map (unembed_indexname o Parse_Tools.the_real_val) (map_filter I (insts @ concl_insts))))
    else
      (fn _ =>
        Unchecked_Term_Insts
          (map (Option.map Parse_Tools.the_real_val) insts,
            map (Option.map Parse_Tools.the_real_val) concl_insts))
  else
    if checked
    then
      (fn thm =>
        Named_Insts
          (apply2
            (map (Option.map (fn p => (Parse_Tools.the_parse_val p, Parse_Tools.the_parse_fun p))))
            (insts, concl_insts)
          |> of_rule thm |> map ((fn (xi, (nm, f)) => embed_indexname ((xi, nm), f))), fixes))
    else
      let val result = close_unchecked_insts context ((insts, concl_insts), fixes);
      in fn _ => result end;


fun read_instantiate_closed ctxt (Named_Insts (insts, fixes)) thm  =
      let
        val insts' = map (fn ((v, t), _) => ((v, Position.none), t)) insts;

        val (thm_insts, thm') = add_thm_insts ctxt thm;
        val (thm'', thm_insts') =
          Rule_Insts.where_rule ctxt insts' fixes thm'
          |> get_thm_insts;

        val tyinst =
          ListPair.zip (fst thm_insts, fst thm_insts') |> map (fn ((xi, _), typ) => (xi, typ));
        val tinst =
          ListPair.zip (snd thm_insts, snd thm_insts') |> map (fn ((xi, _), t) => (xi, t));

        val _ =
          map (fn ((xi, _), f) =>
            (case AList.lookup (op =) tyinst xi of
              SOME typ => f (Logic.mk_type typ)
            | NONE =>
                (case AList.lookup (op =) tinst xi of
                  SOME t => f t
                | NONE => error "Lost indexname in instantiated theorem"))) insts;
      in
        (thm'' |> restore_tags thm)
      end
  | read_instantiate_closed ctxt (Unchecked_Term_Insts insts) thm =
      let
        val (xis, ts) = ListPair.unzip (of_rule thm insts);
        val ctxt' = Variable.declare_maxidx (Thm.maxidx_of thm) ctxt;
        val (ts', ctxt'') = Variable.import_terms false ts ctxt';
        val ts'' = Variable.export_terms ctxt'' ctxt ts';
        val insts' = ListPair.zip (xis, ts'');
      in instantiate_xis ctxt insts' thm end
  | read_instantiate_closed ctxt (Term_Insts insts) thm =
      instantiate_xis ctxt insts thm;

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>where'\<close>
      (Scan.lift
        (Parse.and_list1 (Args'.var -- (Args.$$$ "=" |-- Parse_Tools.name_term)) -- Parse.for_fixes)
        >> (fn args =>
            let val args' = read_where_insts args in
              fn (context, thm) =>
                (NONE, SOME (read_instantiate_closed (Context.proof_of context) args' thm))
            end))
      "named instantiation of theorem");

val _ =
  Theory.setup
    (Attrib.setup \<^binding>\<open>of'\<close>
      (Scan.lift
        (Args.mode "unchecked" --
          (Scan.repeat (Scan.unless concl inst) --
            Scan.optional (concl |-- Scan.repeat inst) [] --
            Parse.for_fixes)) -- Scan.state >>
      (fn ((unchecked, args), context) =>
        let
          val read_insts = read_of_insts (not unchecked) context args;
        in
          fn (context, thm) =>
            let val thm' =
              if Thm.is_free_dummy thm andalso unchecked
              then Drule.free_dummy_thm
              else read_instantiate_closed (Context.proof_of context) (read_insts thm) thm
            in (NONE, SOME thm') end
        end))
      "positional instantiation of theorem");

end;
\<close>
ML\<open>open Resources\<close>
section \<open>User Defined Commands in the Semantic Verification Space\<close>

ML \<comment> \<open>\<^theory>\<open>Isabelle_C.C_Eval\<close>\<close> \<open>
structure C_Module' =
struct
structure Data_Annot = Generic_Data
(
  type T = (bool * string) list Inttab.table
  val empty = Inttab.empty
  val merge = K empty
)
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/args.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay
    Analogous to:
(*  Title:      Pure/Isar/args.ML
    Author:     Markus Wenzel, TU Muenchen

Quasi-inner syntax based on outer tokens: concrete argument syntax of
attributes, methods etc.
*)*)
\<open>
structure C_Args =
struct

(** argument scanners **)

(* basic *)

val ident = C_Parse.token
  (C_Parse.short_ident || C_Parse.long_ident || C_Parse.sym_ident || C_Parse.term_var ||
    C_Parse.type_ident || C_Parse.type_var || C_Parse.number);

val string = C_Parse.token C_Parse.string;

val cartouche = C_Parse.token C_Parse.cartouche;

val embedded_token = ident || string || cartouche;
val embedded_inner_syntax = embedded_token >> C_Token.inner_syntax_of;
end
\<close>

ML \<comment> \<open>\<^theory>\<open>Isabelle_C.C_Command\<close>\<close> \<open>
local
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
val Precond = Invariant  (* Hack *)
val Postcond = Invariant (* Hack *)

fun bind scan f ((stack1, (to_delay, stack2)), _) =
  C_Parse.range scan
  >> (fn (src, range) =>
      C_Env.Parsing
        ( (stack1, stack2)
        , ( range
          , C_Inner_Syntax.bottom_up (f src)
          , Symtab.empty
          , to_delay)))

fun command cmd scan0 scan f =
       C_Annotation.command' cmd "" (K (scan0 -- (scan >> f) >> K C_Env.Never))

fun command' cmd scan f =
       C_Annotation.command' cmd "" (bind scan f)

fun command'' cmd _ _ _ =
  command' cmd
           (C_Token.syntax' (Parse.token Parse.term))
           (fn src => fn _ => fn context =>
             ML_Context.exec
               (tap (fn _ => Syntax.read_term (Context.proof_of context)
                                              (Token.inner_syntax_of src)))
               context)

fun inv_measure b src _ gthy =
  let val l = length (C_Module.Data_In_Source.get gthy)
  in C_Module'.Data_Annot.map (Inttab.map_default (l, []) (cons (b, src))) gthy end

val invariant = inv_measure true
val measure = inv_measure false

in
val _ = Theory.setup ((* 1 '@' *)
                         command ("INVARIANT", \<^here>) scan_colon C_Parse.term Invariant
                      #> command ("INV", \<^here>) scan_colon C_Parse.term Invariant
                      #> command' ("invariant", \<^here>) C_Args.embedded_inner_syntax invariant
                      #> command' ("measure", \<^here>) C_Args.embedded_inner_syntax measure

                      (* '+' until being at the position of the first ident
                        then 2 '@' *)
                      #> command ("FNSPEC", \<^here>) scan_opt_colon (scan_ident --| scan_opt_colon -- C_Parse.term) Fnspec
                      #> command ("RELSPEC", \<^here>) scan_opt_colon C_Parse.term Relspec
                      #> command ("MODIFIES", \<^here>) scan_colon (Scan.repeat (   scan_brack_star >> pair true
                                                                          || scan_ident >> pair false))
                                                            Modifies
                      #> command ("DONT_TRANSLATE", \<^here>) scan_opt_colon (Scan.succeed ()) (K Dont_translate)

                      (**)
                      #> command ("AUXUPD", \<^here>) scan_colon C_Parse.term Auxupd
                      #> command ("GHOSTUPD", \<^here>) scan_colon C_Parse.term Ghostupd
                      #> command ("SPEC", \<^here>) scan_colon C_Parse.term Spec
                      #> command ("END-SPEC", \<^here>) scan_colon C_Parse.term End_spec

                      (**)
                      #> command ("CALLS", \<^here>) scan_opt_colon (Scan.repeat scan_ident) Calls
                      #> command ("OWNED_BY", \<^here>) scan_opt_colon scan_ident Owned_by

                      (* misc. *)
                      #> command'' ("requires", \<^here>) scan_opt_colon C_Parse.term Precond
                      #> command'' ("ensures", \<^here>) scan_opt_colon C_Parse.term Postcond);
end
\<close>

section \<open>Miscellaneous\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/ML/ml_options.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay
    Analogous to:
(*  Title:      Pure/ML/ml_options.ML
    Author:     Makarius

ML configuration options.
*)*)
\<open>
structure C_Options' =
struct
val generate_logical_files = Attrib.setup_config_bool @{binding generate_logical_files} (K true);
end
\<close>

end
