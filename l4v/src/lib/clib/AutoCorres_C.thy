(*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

chapter \<open>Extending C refinement proofs using AutoCorres\<close>

theory AutoCorres_C
imports
  Corres_C
  AutoCorresModifiesProofs
begin

text \<open>
This theory provides some tools for extending existing collections of C refinement proofs,
which use the @{term ccorresG} framework, with new proofs using the higher-level
@{term corres_underlying} framework. We use AutoCorres to move between the frameworks.

See AutoCorresTest for examples.
\<close>

section \<open>Setup\<close>

text \<open>
The imports for this theory cause a merge between AutoCorres and the preamble for CRefine.
AutoCorres both adds to and deletes from various rule sets, such that the merge produces
an entirely new theory context, which is unfamiliar to any previous CRefine or AutoCorres
development. In particular, rules which were deleted in AutoCorres may reappear in this
theory, but in a different place in the rule set than they appeared in Corres_C.

The following setup restores the ordering from @{theory Corres_C} for the crucial
@{attribute wp_comb} rule set, and places new rules introduced by @{theory AutoCorres} at
the end of the @{attribute wp_comb} set.

To ensure that we only have to do this once, we are careful to ensure that there is only
one theory merge between AutoCorres and CRefine. We import @{theory L4VerifiedLinks} into
@{theory AutoCorresModifiesProofs}, and import the latter here. This satisfies the
dependencies from @{theory AutoCorresModifiesProofs} to @{theory AutoCorres}, and from
this theory to @{theory L4VerifiedLinks} and @{theory Corres_C}, without duplicating
theory merges. Finally, we list @{theory L4VerifiedLinks} as a top-level theory in the
CBaseRefine session, so that @{theory AutoCorres} need not be processed in a CRefine
session, but do not import @{theory AutoCorres} into @{text Include_C}, since that would
cause a redundant theory merge.
\<close>

setup \<open>
  fn thy => let
    fun get_combs thy = #combs (WeakestPre.get_rules (Proof_Context.init_global thy) [])
    val corres_c_combs = get_combs (Context.get_theory thy "Corres_C")
    val accorres_combs = get_combs thy
    val subtract_thms = subtract (fn (a,b) => Thm.prop_of a = Thm.prop_of b)
    val accorres_extra = subtract_thms corres_c_combs accorres_combs
    fun upd attr = fold_rev (snd oo Thm.apply_attribute attr)
    val add = upd WeakestPre.combs_add
    val del = upd WeakestPre.combs_del
    val upd_gen = add corres_c_combs o add accorres_extra o del accorres_combs
  in Context.theory_of (upd_gen (Context.Theory thy)) end
\<close>

text \<open>
AutoCorres adds some rules about @{term whenE} to the @{attribute wp} set, which don't always
behave nicely. They introduce @{term If} expressions into pre and post conditions, where they
don't always simplify as one might expect. We replace them with a rule that does allow the
conditional to simplify away more often.

FIXME: Move this change into AutoCorres itself, or the underlying VCG library.
\<close>

lemmas [wp del] =
  NonDetMonadEx.validE_whenE
  NonDetMonadLemmaBucket.hoare_whenE_wp

lemmas hoare_whenE_wp2 [wp] =
  NonDetMonadLemmaBucket.hoare_whenE_wp[simplified if_apply_def2]

section \<open>Rules for proving @{term ccorres_underlying} goals\<close>

text \<open>
Following are rules for converting a @{term ccorresG} goal to a @{term corres_underlying}
goal, by making use of an automatically generated @{term ac_corres} fact about the procedure.

For the first of these, the user is expected to specify the return-value relation for the resulting
@{term corres_underlying} goal, and will be required to prove that it implies the return-value
relation of the original @{term ccorresG} goal.
\<close>

lemma corres_to_ccorres:
  assumes rf_sr_def: "rf_sr \<equiv> {(s,s'). cstate_relation s (globals s')}"
  assumes acc: "ac_corres globals check_term \<Gamma> ret_xf G (liftE ac) c"
  assumes cac: "corres_underlying {(s,s'). cstate_relation s s'} True True R P Q a ac"
  assumes pre: "\<And>s s'. cstate_relation s (globals s') \<Longrightarrow> P' s \<and> s' \<in> Q' \<Longrightarrow> P s \<and> Q (globals s')"
  assumes p_g: "\<And>s s'. cstate_relation s (globals s') \<Longrightarrow> P' s \<and> s' \<in> Q' \<Longrightarrow> G s'"
  assumes ret: "\<And>r s'. R r (ret_xf s') \<longrightarrow> R' r (ret_xf' s')"
  shows "ccorresG rf_sr \<Gamma> R' ret_xf' P' Q' [] a c"
  unfolding rf_sr_def using ac_corres_ccorres_underlying[OF acc] cac pre p_g
  by (fastforce simp: ccorres_underlying_def corres_underlying_def unif_rrel_def
                      liftE_def in_liftE[simplified liftE_def]
                dest: mp[OF ret]
               split: xstate.splits)

text \<open>
In the following rule, the return-value relation for the resulting @{term corres_underlying}
goal is fixed to a reasonably general relation. In cases where this return-value relation is
good enough, it saves the effort of explicitly specifying a return-value relation.
\<close>

lemma corres_to_ccorres_rv_spec:
  assumes "rf_sr \<equiv> {(s,s'). cstate_relation s (globals s')}"
  assumes "ac_corres globals check_term \<Gamma> ret_xf G (liftE ac) c"
  assumes "corres_underlying {(s,s'). cstate_relation s s'} True True
                             (\<lambda>r r'. \<forall>s'. r' = ret_xf s' \<longrightarrow> R' r (ret_xf' s')) P Q a ac"
  assumes "\<And>s s'. cstate_relation s (globals s') \<Longrightarrow> P' s \<and> s' \<in> Q' \<Longrightarrow> P s \<and> Q (globals s')"
  assumes "\<And>s s'. cstate_relation s (globals s') \<Longrightarrow> P' s \<and> s' \<in> Q' \<Longrightarrow> G s'"
  shows "ccorresG rf_sr \<Gamma> R' ret_xf' P' Q' [] a c"
  using assms by (auto intro: corres_to_ccorres)

section \<open>Rules for importing @{term ccorresG} facts\<close>

text \<open>
While proving a @{term corres_underlying} goal which was obtained from a @{term ccorresG} goal,
we might want to make use of existing @{term ccorresG} facts about called procedures. Following
are rules for converting existing @{term ccorresG} facts to suitable @{term corres_underlying}
facts.
\<close>

lemma in_AC_call_simpl:
  fixes r s s' arg_pred ret_xf \<Gamma> f_'proc
  shows "(r, s') \<in> fst (AC_call_L1 arg_pred globals ret_xf (L1_call_simpl check_term \<Gamma> f_'proc) s) \<Longrightarrow>
         \<exists>cs cs'. s = globals cs \<and> arg_pred cs \<and>
                  (check_term \<longrightarrow> \<Gamma> \<turnstile> Call f_'proc \<down> Normal cs) \<and>
                  \<Gamma> \<turnstile> \<langle>Call f_'proc, Normal cs\<rangle> \<Rightarrow> Normal cs' \<and>
                  s' = globals cs' \<and> r = ret_xf cs'"
  apply (clarsimp simp: AC_call_L1_def L2_call_L1_def L1_call_simpl_def
                        in_monad liftM_def select_def select_f_def
                 split: xstate.splits sum.splits)
  apply (rename_tac cs cs' status; case_tac status; fastforce)
  done

text \<open>
Given a @{term ccorresG} fact, we need to process its preconditions to obtain a
@{term corres_underlying} fact in a usable form. The following definition, rules and method
provide some machinery for this processing.

For a @{term ccorresG} rule about a procedure call, the concrete precondition typically
describes how local variables in the C state relate to the arguments of the abstract procedure
call. In some cases, it might also talk about the global C state.

For the conversion from @{term ccorresG} to @{term corres_underlying}, we will use AutoCorres
to generate an abstract wrapper around the C call. The wrapper will also have a precondition
describing the relationship between local variables in the C state, and arguments to the
wrapper.

The purpose of this machinery, then, is to partition the components of the @{term ccorresG}
precondition. Preconditions concerning function arguments are matched between the @{term ccorresG}
fact and the AutoCorres-generated wrapper, and need not appear in the preconditions of the
resulting @{term ccorres_underlying} rule. On the other hand, preconditions concerning global
state must appear in the resulting @{term ccorres_underlying} rule.
\<close>

definition
  "ccorres_to_corres_pre Q E Q' s' \<equiv> Q (globals s') \<longrightarrow> E s' \<and> s' \<in> Q'"

text \<open>
In @{term ccorres_to_corres_pre}, parameter @{term Q'} is the @{term ccorresG} precondition
begin analysed; parameter @{term Q} is a schematic variable for what will become the precondition
of the resulting @{term ccorres_underlying} rule, and therefore only concerns global state; and
parameter @{term E} accumulates equalities between arguments to the AutoCorres-generated wrapper
and the arguments to the abstract function call in the @{term ccorresG} fact.
\<close>

text \<open>
Preconditions concerning global variables are incorporated into the precondition of the
resulting @{term ccorres_underlying} fact.
\<close>
lemma ccorres_to_corres_pre_globals_Int:
  assumes "ccorres_to_corres_pre Q E Q' s'"
  shows "ccorres_to_corres_pre (P and Q) E ({s'. P (globals s')} \<inter> Q') s'"
  using assms by (simp add: ccorres_to_corres_pre_def)

lemmas ccorres_to_corres_pre_globals_base
  = ccorres_to_corres_pre_globals_Int[where Q'=UNIV, simplified Int_UNIV_right]

text \<open>
For preconditions concerning function arguments, we can eliminate any mention of C local
variable state, and are left with a predicate on the argument to AutoCorres-generated
wrapper. Typically, this will be a relation to an argument to the abstract call in the
@{term ccorresG} fact.
\<close>
lemma ccorres_to_corres_pre_local_Int:
  assumes "f s' = x"
  assumes "ccorres_to_corres_pre Q (K (P x) and E) Q' s'"
  shows "ccorres_to_corres_pre Q E ({s'. P (f s')} \<inter> Q') s'"
  using assms by (simp add: ccorres_to_corres_pre_def)

lemmas ccorres_to_corres_pre_local_base
  = ccorres_to_corres_pre_local_Int[where Q'=UNIV, simplified Int_UNIV_right]

lemma ccorres_to_corres_pre_UNIV_Int:
  assumes "ccorres_to_corres_pre Q E Q' s'"
  shows "ccorres_to_corres_pre Q E (UNIV \<inter> Q') s'"
  using assms by (simp add: ccorres_to_corres_pre_def)

lemmas ccorres_to_corres_pre_intros =
  ccorres_to_corres_pre_UNIV_Int
  ccorres_to_corres_pre_globals_Int
  ccorres_to_corres_pre_globals_base

lemmas ccorres_to_corres_pre_elims =
  ccorres_to_corres_pre_local_Int
  ccorres_to_corres_pre_local_base

lemma ccorres_to_corres_pre_finalise:
  "E s' \<Longrightarrow> ccorres_to_corres_pre \<top> E UNIV s'"
  by (simp add: ccorres_to_corres_pre_def)

method ccorres_to_corres_pre_step =
  (rule ccorres_to_corres_pre_intros | erule ccorres_to_corres_pre_elims)

method ccorres_to_corres_pre_process = (
  (elim pred_andE)?,
  (simp only: Int_assoc)?,
  (ccorres_to_corres_pre_step+)?,
  (rule ccorres_to_corres_pre_finalise),
  (intro pred_andI TrueI; clarsimp)
)

text \<open>
We can easily obtain a partial @{term corres_underlying} fact from a @{term ccorresG} fact.
However, this is not strong enough to prove @{term ccorresG} goals of the form produced by
@{thm corres_to_ccorres} above.
\<close>

lemma ccorres_to_corres_partial:
  assumes rf_sr_def: "rf_sr \<equiv> {(s,s'). cstate_relation s (globals s')}"
  assumes ac_def: "ac_f \<equiv> AC_call_L1 G globals ret_xf (L1_call_simpl check_term \<Gamma> f_'proc)"
  assumes ccorres: "ccorresG rf_sr \<Gamma> R' ret_xf' P Q' [] dspec_f (Call f_'proc)"
  assumes pre: "\<And>s'. G s' \<Longrightarrow> ccorres_to_corres_pre Q \<top> Q' s'"
  assumes ret: "\<And>r s'. R r (ret_xf s') \<longleftrightarrow> R' r (ret_xf' s')"
  shows "corres_underlying {(s, s'). cstate_relation s s'} True False R P Q dspec_f ac_f"
  using ccorres ret pre unfolding ac_def ccorres_to_corres_pre_def
  by (fastforce simp: unif_rrel_def corres_underlying_def ccorres_underlying_def rf_sr_def
                intro: EHOther dest: in_AC_call_simpl)

text \<open>
If we are willing to prove termination of the C code, we can obtain a rule which can be used
with or without the AutoCorres no_c_termination setting, and which is strong enough to prove
goals obtained from @{thm corres_to_ccorres}.
\<close>

lemma ccorres_to_corres_with_termination:
  assumes rf_sr_def: "rf_sr \<equiv> {(s,s'). cstate_relation s (globals s')}"
  assumes ac_def: "ac_f \<equiv> AC_call_L1 G globals ret_xf (L1_call_simpl check_term \<Gamma> f_'proc)"
  assumes ccorres: "ccorresG rf_sr \<Gamma> R' ret_xf' P Q' [] dspec_f (Call f_'proc)"
  assumes pre: "\<And>s'. G s' \<Longrightarrow> ccorres_to_corres_pre Q \<top> Q' s'"
  assumes ret: "\<And>r s'. R r (ret_xf s') \<longleftrightarrow> R' r (ret_xf' s')"
  assumes terminates:
    "\<And>s s'. \<lbrakk> cstate_relation s (globals s'); P s; \<not> snd (dspec_f s); G s' \<rbrakk> \<Longrightarrow>
             \<Gamma> \<turnstile> Call f_'proc \<down> Normal s'"
  shows "corres_underlying {(s, s'). cstate_relation s s'} True True R P Q dspec_f ac_f"
  using ccorres ret pre unfolding ac_def ccorres_to_corres_pre_def
  apply (clarsimp simp: corres_underlying_def ccorres_underlying_def rf_sr_def)
  apply (rule conjI)
   apply (fastforce simp: unif_rrel_def intro: EHOther dest: in_AC_call_simpl)
  apply (clarsimp simp: AC_call_L1_def L2_call_L1_def L1_call_simpl_def)
  apply (cases check_term;
         clarsimp simp: select_f_def select_def snd_bind snd_assert get_def
                 split: sum.splits prod.splits)
    apply (erule impE, blast intro: terminates)
    apply (erule disjE)
     apply (monad_eq split: xstate.splits sum.splits)
      apply (drule EHOther, fastforce)
      apply blast
     apply (drule EHOther, fastforce)
     apply blast
    apply (monad_eq split: xstate.splits)
    apply (fastforce dest: EHAbrupt[OF _ EHEmpty])
   apply (monad_eq split: xstate.splits sum.splits)
    apply (drule EHOther, fastforce)
    apply blast
   apply (drule EHOther, fastforce)
   apply blast
  apply (monad_eq split: xstate.splits)
  apply (fastforce dest: EHAbrupt[OF _ EHEmpty])
  done

text \<open>
When using AutoCorres with the no_c_termination setting, we need not prove termination
of the C code.
\<close>

lemma ccorres_to_corres_no_termination:
  assumes rf_sr_def: "rf_sr \<equiv> {(s,s'). cstate_relation s (globals s')}"
  assumes ac_def: "ac_f \<equiv> AC_call_L1 G globals ret_xf (L1_call_simpl False \<Gamma> f_'proc)"
  assumes ccorres: "ccorresG rf_sr \<Gamma> R' ret_xf' P Q' [] dspec_f (Call f_'proc)"
  assumes pre: "\<And>s'. G s' \<Longrightarrow> ccorres_to_corres_pre Q \<top> Q' s'"
  assumes ret: "\<And>r s'. R r (ret_xf s') \<longleftrightarrow> R' r (ret_xf' s')"
  shows "corres_underlying {(s, s'). cstate_relation s s'} True True R P Q dspec_f ac_f"
  using ccorres ret pre unfolding ac_def ccorres_to_corres_pre_def
  apply (clarsimp simp: ac_def corres_underlying_def ccorres_underlying_def rf_sr_def)
  apply (rule conjI)
   apply (fastforce simp: unif_rrel_def intro: EHOther dest: in_AC_call_simpl)
  apply (clarsimp simp: AC_call_L1_def L2_call_L1_def L1_call_simpl_def)
  apply (clarsimp simp: select_f_def select_def snd_bind snd_assert get_def
                 split: sum.splits prod.splits)
   apply (monad_eq split: xstate.splits sum.splits)
    apply (drule EHOther, fastforce)
    apply blast
   apply (drule EHOther, fastforce)
   apply blast
  apply (monad_eq split: xstate.splits)
  apply (fastforce dest: EHAbrupt[OF _ EHEmpty])
  done

section \<open>Proof automation\<close>

text \<open>
We now provide ML functions for constructing simple proof automation tools.

The first implements a method which converts a @{term ccorresG} goal into a
@{term corres_underlying} goal, using @{thm corres_to_ccorres}, and automatically
solving some subgoals. In some cases, it will also guess an appropriate return-value
relation.

The second is an attribute which converts a @{term ccorresG} fact into a
@{term corres_underlying} fact.

The setup functions are parameterised over a state relation. We instantiate them
for the C kernel below.
\<close>

ML \<open>
signature AUTOCORRES_CREFINE = sig
  val setup_ac_init : thm -> (Proof.context -> Proof.method) context_parser
  val setup_ac_attr : thm -> attribute context_parser
end

structure AutoCorresCRefine : AUTOCORRES_CREFINE = struct

  fun proc_base_name termerr qualified_'proc_name =
    unsuffix "_'proc" (List.last (Long_Name.explode qualified_'proc_name))
      handle Empty => raise termerr "empty proc name"
      handle Fail _ => raise termerr "not a _'proc"

  fun get_call_'proc_name termerr c = case c of
      Const (@{const_name Call}, _) $ Const (qualified_'proc_name, _) => qualified_'proc_name
    | _ => raise termerr "not a Call"

  fun match_ccorres_term termerr ccorres_term = case ccorres_term of
      @{term Trueprop} $
        (Const (@{const_name ccorres_underlying}, _)
          $ _ $ c_Gamma $ c_rel $ c_xf $ a_rel $ a_xf $ _ $ _ $ c_hs $ _ $ c_c) =>
      let
        val _ = if c_rel = a_rel orelse c_xf = a_xf then ()
                  else raise termerr "not a ccorres goal"
      in
        { c_Gamma=c_Gamma, c_rel=c_rel, c_xf=c_xf, c_hs=c_hs, c_c=c_c }
      end
    | _ => raise termerr "not a ccorres goal"

  fun match_ac_corres_term ac_corres_fact_name ac_corres_term = case ac_corres_term of
      @{term Trueprop} $ (Const (@{const_name ac_corres}, _)
        $ _ $ _ $ ac_Gamma $ ac_xf $ _ $ (Const (@{const_name liftE}, _) $ _) $ ac_c)
        => { ac_Gamma=ac_Gamma, ac_xf=ac_xf, ac_c=ac_c }
    | _ => error ("ac_init_tac: " ^ ac_corres_fact_name ^ " not an ac_corres fact")

  fun match_ac_wrap_term ac_wrap_name ac_wrap_term = case ac_wrap_term of
      Const (@{const_name Pure.eq}, _) $ _
        $ (Const (@{const_name AC_call_L1}, _) $ _ $ Const (@{const_name globals}, _) $ ac_xf
        $ (Const (@{const_name L1_call_simpl}, _) $ check_term $ ac_Gamma
        $ (Const (ac_proc_name, _))))
        => { ac_Gamma=ac_Gamma, ac_xf=ac_xf, check_term=check_term, ac_proc_name=ac_proc_name }
    | _ => error ("ac_attr: " ^ ac_wrap_name ^ " wasn't in the expected form")

  fun auto_rv_relation ctxt mk_imp ac_xf c_rel c_xf =
    let
      (* Find the types of return-value relations and extraction functions. *)
      val ccorres_xf_ty = fastype_of c_xf
      val c_state_ty = case ccorres_xf_ty of
          Type("fun", [st_ty, _]) => st_ty
        | _ => raise TYPE ("ac_init_tac'", [ccorres_xf_ty], [c_xf])
      val ac_corres_xf_ty = fastype_of ac_xf
      val ac_corres_ret_ty = case ac_corres_xf_ty of
          Type("fun", [_, acr_ty]) => acr_ty
        | _ => raise TYPE ("ac_init_tac'", [ac_corres_xf_ty], [ac_xf])
      val ccorres_rrel_ty = fastype_of c_rel
      val abstract_ret_ty = case ccorres_rrel_ty of
          Type("fun", [ar_ty, Type("fun", [_, @{typ bool}])]) => ar_ty
        | _ => raise TYPE("ac_init_tac'", [ccorres_rrel_ty], [c_rel])
      val ac_corres_rrel_ty = abstract_ret_ty --> ac_corres_ret_ty --> @{typ bool}

      (* A function for building implications between return-value relations,
         of the form used in corres_to_ccorres. *)
      fun mk_rv_prop rv_rel =
        let
          val r_var = Free ("r", abstract_ret_ty)
          val state_var = Free ("s'", c_state_ty)
          fun mk_rel r xf = r $ r_var $ (xf $ state_var)
          val assm = mk_rel rv_rel ac_xf
          val conc = mk_rel c_rel c_xf
          val prop = HOLogic.mk_Trueprop (mk_imp (assm, conc))
        in
          Logic.all r_var (Logic.all state_var prop)
        end

      (* Try two strategies for guessing a simple return-value relation,
         and proving a corresponding implication:
         - If dc works, use that.
         - If the types allow us to reuse the relation we were given, try that. *)
      fun first _ [] = NONE
        | first f (x::xs) = (if f x then SOME x else first f xs)
      fun prove_rv rv_rel =
          (Goal.prove ctxt [] [] (mk_rv_prop rv_rel) (fn _ => full_simp_tac ctxt 1); true)
                handle ERROR _ => false
    in
      first prove_rv [Const (@{const_name dc}, ac_corres_rrel_ty), c_rel]
        |> Option.map (Thm.cterm_of ctxt)
    end

  fun ac_init_tac corres_to_ccorres corres_to_ccorres_rv_spec ctxt (insts, fixes) ccorres_goal_t =
    let
      fun termerr msg = TERM ("ac_init_tac: " ^ msg, [ccorres_goal_t])

      (* Find the arguments to ccorres in the goal. *)
      val { c_Gamma, c_rel, c_xf, c_hs, c_c } = match_ccorres_term termerr ccorres_goal_t
      val proc_name = proc_base_name termerr (get_call_'proc_name termerr c_c)

      (* Check that the handler stack is empty. *)
      val _ = case c_hs of Const (@{const_name Nil}, _) => ()
                | _ => raise termerr "non-empty handler stack"

      (* Find the AutoCorres-generated fact for that procedure. *)
      val ac_corres_fact_name = proc_name ^ "'_ac_corres"
      val ac_corres_fact = Proof_Context.get_thm ctxt ac_corres_fact_name
            handle ERROR msg => error ("ac_init_tac: " ^ msg)

      (* Find the arguments to ac_corres in the AutoCorres-generated fact. *)
      val { ac_Gamma, ac_xf, ac_c } =
          match_ac_corres_term ac_corres_fact_name (Thm.prop_of ac_corres_fact)

      (* Check that AutoCorres-generated fact is as expected. *)
      val _ = if ac_c = c_c andalso c_Gamma = ac_Gamma then ()
              else error ("ac_init_tac: " ^ ac_corres_fact_name ^ " unexpected fact")

      fun corres_to_ccorres_inst rv_rel =
        Drule.infer_instantiate ctxt [(("R",0), rv_rel)] corres_to_ccorres

      val auto_rv_relation_tac =
        case auto_rv_relation ctxt HOLogic.mk_imp ac_xf c_rel c_xf of
            SOME rv_rel =>
              resolve_tac ctxt [corres_to_ccorres_inst rv_rel] 1 THEN
              resolve_tac ctxt [ac_corres_fact] 1 THEN
              SOLVED' (full_simp_tac ctxt) 4 THEN
              TRY (SOLVED' (full_simp_tac ctxt) 3)
          | NONE =>
              resolve_tac ctxt [corres_to_ccorres_rv_spec] 1 THEN
              resolve_tac ctxt [ac_corres_fact] 1 THEN
              TRY (SOLVED' (full_simp_tac ctxt) 3)

      fun spec_rv_relation_tac thm =
        let
          val init_thm = (ac_corres_fact RS corres_to_ccorres) RS thm
          val inst_thm = Rule_Insts.where_rule ctxt insts fixes init_thm
          val tac =
            TRY (SOLVED' (full_simp_tac ctxt) 4) THEN
            TRY (SOLVED' (full_simp_tac ctxt) 3)
        in
          tac inst_thm
        end
    in
      if null insts andalso null fixes
        then auto_rv_relation_tac
        else spec_rv_relation_tac
    end

  fun ac_attr conv_with_term conv_no_term gen_ctxt insts fixes ccorres_thm =
    let
      val ctxt = Context.proof_of gen_ctxt
      val ccorres_t = Thm.prop_of ccorres_thm

      fun termerr msg = TERM ("ac_attr: " ^ msg, [ccorres_t])

      (* Find the arguments to ccorres in the given fact. *)
      val { c_Gamma, c_rel, c_xf, c_c, ... } = match_ccorres_term termerr ccorres_t

      val qualified_'proc_name = get_call_'proc_name termerr c_c
      val proc_name = proc_base_name termerr qualified_'proc_name

      (* Find the AutoCorres-generated wrapper, and extract relevant arguments. *)
      val ac_wrap_name = proc_name ^ "'_def"
      val ac_wrap_def = Proof_Context.get_thm ctxt ac_wrap_name
            handle ERROR msg => error ("ac_attr: " ^ msg)

      val { ac_Gamma, ac_xf, check_term, ac_proc_name } =
          match_ac_wrap_term ac_wrap_name (Thm.prop_of ac_wrap_def)

      (* Check that AutoCorres-generated wrapper is as expected. *)
      val _ = if ac_proc_name = qualified_'proc_name andalso ac_Gamma = c_Gamma then ()
              else error ("ac_attr: " ^ ac_wrap_name ^ " wasn't in the expected form")

      val ccorres_to_corres = case check_term of
          @{term False} => conv_no_term | _ => conv_with_term

      fun ccorres_to_corres_inst rv_rel =
        Drule.infer_instantiate ctxt [(("R",0), rv_rel)] ccorres_to_corres

      val (ccorres_to_corres', rv_tac) =
        if null insts andalso null fixes then
          case auto_rv_relation ctxt HOLogic.mk_eq ac_xf c_rel c_xf of
              SOME rv_rel => (ccorres_to_corres_inst rv_rel, SOLVED' (full_simp_tac ctxt) 2)
            | NONE => (ccorres_to_corres, all_tac)
          else (Rule_Insts.where_rule ctxt insts fixes ccorres_to_corres, all_tac)

      val ac_corres_init_thm = ccorres_thm RS (ac_wrap_def RS ccorres_to_corres')

      val ccorres_to_corres_pre_process_tac = Method.NO_CONTEXT_TACTIC ctxt
          (Method_Closure.apply_method ctxt @{method ccorres_to_corres_pre_process}
                                       [] [] [] ctxt [])

      val tac = rv_tac THEN ccorres_to_corres_pre_process_tac
    in
      Seq.hd (tac ac_corres_init_thm) |> asm_full_simplify ctxt
    end

  val where_for_parser =
    Scan.lift
      (Scan.optional
        (Args.$$$ "where" |--
          Parse.and_list
            (Parse.position Args.var -- (Args.$$$ "=" |-- Parse.!!! Args.embedded_inner_syntax))
          -- Parse.for_fixes)
        ([],[]))

  fun setup_ac_init rf_sr_def =
    let
      val corres_to_ccorres = rf_sr_def RS @{thm corres_to_ccorres}
      val corres_to_ccorres_rv_spec = rf_sr_def RS @{thm corres_to_ccorres_rv_spec}
      val tac = ac_init_tac corres_to_ccorres corres_to_ccorres_rv_spec
    in
      where_for_parser >>
        (fn args => fn ctxt => fn facts =>
          SIMPLE_METHOD (SUBGOAL (tac ctxt args o #1) 1) facts)
    end

  fun setup_ac_attr rf_sr_def =
    let
      val conv_with_term = rf_sr_def RS @{thm ccorres_to_corres_with_termination}
      val conv_no_term = rf_sr_def RS @{thm ccorres_to_corres_no_termination}
    in
      where_for_parser >>
        (fn (insts, fixes) => fn (ctxt, ccorres_thm) =>
          (NONE, SOME (ac_attr conv_with_term conv_no_term ctxt insts fixes ccorres_thm)))
    end
end
\<close>

section \<open>Kernel instantiation\<close>

text \<open>Here, we instantiate the proof automation for the C kernel.\<close>

context kernel begin

method_setup ac_init = \<open>AutoCorresCRefine.setup_ac_init @{thm rf_sr_def}\<close>
attribute_setup ac = \<open>AutoCorresCRefine.setup_ac_attr @{thm rf_sr_def}\<close>

text \<open>
FIXME: It would be nice to have an abbreviation for the @{term corres_underlying} relation
that comes out of @{method ac_init}. Unfortunately, this causes renumbering of metavariables
produced in resolution, breaking many proofs, so we avoid this for now.
\<close>
(* abbreviation "corres_ac \<equiv> corres_underlying {(s, s'). cstate_relation s s'} True True" *)

end

section \<open>Experiments with transferring bitfield proofs\<close>

text \<open>Generic transfer rules\<close>
lemma autocorres_transfer_spec:
  assumes ac_def:
    "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl check_termination \<Gamma> f_'proc)"
  assumes c_spec:
    "\<forall>s0. \<Gamma>\<turnstile> (Collect (\<lambda>s. s0 = s \<and> P s)) Call f_'proc (Collect (Q s0))"
  assumes precond_deps:
    "\<And>s t. \<lbrakk> arg_rel s; arg_rel t; globals s = globals t \<rbrakk> \<Longrightarrow> P s = P t"
  assumes postcond_deps:
    "\<And>s0 s0' s t. \<lbrakk> arg_rel s0; arg_rel s0'; globals s0 = globals s0';
                    ret_xf s = ret_xf t; globals s = globals t \<rbrakk> \<Longrightarrow> Q s0 s = Q s0' t"
  shows "\<lbrace>\<lambda>s. P cs \<and> s = globals cs \<and> arg_rel cs \<rbrace>
           ac_f
         \<lbrace>\<lambda>r s'. \<exists>cs'. s' = globals cs' \<and> r = ret_xf cs' \<and> Q cs cs' \<rbrace>"
  apply (clarsimp simp: valid_def ac_def AC_call_L1_def L2_call_L1_def L1_call_simpl_def
                        in_monad' in_liftM select_f_def in_select in_fail
                  split: sum.splits xstate.splits)
  apply (rename_tac r', case_tac r'; clarsimp)
  apply (rename_tac xst, case_tac xst; clarsimp)
  apply (drule_tac ?s0.1=s in exec_normal[OF _ _ c_spec[rule_format], rotated])
   apply (blast dest: precond_deps)
  apply (blast dest: postcond_deps)
  done

text \<open>This one is probably more useful\<close>
lemma autocorres_transfer_spec_no_modifies:
  assumes ac_def:
    "ac_f \<equiv> AC_call_L1 arg_rel globals ret_xf (L1_call_simpl check_termination \<Gamma> f_'proc)"
  assumes c_spec:
    "\<forall>s0. hoarep \<Gamma> {} {} (P' s0) (Call f_'proc) (Collect (Q s0)) A" -- \<open>syntax parser barfs...\<close>
  assumes c_modifies:
    "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call f_'proc {t. t may_not_modify_globals \<sigma>}"
  assumes c_spec_unify:
    "\<And>s0. P' s0 = {s. s0 = s \<and> P s}"
  assumes precond_deps:
    "\<And>s0 s t. \<lbrakk> arg_rel s; arg_rel t; globals s = globals t \<rbrakk> \<Longrightarrow> P s = P t"
  assumes postcond_deps:
    "\<And>s0 s0' s t. \<lbrakk> arg_rel s0; arg_rel s0'; globals s0 = globals s0';
                    ret_xf s = ret_xf t; globals s = globals t \<rbrakk> \<Longrightarrow> Q s0 s = Q s0' t"
  shows "\<lbrace>\<lambda>s. s = globals cs \<and> P cs \<and> arg_rel cs \<rbrace>
           ac_f
         \<lbrace>\<lambda>r s'. s' = globals cs \<and> (\<exists>cs'. r = ret_xf cs' \<and> Q cs cs') \<rbrace>"
  apply (clarsimp simp: valid_def ac_def AC_call_L1_def L2_call_L1_def L1_call_simpl_def
                        in_monad' in_liftM select_f_def in_select in_fail
                  split: sum.splits xstate.splits)
  apply (rename_tac r', case_tac r'; clarsimp)
  apply (rename_tac xst, case_tac xst; clarsimp)
  apply (frule_tac ?s0.1=s in exec_normal[OF _ _ c_spec[rule_format], rotated])
   apply (clarsimp simp: c_spec_unify)
   apply (blast dest: precond_deps)
  apply (frule exec_normal[OF singletonI _ c_modifies[rule_format]])
  apply (clarsimp simp: meq_def)
  apply (blast dest: postcond_deps)
  done

subsection \<open>Helpers\<close>

lemma All_to_all':
  "(\<forall>x. P x) \<Longrightarrow> (\<And>x. P x)"
  by simp

text \<open>
  Convert references to global or local state variables, to the opposite one.
  FIXME: surely this has been proven already.
\<close>
lemma collect_lift:
  "Collect (\<lambda>s. s0 = s \<and> f s) = Collect (\<lambda>s. s0 = s \<and> f s0)"
  by blast
lemma collect_unlift:
  "Collect (\<lambda>s. s0 = s \<and> f s0 s) = Collect (\<lambda>s. s0 = s \<and> f s s)"
  by blast


subsection \<open>Experiment with wrapping specs\<close>
lemma exec_no_fault:
  assumes asms: "s \<in> P"
  and     ce: "Gamma \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Fault f"
  and  valid: "Gamma \<turnstile> P c Q, A"
  shows   "False"
  using valid ce asms
  apply -
  apply (frule hoare_sound)
  apply (clarsimp simp: NonDetMonad.bind_def cvalid_def split_def HoarePartialDef.valid_def)
  apply (drule spec, drule spec, drule (1) mp)
  apply auto
  done

lemma exec_no_stuck:
  assumes asms: "s \<in> P"
  and     ce: "Gamma \<turnstile> \<langle>c, Normal s\<rangle> \<Rightarrow> Stuck"
  and  valid: "Gamma \<turnstile> P c Q, A"
  shows   "False"
  using valid ce asms
  apply -
  apply (frule hoare_sound)
  apply (clarsimp simp: NonDetMonad.bind_def cvalid_def split_def HoarePartialDef.valid_def)
  apply (drule spec, drule spec, drule (1) mp)
  apply auto
  done

definition L1_call_simpl_spec where
  "L1_call_simpl_spec check_term Gamma proc precond postcond =
     L1_spec (Collect (\<lambda>(s, t). precond s s \<and> postcond s t))"

lemma L1corres_call_simpl_spec:
  "\<lbrakk> \<forall>s0. Gamma\<turnstile> (Collect (precond s0)) (Call proc) (Collect (postcond s0));
     \<And>s. ct \<Longrightarrow> Gamma\<turnstile>Call proc \<down> Normal s \<rbrakk> \<Longrightarrow>
   L1corres ct Gamma (L1_call_simpl_spec ct Gamma proc precond postcond) (Call proc)"
  apply (clarsimp simp: L1corres_def L1_call_simpl_spec_def L1_defs
                        assert_def snd_select snd_liftE snd_spec
                        in_monad' in_spec
                  split: xstate.splits)
  apply (case_tac t)
     apply (blast dest: exec_normal[rotated])
    apply (blast dest: exec_abrupt[rotated])
   apply (blast intro: exec_no_fault[rotated])
  apply (blast intro: exec_no_stuck[rotated])
  done


section \<open>Termination proofs\<close>
text \<open>
  Proving termination side conditions for @{thm ccorres_to_corres_with_termination}.

  To begin with, we can automatically prove terminates for most
  helper functions as they do not have recursion or loops.
\<close>

named_theorems terminates_trivial

ML \<open>
local
  fun terminates_intros ctxt =
    REPEAT_ALL_NEW (resolve_tac ctxt (Proof_Context.get_thms ctxt "terminates_trivial"));
in
fun terminates_trivial_tac ctxt n st =
  case Logic.concl_of_goal (Thm.prop_of st) n of
      @{term_pat "Trueprop (_ \<turnstile> Call ?f_'proc \<down> _)"} => let
        val f = dest_Const f_'proc |> fst |> Long_Name.base_name |> unsuffix "_'proc";
        val impl = Proof_Context.get_thm ctxt (f ^ "_impl");
        val body = Proof_Context.get_thm ctxt (f ^ "_body_def");
        in st |>
           (resolve_tac ctxt @{thms terminates.Call} n
             THEN resolve_tac ctxt [impl] n
            THEN simp_tac (put_simpset HOL_ss ctxt addsimps
                             (body :: @{thms return_C_def lvar_nondet_init_def})) n
            THEN terminates_intros ctxt n) end
    | _ => terminates_intros ctxt n st
end
\<close>

lemma [terminates_trivial]:
  "\<lbrakk> \<And>s. \<Gamma> \<turnstile> c \<down> Normal s \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Guard F G c \<down> Normal s"
  apply (blast intro: terminates.Guard terminates.GuardFault)
  done
lemma [terminates_trivial]:
  "\<lbrakk> \<And>s. \<Gamma> \<turnstile> c1 \<down> Normal s; \<And>s. \<Gamma> \<turnstile> c2 \<down> Normal s \<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> Cond C c1 c2 \<down> Normal s"
  apply (blast intro: terminates.CondTrue terminates.CondFalse)
  done
lemma [terminates_trivial]:
  "\<lbrakk> \<Gamma> \<turnstile> c1 \<down> Normal s; \<And>s. \<Gamma> \<turnstile> c2 \<down> Normal s \<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> c1;;c2 \<down> Normal s"
  apply (erule terminates.Seq)
  apply clarsimp
  apply (case_tac s'; auto)
  done

lemma [terminates_trivial]:
  fixes \<Gamma> return init shows
  "\<lbrakk> \<And>s. \<Gamma> \<turnstile> Call p \<down> Normal s; \<And>s t u. \<Gamma> \<turnstile> c s t \<down> Normal u \<rbrakk> \<Longrightarrow>
   \<Gamma> \<turnstile> call init p return c \<down> Normal s"
  apply (case_tac "\<Gamma> p")
   apply (erule terminates_callUndefined)
  apply (fastforce simp: terminates_Call_body intro: terminates_call)
  done

lemmas [terminates_trivial] =
  terminates.Basic
  terminates.Catch[rule_format]
  terminates.Throw
  terminates.Skip
  terminates.Spec


end
