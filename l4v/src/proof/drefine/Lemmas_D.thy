(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(* Collects general lemmas in the capDL refinement proof.
   Those should eventually be moved to Lib.

   Also defines a single entry point for all drefine theories
   in which global simpset and notation changes can be made.
*)

theory Lemmas_D
imports
  "DBaseRefine.Include_D"
  MoreHOL
  MoreCorres
  "ExecSpec.InvocationLabels_H"
begin

no_notation bind_drop (infixl ">>" 60)

declare fun_upd_restrict_conv[simp del]

(* FIXME: move *)
lemma nonempty_pick_in:
  "a \<noteq> {} \<Longrightarrow> pick a \<in> a"
  by (metis all_not_in_conv someI_ex)

lemma pick_singleton[simp]:
  "pick {a} = a"
  apply (rule ccontr)
  apply (cut_tac nonempty_pick_in)
   apply fastforce
  apply fastforce
  done

(* FIXME: eventually move to AInvs *)
lemma is_tcb_TCB[simp]: "is_tcb (TCB t)"
  by (simp add: is_tcb)

declare dxo_wp_weak[wp del]
declare is_aligned_no_overflow[simp]

end
