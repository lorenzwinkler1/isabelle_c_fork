(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_lib_Gogolla_challenge_integer.thy --- Example using the OCL library.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013      Universite Paris-Sud, France
 *               2013      IRT SystemX, France
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
(* $Id:$ *)

header{* Gogolla's challenge on Sets *}

theory
  OCL_lib_Gogolla_challenge_integer
imports
  OCL_lib_Gogolla_challenge
begin

section{* Properties: OclIncluding *}
subsection{* Commutativity *}

lemma including_swap_ :
 assumes S_def : "\<tau> \<Turnstile> \<delta> S"
     and i_val : "\<tau> \<Turnstile> \<upsilon> i"
     and j_val : "\<tau> \<Turnstile> \<upsilon> j"
   shows "\<tau> \<Turnstile> ((S :: ('\<AA>, int option option) Set)->including(i)->including(j) \<doteq> (S->including(j)->including(i)))"
by(rule including_swap__generic[OF includes_execute_int StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_refl StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid including_includes], simp_all add: assms)

lemma including_swap' : "\<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ((S :: ('\<AA>, int option option) Set)->including(i)->including(j) \<tau> = (S->including(j)->including(i)) \<tau>)"
by(rule including_swap'_generic[OF including_swap_0_generic[OF includes_execute_int StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_refl StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid including_includes]])

lemma including_swap : "\<forall>\<tau>. \<tau> \<Turnstile> \<delta> S \<Longrightarrow> \<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> i \<Longrightarrow> \<forall>\<tau>. \<tau> \<Turnstile> \<upsilon> j \<Longrightarrow> ((S :: ('\<AA>, int option option) Set)->including(i)->including(j) = (S->including(j)->including(i)))"
by(rule including_swap_generic[OF including_swap_0_generic[OF includes_execute_int StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_refl StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid including_includes]])

section{* Properties: (with comp fun commute) OclIncluding *}
subsection{* Preservation of comp fun commute (instance) *}

lemma including_commute : "EQ_comp_fun_commute (\<lambda>j (r2 :: ('\<AA>, int option option) Set). (r2->including(j)))"
by(rule including_commute_generic[OF including_swap'_generic[OF including_swap_0_generic[OF includes_execute_int StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_refl StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid including_includes]]])

lemma including_commute2 :
 assumes i_int : "is_int i"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). ((acc->including(x))->including(i)))"
by(rule including_commute2_generic[OF including_swap'_generic[OF including_swap_0_generic[OF includes_execute_int StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_refl StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid including_includes]]], simp_all add: assms)

lemma including_commute3 :
 assumes i_int : "is_int i"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). acc->including(i)->including(x))"
by(rule including_commute3_generic[OF including_swap'_generic[OF including_swap_0_generic[OF includes_execute_int StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_refl StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid including_includes]]], simp_all add: assms)

lemma including_commute4 :
 assumes i_int : "is_int i"
     and j_int : "is_int j"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). acc->including(i)->including(x)->including(j))"
by(rule including_commute4_generic[OF including_swap'_generic[OF including_swap_0_generic[OF includes_execute_int StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_refl StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid including_includes]]], simp_all add: assms)

lemma including_commute5 :
 assumes i_int : "is_int i"
     and j_int : "is_int j"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). acc->including(x)->including(j)->including(i))"
by(rule including_commute5_generic[OF including_swap'_generic[OF including_swap_0_generic[OF includes_execute_int StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_refl StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid including_includes]]], simp_all add: assms)

lemma including_commute6 :
 assumes i_int : "is_int i"
     and j_int : "is_int j"
   shows "EQ_comp_fun_commute (\<lambda>x (acc :: ('\<AA>, int option option) Set). acc->including(i)->including(j)->including(x))"
by(rule including_commute6_generic[OF including_swap'_generic[OF including_swap_0_generic[OF includes_execute_int StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_refl StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_defined_args_valid including_includes]]], simp_all add: assms)

section{* Properties: (with comp fun commute) OclIterate and OclIncluding *}
subsection{* Identity *}

lemma i_including_id' :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
   shows "(Finite_Set.fold (\<lambda>j r2. r2->including(j)) S ((\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil>)) \<tau> = S \<tau>"
by(rule i_including_id'_generic[OF including_commute], simp_all add: assms)

lemma iterate_including_id :
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
     shows "(S ->iterate(j;r2=S | r2->including(j))) = S"
by(rule iterate_including_id_generic[OF including_commute], simp_all add: assms)

lemma i_including_id00 :
 assumes S_all_int : "\<And>\<tau>. all_int_set ((\<lambda>a (\<tau>:: '\<AA> st). a) ` \<lceil>\<lceil>Rep_Set_0 ((S :: ('\<AA>, int option option) Set) \<tau>)\<rceil>\<rceil>)"
   shows "\<And>\<tau>. \<forall>S'. (\<forall>\<tau>. all_defined \<tau> S') \<longrightarrow> (let img = image (\<lambda>a (\<tau>:: '\<AA> st). a) ; set' = img \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> ; f = (\<lambda>x. x) in
              (\<forall>\<tau>. f ` set' = img \<lceil>\<lceil>Rep_Set_0 (S' \<tau>)\<rceil>\<rceil>) \<longrightarrow>
              (Finite_Set.fold (\<lambda>j r2. r2->including(f j)) Set{} set') = S')"
by(rule i_including_id00_generic[OF including_commute], simp_all add: assms)

lemma iterate_including_id00 :
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
       and S_incl : "\<And>\<tau> \<tau>'. S \<tau> = S \<tau>'"
     shows "(S->iterate(j;r2=Set{} | r2->including(j))) = S"
by(rule iterate_including_id00_generic[OF including_commute], simp_all add: assms)

subsection{* all defined (construction) *}

lemma preserved_defined :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> (A :: ('\<AA>, int option option) Set)"
   shows "let S' = (\<lambda>a \<tau>. a) ` \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> in
          \<forall>\<tau>. all_defined \<tau> (Finite_Set.fold (\<lambda>x acc. (acc->including(x))) A S')"
by(rule preserved_defined_generic[OF including_commute S_all_def], simp_all add: assms)

subsection{* Preservation of comp fun commute (main) *}

lemma iterate_including_commute_var :
 assumes f_comm : "EQ_comp_fun_commute0 (\<lambda>x. (F :: '\<AA> Integer
                                  \<Rightarrow> ('\<AA>, _) Set
                                  \<Rightarrow> ('\<AA>, _) Set) (\<lambda>_. x))"
     and f_empty : "\<And>x y.
            is_int (\<lambda>(_:: '\<AA> st). x) \<Longrightarrow>
            is_int (\<lambda>(_:: '\<AA> st). y) \<Longrightarrow>
                OclIterate Set{\<lambda>(_:: '\<AA> st). x, a} Set{\<lambda>(_:: '\<AA> st). x, a} F->including(\<lambda>(_:: '\<AA> st). y) =
                OclIterate Set{\<lambda>(_:: '\<AA> st). y, a} Set{\<lambda>(_:: '\<AA> st). y, a} F->including(\<lambda>(_:: '\<AA> st). x)"
     and com : "\<And>S x y \<tau>.
            is_int (\<lambda>(_:: '\<AA> st). x) \<Longrightarrow>
            is_int (\<lambda>(_:: '\<AA> st). y) \<Longrightarrow>
            \<forall>(\<tau> :: '\<AA> st). all_defined \<tau> S \<Longrightarrow>
            \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
                (OclIterate (((OclIterate S S F)->including(a))->including(\<lambda>(_:: '\<AA> st). x)) (((OclIterate S S F)->including(a))->including(\<lambda>(_:: '\<AA> st). x)) F)->including(\<lambda>(_:: '\<AA> st). y) \<tau> =
                (OclIterate (((OclIterate S S F)->including(a))->including(\<lambda>(_:: '\<AA> st). y)) (((OclIterate S S F)->including(a))->including(\<lambda>(_:: '\<AA> st). y)) F)->including(\<lambda>(_:: '\<AA> st). x) \<tau> "
     and a_int : "is_int a"
   shows "EQ_comp_fun_commute0 (\<lambda>x r1. (((r1 ->iterate(j;r2=r1 | F j r2))->including(a))->including(\<lambda>(_:: '\<AA> st). x)))"
by(rule iterate_including_commute_var_generic[OF including_swap], simp_all add: assms)

subsection{* Execution OclIncluding out of OclIterate (theorem) *}

lemma including_out1 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and i_int : "is_int i"
     shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow>
            ((S :: ('\<AA>, _) Set)->iterate(x;acc=A | acc->including(x)->including(i))) \<tau> = (S->iterate(x;acc=A | acc->including(x))->including(i)) \<tau>"
by(rule including_out1_generic[OF including_commute including_commute2 including_swap], simp_all add: assms)

lemma including_out2 :
 assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
     and A_all_def : "\<And>\<tau>. all_defined \<tau> A"
     and i_int : "is_int i"
     and x0_int : "is_int x0"
     shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S->iterate(x;acc=A | acc->including(x0)->including(x)->including(i))) \<tau> = (S->iterate(x;acc=A | acc->including(x0)->including(x))->including(i)) \<tau>"
 apply(rule including_out2_generic[OF including_commute including_commute2 including_commute3 including_commute4 including_commute5 including_swap including_out1])
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
 apply(simp add: assms)
by(rule preserved_defined, simp_all add: assms)

lemma including_out0 :
   assumes S_all_def : "\<And>\<tau>. all_defined \<tau> (S :: ('\<AA>, int option option) Set)"
       and S_include : "\<And>\<tau> \<tau>'. S \<tau> = S \<tau>'"
       and S_notempty : "\<And>\<tau>. \<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {}"
       and a_int : "is_int a"
     shows "(S->iterate(x;acc=Set{a} | acc->including(x))) = (S->including(a))"
by(rule including_out0_generic[OF including_commute], simp_all add: assms)

subsection{* Execution OclIncluding out of OclIterate (corollary) *}

lemma iterate_including_id_out :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, int option option) Set)"
     and a_int : "is_int a"
   shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate(j;r2=S | r2->including(a)->including(j))) \<tau> = S->including(a) \<tau>"
by(rule iterate_including_id_out_generic[OF including_commute including_commute2 including_commute3 including_swap including_out1], simp_all add: assms)

lemma iterate_including_id_out' :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, int option option) Set)"
     and a_int : "is_int a"
   shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate(j;r2=S | r2->including(j)->including(a))) \<tau> = S->including(a) \<tau>"
by(rule iterate_including_id_out'_generic[OF including_commute including_out1], simp_all add: assms)

lemma iterate_including_id_out'''' :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, int option option) Set)"
     and a_int : "is_int a"
     and b_int : "is_int b"
   shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate(j;r2=S | r2->including(a)->including(j)->including(b))) \<tau> = S->including(a)->including(b) \<tau>"
by(rule iterate_including_id_out''''_generic[OF including_out2 including_commute3 iterate_including_id_out], simp_all add: assms)

lemma iterate_including_id_out''' :
 assumes S_def : "\<And>\<tau>. all_defined \<tau> (S:: ('\<AA>, int option option) Set)"
     and a_int : "is_int a"
     and b_int : "is_int b"
   shows "\<lceil>\<lceil>Rep_Set_0 (S \<tau>)\<rceil>\<rceil> \<noteq> {} \<Longrightarrow> (S ->iterate(j;r2=S | r2->including(a)->including(b)->including(j))) \<tau> = S->including(a)->including(b) \<tau>"
by(rule iterate_including_id_out'''_generic[OF including_commute4 including_commute6 including_swap iterate_including_id_out''''], simp_all add: assms)

section{* Conclusion *}

lemma GogollasChallenge_on_sets:
      "\<tau> \<Turnstile> (Set{ \<six>,\<eight> } ->iterate(i;r1=Set{\<nine>}|
                        r1->iterate(j;r2=r1|
                                    r2->including(\<zero>)->including(i)->including(j)))) \<doteq> Set{\<zero>, \<six>, \<eight>, \<nine>}"
proof -
 have val_0 : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> \<zero>" by simp
 have val_6 : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> \<six>" by simp
 have val_8 : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> \<eight>" by simp
 have val_9 : "\<And>\<tau>. \<tau> \<Turnstile> \<upsilon> \<nine>" by simp
 have OclInt0_int : "is_int \<zero>" by (metis StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict' foundation1 is_int_def null_non_OclInt0 OclInt0_def valid4)
 have OclInt6_int : "is_int \<six>" by (metis StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict' foundation1 is_int_def null_non_OclInt6 OclInt6_def valid4)
 have OclInt8_int : "is_int \<eight>" by (metis StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict' foundation1 is_int_def null_non_OclInt8 OclInt8_def valid4)
 have OclInt9_int : "is_int \<nine>" by (metis StrictRefEq\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_strict' foundation1 is_int_def null_non_OclInt9 OclInt9_def valid4)
 show ?thesis
 by(rule GogollasChallenge_on_sets_generic[OF val_0 val_6 val_8 val_9 OclInt0_int OclInt6_int OclInt8_int OclInt9_int including_commute including_commute2 including_commute3 including_commute4 including_commute6 including_swap iterate_including_id iterate_including_id_out iterate_including_id_out' iterate_including_id_out''' iterate_including_id_out'''' including_swap' iterate_including_commute_var including_out0 including_out1 including_out2])
qed

end
