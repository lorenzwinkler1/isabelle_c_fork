(*<*)
(******************************************************************************
 * A Hoare Calculus for CLean
 *
 * Authors : Burkhart Wolff
 * 
 * Copyright (c) 2018-2019 Université Paris-Saclay, France
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
(*>*)

theory Hoare_Clean
  imports Hoare_MonadSE
          Clean
begin


subsection\<open>Clean Control Rules\<close>

lemma break1: "\<lbrace>\<lambda>\<sigma>.  P (\<sigma> \<lparr> break_status := True \<rparr>) \<rbrace> break \<lbrace>\<lambda>r \<sigma>.  P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def break_def unit_SE_def by auto

lemma unset_break1: "\<lbrace>\<lambda>\<sigma>.  P (\<sigma> \<lparr> break_status := False \<rparr>) \<rbrace> unset_break_status \<lbrace>\<lambda>r \<sigma>. P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def unset_break_status_def unit_SE_def by auto

lemma set_return1: "\<lbrace>\<lambda>\<sigma>.  P (\<sigma> \<lparr> return_status := True \<rparr>) \<rbrace> set_return_status \<lbrace>\<lambda>r \<sigma>. P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def set_return_status_def unit_SE_def by auto

lemma unset_return1: "\<lbrace>\<lambda>\<sigma>.  P (\<sigma> \<lparr> return_status := False \<rparr>) \<rbrace> unset_return_status \<lbrace>\<lambda>r \<sigma>. P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def unset_return_status_def unit_SE_def by auto


subsection\<open>Clean Skip Rules\<close>

lemma assign_global_skip:
"\<lbrace>\<lambda>\<sigma>.   exec_stop \<sigma> \<and> P \<sigma> \<rbrace>  assign_global upd rhs  \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def
  by (simp add: assign_def assign_global_def)

lemma assign_local_skip:
"\<lbrace>\<lambda>\<sigma>.   exec_stop \<sigma> \<and> P \<sigma> \<rbrace> assign_local upd rhs  \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def
  by (simp add: assign_def assign_local_def)

lemma return_skip:
"\<lbrace>\<lambda>\<sigma>.  exec_stop \<sigma> \<and> P \<sigma> \<rbrace> return\<^sub>C upd rhs \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding hoare\<^sub>3_def return\<^sub>C_def unit_SE_def assign_local_def assign_def bind_SE'_def bind_SE_def
  by auto

lemma assign_clean_skip:
"\<lbrace>\<lambda>\<sigma>.   exec_stop \<sigma> \<and> P \<sigma> \<rbrace>  assign tr  \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def
  by (simp add: assign_def assign_def)

lemma if_clean_skip:
"\<lbrace>\<lambda>\<sigma>.   exec_stop \<sigma> \<and> P \<sigma> \<rbrace>  if\<^sub>C C then E else F fi \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def if_SE_def
  by (simp add: if_C_def)

lemma while_clean_skip:
"\<lbrace>\<lambda>\<sigma>.   exec_stop \<sigma> \<and> P \<sigma> \<rbrace>  while\<^sub>C cond do body od  \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def while_C_def 
  by auto

lemma if_opcall_skip:
"\<lbrace>\<lambda>\<sigma>.   exec_stop \<sigma> \<and> P \<sigma>\<rbrace> (call\<^sub>C M A\<^sub>1) \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma>\<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def call\<^sub>C_def
  by simp

lemma if_funcall_skip:
"\<lbrace>\<lambda>\<sigma>. exec_stop \<sigma> \<and> P \<sigma>\<rbrace>(p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C fun E ; assign_local upd (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p)) \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma>\<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def call\<^sub>C_def assign_local_def assign_def
  by (simp add: bind_SE_def)

lemma if_funcall_skip':
"\<lbrace>\<lambda>\<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>(p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C fun E ; assign_global upd (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p)) \<lbrace>\<lambda>r \<sigma>. exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def call\<^sub>C_def assign_global_def assign_def
  by (simp add: bind_SE_def)




subsection\<open>Clean Assign Rules\<close>


lemma assign_global:
  assumes * : "\<sharp> upd"
  shows "\<lbrace>\<lambda>\<sigma>. \<not>exec_stop \<sigma> \<and> P (upd (\<lambda>_. rhs \<sigma>) \<sigma>) \<rbrace> 
         assign_global upd rhs 
         \<lbrace>\<lambda>r \<sigma>. \<not>exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def assign_global_def  assign_def
  by(auto simp: assms)

lemma assign_local:
  assumes * : "\<sharp> (upd \<circ> map_hd)"
  shows "\<lbrace>\<lambda>\<sigma>.  \<not> exec_stop \<sigma> \<and> P ((upd \<circ> map_hd) (\<lambda>_. rhs \<sigma>) \<sigma>) \<rbrace>  
          assign_local upd rhs  
         \<lbrace>\<lambda>r \<sigma>. \<not> exec_stop \<sigma> \<and> P \<sigma> \<rbrace>"
  unfolding    hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def assign_local_def  assign_def
  using assms exec_stop_vs_control_independence by fastforce

lemma return_assign:
  assumes * : "\<sharp> (upd \<circ> map_hd)"
  shows "\<lbrace>\<lambda> \<sigma>. \<not> exec_stop \<sigma> \<and> P ((upd \<circ> map_hd) (\<lambda>_. rhs \<sigma>) (\<sigma> \<lparr> return_status := True \<rparr>))\<rbrace> 
          return\<^sub>C upd rhs
         \<lbrace>\<lambda>r \<sigma>. P \<sigma> \<rbrace>"
  unfolding return\<^sub>C_def hoare\<^sub>3_def skip\<^sub>S\<^sub>E_def unit_SE_def assign_local_def assign_def 
            set_return_status_def bind_SE'_def bind_SE_def 
  proof (auto)
  fix \<sigma> :: "'b control_state_scheme"
    assume a1: "P (upd (map_hd (\<lambda>_. rhs \<sigma>)) (\<sigma>\<lparr>return_status := True\<rparr>))"
  assume "\<not> exec_stop \<sigma>"
  then have f2: "\<not> exec_stop ((upd \<circ> map_hd) (\<lambda>a. rhs \<sigma>) \<lparr>break_status = break_status \<sigma>, return_status = return_status \<sigma>, \<dots> = more \<sigma>\<rparr>)"
    by (metis (full_types) assms exec_stop_vs_control_independence surjective)
    have f3: "(upd \<circ> map_hd) (\<lambda>a. rhs \<sigma>) \<lparr>break_status = break_status \<sigma>, return_status = return_status \<sigma>, \<dots> = more \<sigma>\<rparr> = upd (map_hd (\<lambda>a. rhs \<sigma>)) \<sigma>"
      by (metis comp_def surjective)
  then have "\<lparr>break_status = break_status (upd (map_hd (\<lambda>a. rhs \<sigma>)) \<sigma>), return_status = return_status (upd (map_hd (\<lambda>a. rhs \<sigma>)) \<sigma>), \<dots> = more (upd (map_hd (\<lambda>a. rhs \<sigma>)) \<sigma>)\<rparr> = \<lparr>break_status = False, return_status = False, \<dots> = more (upd (map_hd (\<lambda>a. rhs \<sigma>)) \<sigma>)\<rparr>"
  using f2 by (simp add: exec_stop_def)
  then have "\<not> exec_stop \<lparr>break_status = False, return_status = True, \<dots> = more (upd (map_hd (\<lambda>a. rhs \<sigma>)) \<sigma>)\<rparr>"
      using f3 f2 by (metis (no_types) assms exec_stop_vs_control_independence exec_stop_vs_control_independence' surjective update_convs(2))
    then have f4: "upd (map_hd (\<lambda>a. rhs \<sigma>)) (\<sigma>\<lparr>return_status := True\<rparr>) = \<lparr>break_status = False, return_status = True, \<dots> = more (upd (map_hd (\<lambda>a. rhs \<sigma>)) \<sigma>)\<rparr>"
      by (simp add: exec_stop_def)
    have "upd (map_hd (\<lambda>a. rhs \<sigma>)) \<sigma> = \<lparr>break_status = False, return_status = False, \<dots> = more (upd (map_hd (\<lambda>a. rhs \<sigma>)) \<sigma>)\<rparr>"
      using f3 f2 by (simp add: exec_stop_def)
    then show "P (upd (map_hd (\<lambda>a. rhs \<sigma>)) \<sigma> \<lparr>return_status := True\<rparr>)"
      using f4 a1 by (metis (no_types) update_convs(2))
  qed
  (* do we need independence of rhs ? Not really. 'Normal' programs would never
     be control-state dependent, and 'artificial' ones would still be correct ...*)


subsection\<open>Clean Construct Rules\<close>

lemma cond_clean : 
  "    \<lbrace>\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> P \<sigma> \<and> cond \<sigma>\<rbrace> M \<lbrace>Q\<rbrace>
   \<Longrightarrow> \<lbrace>\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> P \<sigma> \<and> \<not> cond \<sigma>\<rbrace> M' \<lbrace>Q\<rbrace>  
   \<Longrightarrow> \<lbrace>\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> P \<sigma>\<rbrace> if\<^sub>C cond then M else M' fi\<lbrace>Q\<rbrace>"
  unfolding hoare\<^sub>3_def hoare\<^sub>3'_def bind_SE_def if_SE_def
  by (simp add: if_C_def)


lemma while_clean :
  assumes  * : "\<lbrace>\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> cond \<sigma> \<and> P \<sigma>\<rbrace>  M \<lbrace>\<lambda>_. P\<rbrace>"
  and cond_idpc : "\<forall>x \<sigma>.  (cond (\<sigma>\<lparr>break_status := x\<rparr>)) = cond \<sigma> "
  and inv_idpc : "\<forall>x \<sigma>.  (P (\<sigma>\<lparr>break_status := x\<rparr>)) = P \<sigma> "
  and measure: "\<forall>\<sigma>. \<not> exec_stop \<sigma> \<and> cond \<sigma> \<and> P \<sigma> \<longrightarrow> M \<sigma> \<noteq> None \<and> f(snd(the(M \<sigma>))) < ((f \<sigma>)::nat) "
  shows        "\<lbrace>\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> P \<sigma>\<rbrace> while\<^sub>C cond do M od \<lbrace>\<lambda>_ \<sigma>. (exec_stop \<sigma> \<or> \<not>cond \<sigma>) \<and> P \<sigma>\<rbrace>"
  unfolding while_C_def hoare\<^sub>3_def hoare\<^sub>3'_def
  apply simp
  apply(simp only: hoare\<^sub>3_def[symmetric])
  apply(rule sequence') prefer 2 
   apply(rule  Hoare_Clean.unset_break1)
  apply(simp add: cond_idpc inv_idpc)
  oops
  find_theorems unset_break_status


  text\<open>Consequence and Sequence rules where inherited from the underlying Hoare-Monad theory.\<close>


end





