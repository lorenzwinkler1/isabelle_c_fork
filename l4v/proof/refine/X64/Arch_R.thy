(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
  Top level architecture related proofs.
*)

theory Arch_R
imports Untyped_R Finalise_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)

declare is_aligned_shiftl [intro!]
declare is_aligned_shiftr [intro!]

definition
  "asid_ci_map i \<equiv>
  case i of X64_A.MakePool frame slot parent base \<Rightarrow>
  X64_H.MakePool frame (cte_map slot) (cte_map parent) base"

definition
  "valid_aci' aci \<equiv> case aci of MakePool frame slot parent base \<Rightarrow>
  \<lambda>s. cte_wp_at' (\<lambda>c. cteCap c = NullCap) slot s \<and>
      cte_wp_at' (\<lambda>cte. \<exists>idx.  cteCap cte = UntypedCap False frame pageBits idx) parent s \<and>
      descendants_of' parent (ctes_of s) = {} \<and>
      slot \<noteq> parent \<and>
      ex_cte_cap_to' slot s \<and>
      sch_act_simple s \<and>
      is_aligned base asid_low_bits \<and> base \<le> 2^asid_bits - 1"

lemma vp_strgs':
  "valid_pspace' s \<longrightarrow> pspace_distinct' s"
  "valid_pspace' s \<longrightarrow> pspace_aligned' s"
  "valid_pspace' s \<longrightarrow> valid_mdb' s"
  by auto

lemma safe_parent_strg':
  "cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap False frame pageBits idx) p s \<and>
   descendants_of' p (ctes_of s) = {} \<and>
   valid_pspace' s
  \<longrightarrow> safe_parent_for' (ctes_of s) p (ArchObjectCap (ASIDPoolCap frame base))"
  apply (clarsimp simp: safe_parent_for'_def cte_wp_at_ctes_of)
  apply (case_tac cte)
  apply (simp add: isCap_simps)
  apply (subst conj_comms)
  apply (rule context_conjI)
   apply (drule ctes_of_valid_cap', fastforce)
   apply (clarsimp simp: valid_cap'_def capAligned_def)
   apply (drule is_aligned_no_overflow)
   apply (clarsimp simp: capRange_def asid_low_bits_def bit_simps)
  apply (clarsimp simp: sameRegionAs_def2 isCap_simps capRange_def asid_low_bits_def bit_simps)
  done

lemma descendants_of'_helper:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q (descendants_of' t (null_filter' (ctes_of s)))\<rbrace>
   \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. Q (descendants_of' t (ctes_of s))\<rbrace>"
  apply (clarsimp simp:valid_def)
  apply (subst null_filter_descendants_of')
  prefer 2
   apply fastforce
  apply simp
  done

lemma createObject_typ_at':
  "\<lbrace>\<lambda>s.  koTypeOf ty = otype \<and> is_aligned ptr (objBitsKO ty) \<and>
         pspace_aligned' s \<and> pspace_no_overlap' ptr (objBitsKO ty) s\<rbrace>
   createObjects' ptr (Suc 0) ty 0
   \<lbrace>\<lambda>rv s. typ_at' otype ptr s\<rbrace>"
  apply (clarsimp simp:createObjects'_def alignError_def split_def | wp hoare_unless_wp | wpc )+
    apply (simp add:obj_at'_def)+
   apply (wp hoare_unless_wp)+
  apply (clarsimp simp:ko_wp_at'_def typ_at'_def pspace_distinct'_def)+
  apply (subgoal_tac "ps_clear ptr (objBitsKO ty)
    (s\<lparr>ksPSpace := \<lambda>a. if a = ptr then Some ty else ksPSpace s a\<rparr>)")
  apply (simp add:ps_clear_def)+
  apply (rule ccontr)
  apply (drule int_not_emptyD)
  apply clarsimp
  apply (unfold pspace_no_overlap'_def)
  apply (erule allE)+
  apply (erule(1) impE)
  apply (subgoal_tac "x \<in> {x..x + 2 ^ objBitsKO y - 1}")
   apply (fastforce simp:is_aligned_neg_mask_eq p_assoc_help)
  apply (drule(1) pspace_alignedD')
  apply (clarsimp simp: is_aligned_no_wrap' p_assoc_help)
  done

lemma retype_region2_ext_retype_region_ArchObject:
  "retype_region ptr n us (ArchObject x)=
  retype_region2 ptr n us (ArchObject x)"
  apply (rule ext)
  apply (simp add:retype_region_def retype_region2_def bind_assoc
    retype_region2_ext_def retype_region_ext_def default_ext_def)
  apply (rule ext)
  apply (intro monad_eq_split_tail ext)+
     apply simp
    apply simp
   apply (simp add:gets_def get_def bind_def return_def simpler_modify_def )
   apply (rule_tac x = xc in fun_cong)
   apply (rule_tac f = do_extended_op in arg_cong)
   apply (rule ext)
   apply simp
  apply simp
  done

lemma set_cap_device_and_range_aligned:
  "is_aligned ptr sz \<Longrightarrow> \<lbrace>\<lambda>_. True\<rbrace>
    set_cap
     (cap.UntypedCap dev ptr sz idx)
     aref
    \<lbrace>\<lambda>rv s.
        \<exists>slot.
           cte_wp_at
            (\<lambda>c. cap_is_device c = dev \<and>
                 up_aligned_area ptr sz \<subseteq> cap_range c)
            slot s\<rbrace>"
  apply (subst is_aligned_neg_mask_eq[symmetric])
   apply simp
  apply (wp set_cap_device_and_range)
  done

lemma pac_corres:
  "asid_ci_map i = i' \<Longrightarrow>
  corres dc
         (einvs and ct_active and valid_aci i)
         (invs' and ct_active' and valid_aci' i')
         (perform_asid_control_invocation i)
         (performASIDControlInvocation i')"
  apply (cases i)
  apply (rename_tac word1 prod1 prod2 word2)
  apply (clarsimp simp: asid_ci_map_def)
  apply (simp add: perform_asid_control_invocation_def placeNewObject_def2
                   performASIDControlInvocation_def)
  apply (rule corres_name_pre)
  apply (clarsimp simp:valid_aci_def valid_aci'_def cte_wp_at_ctes_of cte_wp_at_caps_of_state)
  apply (subgoal_tac "valid_cap' (capability.UntypedCap False word1 pageBits idx) s'")
   prefer 2
   apply (case_tac ctea)
   apply clarsimp
   apply (erule ctes_of_valid_cap')
   apply fastforce
  apply (frule valid_capAligned)
  apply (clarsimp simp: capAligned_def page_bits_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       prefer 2
       apply (erule detype_corres)
       apply (simp add:pageBits_def)
      apply (rule corres_split[OF _ getSlotCap_corres])
         apply (rule_tac F = " pcap = (cap.UntypedCap False word1 pageBits idxa)" in corres_gen_asm)
         apply (rule corres_split[OF _ updateFreeIndex_corres])
             apply (rule corres_split)
                prefer 2
                apply (simp add: retype_region2_ext_retype_region_ArchObject )
                apply (rule corres_retype [where ty="Inl (KOArch (KOASIDPool F))",
                                           unfolded APIType_map2_def makeObjectKO_def,
                                           THEN createObjects_corres',simplified,
                                           where val = "makeObject::asidpool"])
                      apply simp
                     apply (simp add: objBits_simps obj_bits_api_def arch_kobj_size_def
                                      default_arch_object_def archObjSize_def)+
                  apply (simp add: obj_relation_retype_def default_object_def
                                   default_arch_object_def objBits_simps archObjSize_def)
                  apply (simp add: other_obj_relation_def asid_pool_relation_def)
                  apply (simp add: makeObject_asidpool const_def inv_def)
                 apply (rule range_cover_full)
                  apply (simp add:obj_bits_api_def arch_kobj_size_def default_arch_object_def)+
               apply (rule corres_split)
                  prefer 2
                  apply (rule cins_corres_simple, simp, rule refl, rule refl)
                 apply (rule_tac F="is_aligned word2 asid_low_bits" in corres_gen_asm)
                 apply (simp add: is_aligned_mask dc_def[symmetric])
                 apply (rule corres_split [where P=\<top> and P'=\<top> and r'="\<lambda>t t'. t = t' o ucast"])
                    prefer 2
                    apply (clarsimp simp: state_relation_def arch_state_relation_def)
                   apply (rule corres_trivial)
                   apply (rule corres_modify)
                   apply (thin_tac "x \<in> state_relation" for x)
                   apply (clarsimp simp: state_relation_def arch_state_relation_def o_def)
                   apply (rule ext)
                   apply clarsimp
                   apply (erule_tac P = "x = asid_high_bits_of word2" in notE)
                   apply (rule word_eqI[rule_format])
                   apply (drule_tac x1="ucast x" in bang_eq [THEN iffD1])
                   apply (erule_tac x=n in allE)
                   apply (simp add: word_size nth_ucast)
                  apply wp+
              apply (strengthen safe_parent_strg[where idx = "2^pageBits"])
              apply (strengthen invs_valid_objs invs_distinct
                                invs_psp_aligned invs_mdb
                     | simp cong:conj_cong)+
              apply (wp retype_region_plain_invs[where sz = pageBits]
                        retype_cte_wp_at[where sz = pageBits])+
             apply (strengthen vp_strgs'
                    safe_parent_strg'[where idx = "2^pageBits"])
             apply (simp cong: conj_cong)
             apply (wp createObjects_valid_pspace'
                       [where sz = pageBits and ty="Inl (KOArch (KOASIDPool undefined))"])
                apply (simp add: makeObjectKO_def)+
               apply (simp add:objBits_simps archObjSize_def range_cover_full)+
             apply (clarsimp simp:valid_cap'_def)
             apply (wp createObject_typ_at'
                       createObjects_orig_cte_wp_at'[where sz = pageBits])
             apply (rule descendants_of'_helper)
             apply (wp createObjects_null_filter'
                       [where sz = pageBits and ty="Inl (KOArch (KOASIDPool undefined))"])
            apply (clarsimp simp:is_cap_simps)
           apply (simp add: free_index_of_def)

          apply (clarsimp simp: conj_comms obj_bits_api_def arch_kobj_size_def
                 objBits_simps archObjSize_def default_arch_object_def
                 pred_conj_def)
          apply (clarsimp simp: conj_comms
                | strengthen invs_mdb invs_valid_pspace)+
          apply (simp add:region_in_kernel_window_def)
          apply (wp set_untyped_cap_invs_simple[where sz = pageBits]
                    set_cap_cte_wp_at
                    set_cap_caps_no_overlap[where sz = pageBits]
                    set_cap_no_overlap
                    set_cap_device_and_range_aligned[where dev = False,simplified]
                    set_untyped_cap_caps_overlap_reserved[where sz = pageBits])+
         apply (clarsimp simp: conj_comms obj_bits_api_def arch_kobj_size_def
                               objBits_simps archObjSize_def default_arch_object_def
                               makeObjectKO_def range_cover_full
                         simp del: capFreeIndex_update.simps
                | strengthen invs_valid_pspace' invs_pspace_aligned'
                             invs_pspace_distinct'
                             exI[where x="makeObject :: asidpool"])+
         apply (wp updateFreeIndex_forward_invs'
           updateFreeIndex_pspace_no_overlap'
           updateFreeIndex_caps_no_overlap''
           updateFreeIndex_descendants_of2
           updateFreeIndex_cte_wp_at
           updateFreeIndex_caps_overlap_reserved
             | simp add: descendants_of_null_filter' split del: if_split)+
       apply (wp get_cap_wp)+
     apply (subgoal_tac "word1 && ~~ mask pageBits = word1 \<and> pageBits \<le> word_bits \<and> word_size_bits \<le> pageBits")
      prefer 2
      apply (clarsimp simp:bit_simps word_bits_def is_aligned_neg_mask_eq)
     apply (simp only:delete_objects_rewrite)
     apply wp+
    apply (clarsimp simp: conj_comms)
    apply (clarsimp simp: conj_comms ex_disj_distrib
           | strengthen invs_valid_pspace' invs_pspace_aligned'
                        invs_pspace_distinct')+
    apply (wp deleteObjects_invs'[where p="makePoolParent i'"]
              deleteObjects_cte_wp_at'
              deleteObjects_descendants[where p="makePoolParent i'"])
    apply (clarsimp split del: if_split simp:valid_cap'_def)
    apply (wp hoare_vcg_ex_lift
              deleteObjects_caps_no_overlap''[where slot="makePoolParent i'"]
              deleteObject_no_overlap
              deleteObjects_ct_active'[where cref="makePoolParent i'"])
    apply (clarsimp simp: is_simple_cap_def valid_cap'_def max_free_index_def is_cap_simps
                    cong: conj_cong)
    apply (strengthen empty_descendants_range_in')
    apply (wp deleteObjects_descendants[where p="makePoolParent i'"]
              deleteObjects_cte_wp_at'
              deleteObjects_null_filter[where p="makePoolParent i'"])
   apply (clarsimp simp:invs_mdb max_free_index_def invs_untyped_children)
   apply (subgoal_tac "detype_locale x y sa" for x y)
    prefer 2
    apply (simp add:detype_locale_def)
    apply (fastforce simp:cte_wp_at_caps_of_state descendants_range_def2
            empty_descendants_range_in invs_untyped_children)
   apply (intro conjI)
          apply (clarsimp)
         apply (erule(1) caps_of_state_valid)
        subgoal by (fastforce simp:cte_wp_at_caps_of_state
                descendants_range_def2 empty_descendants_range_in)
       apply (fold_subgoals (prefix))[2]
       subgoal premises prems using prems by (clarsimp simp:invs_def valid_state_def)+
     apply (clarsimp simp:cte_wp_at_caps_of_state)
    apply (drule detype_locale.non_null_present)
     apply (fastforce simp:cte_wp_at_caps_of_state)
    apply simp
   apply (frule_tac ptr = "(aa,ba)" in detype_invariants [rotated 3])
        apply fastforce
       apply simp
      apply (simp add: cte_wp_at_caps_of_state)
     apply (simp add: is_cap_simps)
    apply (simp add:empty_descendants_range_in descendants_range_def2)
   apply (frule intvl_range_conv[where bits = pageBits])
    apply (clarsimp simp:pageBits_def word_bits_def)
   apply (clarsimp simp: invs_valid_objs cte_wp_at_caps_of_state range_cover_full
                         invs_psp_aligned invs_distinct cap_master_cap_simps is_cap_simps
                         is_simple_cap_def)
   apply (clarsimp simp: conj_comms)
   apply (rule conjI,clarsimp)
   apply (frule ex_cte_cap_protects)
        apply (simp add:cte_wp_at_caps_of_state)
       apply (simp add:empty_descendants_range_in)
      apply fastforce
     apply (rule subset_refl)
    apply fastforce
   apply clarsimp
   apply (rule conjI,clarsimp simp:clear_um_def)
   apply (simp add:detype_clear_um_independent)
   apply (rule conjI,erule caps_no_overlap_detype[OF descendants_range_caps_no_overlapI])
     apply (clarsimp simp:is_aligned_neg_mask_eq cte_wp_at_caps_of_state)
     apply (simp add:empty_descendants_range_in)+
   apply (rule conjI)
    apply clarsimp
    apply (drule_tac p = "(aa,ba)" in cap_refs_in_kernel_windowD2[OF caps_of_state_cteD])
     apply fastforce
    apply (clarsimp simp: region_in_kernel_window_def valid_cap_def
                          cap_aligned_def is_aligned_neg_mask_eq detype_def clear_um_def)
   apply (rule conjI, rule pspace_no_overlap_subset,
         rule pspace_no_overlap_detype[OF caps_of_state_valid])
        apply (simp add:invs_psp_aligned invs_valid_objs is_aligned_neg_mask_eq)+
   apply (clarsimp simp: detype_def clear_um_def detype_ext_def valid_sched_def valid_etcbs_def
            st_tcb_at_kh_def obj_at_kh_def st_tcb_at_def obj_at_def is_etcb_at_def)
  apply (simp add: detype_def clear_um_def)
  apply (drule_tac x = "cte_map (aa,ba)" in pspace_relation_cte_wp_atI[OF state_relation_pspace_relation])
    apply (simp add:invs_valid_objs)+
  apply clarsimp
  apply (drule cte_map_inj_eq)
       apply ((fastforce simp:cte_wp_at_caps_of_state)+)[5]
  apply (clarsimp simp:cte_wp_at_caps_of_state invs_valid_pspace' conj_comms cte_wp_at_ctes_of
                       valid_cap_simps')
  apply (strengthen refl)
  apply clarsimp
  apply (frule empty_descendants_range_in')
  apply (intro conjI,
    simp_all add: is_simple_cap'_def isCap_simps descendants_range'_def2
                  null_filter_descendants_of'[OF null_filter_simp']
                  capAligned_def asid_low_bits_def)
      apply (erule descendants_range_caps_no_overlapI')
       apply (fastforce simp:cte_wp_at_ctes_of is_aligned_neg_mask_eq)
      apply (simp add:empty_descendants_range_in')
     apply (simp add:word_bits_def bit_simps)
    apply (rule is_aligned_weaken)
     apply (rule is_aligned_shiftl_self[unfolded shiftl_t2n,where p = 1,simplified])
    apply (simp add:pageBits_def)
   apply clarsimp
   apply (drule(1) cte_cap_in_untyped_range)
        apply (fastforce simp:cte_wp_at_ctes_of)
       apply assumption+
    apply fastforce
   apply simp
  apply clarsimp
  apply (drule (1) cte_cap_in_untyped_range)
       apply (fastforce simp add: cte_wp_at_ctes_of)
      apply assumption+
    apply (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
   apply fastforce
  apply simp
  done

(* FIXME x64: move *)
definition
  ioport_data_relation :: "io_port_invocation_data \<Rightarrow> ioport_invocation_data \<Rightarrow> bool"
where
  "ioport_data_relation d d' \<equiv> case d of
    X64_A.IOPortIn8 \<Rightarrow> d' = IOPortIn8
  | X64_A.IOPortIn16 \<Rightarrow> d' = IOPortIn16
  | X64_A.IOPortIn32 \<Rightarrow> d' = IOPortIn32
  | X64_A.IOPortOut8 w \<Rightarrow> d' = IOPortOut8 w
  | X64_A.IOPortOut16 w \<Rightarrow> d' = IOPortOut16 w
  | X64_A.IOPortOut32 w \<Rightarrow> d' = IOPortOut32 w"

definition
  ioport_invocation_map :: "io_port_invocation \<Rightarrow> ioport_invocation \<Rightarrow> bool"
where
  "ioport_invocation_map i i' \<equiv> case i of
       X64_A.IOPortInvocation iop dat \<Rightarrow> \<exists>dat'. i' = IOPortInvocation iop dat' \<and> ioport_data_relation dat dat'"

definition
  archinv_relation :: "arch_invocation \<Rightarrow> Arch.invocation \<Rightarrow> bool"
where
  "archinv_relation ai ai' \<equiv> case ai of
     arch_invocation.InvokePageTable pti \<Rightarrow>
       \<exists>pti'. ai' = InvokePageTable pti' \<and> page_table_invocation_map pti pti'
   | arch_invocation.InvokePageDirectory pdi \<Rightarrow>
       \<exists>pdi'. ai' = InvokePageDirectory pdi' \<and> page_directory_invocation_map pdi pdi'
   | arch_invocation.InvokePDPT pdpti \<Rightarrow>
       \<exists>pdpti'. ai' = InvokePDPT pdpti' \<and> pdpt_invocation_map pdpti pdpti'
   | arch_invocation.InvokePage pgi \<Rightarrow>
       \<exists>pgi'. ai' = InvokePage pgi' \<and> page_invocation_map pgi pgi'
   | arch_invocation.InvokeASIDControl aci \<Rightarrow>
       \<exists>aci'. ai' = InvokeASIDControl aci' \<and> aci' = asid_ci_map aci
   | arch_invocation.InvokeASIDPool ap \<Rightarrow>
       \<exists>ap'. ai' = InvokeASIDPool ap' \<and>  ap' = asid_pool_invocation_map ap
   | arch_invocation.InvokeIOPort iopi \<Rightarrow>
       \<exists>iopi'. ai' = InvokeIOPort iopi' \<and> ioport_invocation_map iopi iopi'"

definition
  valid_arch_inv' :: "Arch.invocation \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "valid_arch_inv' ai \<equiv> case ai of
     InvokePageTable pti \<Rightarrow> valid_pti' pti
   | InvokePageDirectory pdi \<Rightarrow> valid_pdi' pdi
   | InvokePDPT pdpti \<Rightarrow> valid_pdpti' pdpti
   | InvokePage pgi \<Rightarrow> valid_page_inv' pgi
   | InvokeASIDControl aci \<Rightarrow> valid_aci' aci
   | InvokeASIDPool ap \<Rightarrow> valid_apinv' ap
   | InvokeIOPort i \<Rightarrow> \<top>"

lemma mask_vmrights_corres:
  "maskVMRights (vmrights_map R) (rightsFromWord d) =
  vmrights_map (mask_vm_rights R (data_to_rights d))"
  by (clarsimp simp: rightsFromWord_def data_to_rights_def
                     vmrights_map_def Let_def maskVMRights_def
                     mask_vm_rights_def nth_ucast
                     validate_vm_rights_def vm_read_write_def
                     vm_kernel_only_def vm_read_only_def
               split: bool.splits)

lemma vm_attributes_corres:
  "vmattributes_map (attribs_from_word w) = attribsFromWord w"
  by (clarsimp simp: attribsFromWord_def attribs_from_word_def
                     Let_def vmattributes_map_def)

lemma check_vp_corres:
  "corres (ser \<oplus> dc) \<top> \<top>
          (check_vp_alignment sz w)
          (checkVPAlignment sz w)"
  apply (simp add: check_vp_alignment_def checkVPAlignment_def)
  apply (cases sz, simp_all add: corres_returnOk unlessE_whenE is_aligned_mask)
     apply ((rule corres_guard_imp, rule corres_whenE, rule refl, auto)[1])+
  done

lemma checkVP_wpR [wp]:
  "\<lbrace>\<lambda>s. vmsz_aligned' w sz \<longrightarrow> P () s\<rbrace>
  checkVPAlignment sz w \<lbrace>P\<rbrace>, -"
  apply (simp add: checkVPAlignment_def unlessE_whenE cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_whenE_wp|wpc)+
  apply (simp add: is_aligned_mask vmsz_aligned'_def)
  done

lemma checkVP_inv: "\<lbrace>P\<rbrace> checkVPAlignment sz w \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: checkVPAlignment_def unlessE_whenE cong: vmpage_size.case_cong)
  apply (rule hoare_pre)
   apply (wp hoare_whenE_wp|wpc)+
  apply simp
  done

lemma asidHighBits [simp]:
  "asidHighBits = asid_high_bits"
  by (simp add: asidHighBits_def asid_high_bits_def)

declare word_unat_power [symmetric, simp del]

crunch inv [wp]: "X64_H.decodeInvocation" "P"
  (wp: crunch_wps mapME_x_inv_wp getASID_wp
   simp: forME_x_def crunch_simps

   ignore: forME_x getObject)

(* FIXME: Move *)
lemma case_option_corres:
  assumes nonec: "corres r Pn Qn (nc >>= f) (nc' >>= g)"
  and     somec: "\<And>v'. corres r (Ps v') (Qs v') (sc v' >>= f) (sc' v' >>= g)"
  shows "corres r (case_option Pn Ps v) (case_option Qn Qs v) (case_option nc sc v >>= f) (case_option nc' sc' v >>= g)"
  apply (cases v)
   apply simp
   apply (rule nonec)
  apply simp
  apply (rule somec)
  done

lemma case_option_corresE:
  assumes nonec: "corres r Pn Qn (nc >>=E f) (nc' >>=E g)"
  and     somec: "\<And>v'. corres r (Ps v') (Qs v') (sc v' >>=E f) (sc' v' >>=E g)"
  shows "corres r (case_option Pn Ps v) (case_option Qn Qs v) (case_option nc sc v >>=E f) (case_option nc' sc' v >>=E g)"
  apply (cases v)
   apply simp
   apply (rule nonec)
  apply simp
  apply (rule somec)
  done


lemma cap_relation_Untyped_eq:
  "cap_relation c (UntypedCap d p sz f) = (c = cap.UntypedCap d p sz f)"
  by (cases c) auto

lemma vmsz_aligned_less_kernel_base_eq:
  "\<lbrakk>ptr + 2 ^ pageBitsForSize vmpage_size - 1 < pptr_base;vmsz_aligned ptr vmpage_size\<rbrakk>
   \<Longrightarrow> ptr < pptr_base"
  apply (simp add:vmsz_aligned_def)
  apply (rule ccontr)
  apply (simp add:not_less)
  apply (drule(1) less_le_trans)
  apply (drule is_aligned_no_overflow)
  apply (simp add:not_less[symmetric])
  done

declare check_vp_alignment_inv[wp del]

lemma select_ext_fa:
  "free_asid_select asid_tbl \<in> S
  \<Longrightarrow> ((select_ext (\<lambda>_. free_asid_select asid_tbl) S) :: (3 word) det_ext_monad)
   = return (free_asid_select asid_tbl)"
  by (simp add: select_ext_def get_def gets_def bind_def assert_def return_def fail_def)

lemma select_ext_fap:
  "free_asid_pool_select p b \<in> S
  \<Longrightarrow> ((select_ext (\<lambda>_. free_asid_pool_select p b) S) :: (9 word) det_ext_monad)
   = return (free_asid_pool_select p b)"
  by (simp add: select_ext_def get_def gets_def bind_def assert_def return_def)

lemma page_base_corres[simp]:
  "pageBase vaddr vmsize = page_base vaddr vmsize"
  by (clarsimp simp: pageBase_def page_base_def)

lemma neg_mask_combine:
  "~~ mask a && ~~ mask b = ~~ mask (max a b)"
  by (auto simp: word_ops_nth_size word_size intro!: word_eqI)

lemma vs_lookup_pages1I:
  "\<lbrakk> ko_at ko p s; (r, p') \<in> vs_refs_pages ko;
          rs' = r # rs \<rbrakk> \<Longrightarrow> ((rs,p) \<unrhd>1 (rs',p')) s"
  by (fastforce simp add: vs_lookup_pages1_def)

lemma vs_refs_pages_ptI:
  "pt x = pte \<Longrightarrow> pte_ref_pages pte = Some r'
    \<Longrightarrow> (VSRef (ucast x) (Some APageTable), r') \<in> vs_refs_pages (ArchObj (PageTable pt))"
  apply (simp add: vs_refs_pages_def)
  apply (rule image_eqI[rotated], rule graph_ofI[where x=x], simp)
  apply simp
  done

lemmas vs_refs_pages_pt_smallI
    = vs_refs_pages_ptI[where pte="X64_A.pte.SmallPagePTE x y z" for x y z,
        unfolded pte_ref_pages_def, simplified, OF _ refl]

lemma vs_refs_pages_pdI:
  "pd x = pde \<Longrightarrow> pde_ref_pages pde = Some r'
    \<Longrightarrow> (VSRef (ucast x) (Some APageDirectory), r') \<in> vs_refs_pages (ArchObj (PageDirectory pd))"
  apply (simp add: vs_refs_pages_def)
  apply (rule image_eqI[rotated], rule graph_ofI[where x=x], simp)
  apply simp
  done

lemmas vs_refs_pages_pd_largeI
    = vs_refs_pages_pdI[where pde="X64_A.pde.LargePagePDE x y z " for x y z ,
        unfolded pde_ref_pages_def, simplified, OF _ refl]

lemma vs_refs_pages_pdptI:
  "pdpt x = pdpte \<Longrightarrow> pdpte_ref_pages pdpte = Some r'
    \<Longrightarrow> (VSRef (ucast x) (Some APDPointerTable), r') \<in> vs_refs_pages (ArchObj (PDPointerTable pdpt))"
  apply (simp add: vs_refs_pages_def)
  apply (rule image_eqI[rotated], rule graph_ofI[where x=x], simp)
  apply simp
  done

lemmas vs_refs_pages_pdpt_hugeI
    = vs_refs_pages_pdptI[where pdpte="X64_A.pdpte.HugePagePDPTE x y z " for x y z ,
        unfolded pdpte_ref_pages_def, simplified, OF _ refl]

lemma vs_refs_pages_pml4I:
  "pml4 x = pml4e \<Longrightarrow> pml4e_ref_pages pml4e = Some r'
    \<Longrightarrow> x \<notin> kernel_mapping_slots
    \<Longrightarrow> (VSRef (ucast x) (Some APageMapL4), r') \<in> vs_refs_pages (ArchObj (PageMapL4 pml4))"
  apply (simp add: vs_refs_pages_def)
  apply (rule image_eqI[rotated], rule graph_ofI[where x=x], simp)
  apply simp
  done

lemma userVTop_conv[simp]: "userVTop = user_vtop"
  by (simp add: userVTop_def user_vtop_def)

lemma find_vspace_for_asid_lookup_slot [wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs\<rbrace>
  find_vspace_for_asid asid
  \<lbrace>\<lambda>rv. \<exists>\<rhd> (lookup_pml4_slot rv vptr && ~~ mask pml4_bits)\<rbrace>, -"
  apply (rule hoare_pre)
   apply (rule hoare_post_imp_R)
    apply (rule hoare_vcg_R_conj)
     apply (rule hoare_vcg_R_conj)
      apply (rule find_vspace_for_asid_inv [where P="\<top>", THEN valid_validE_R])
     apply (rule find_vspace_for_asid_lookup)
    apply (rule find_vspace_for_asid_aligned_pm)
   apply clarsimp
   apply (subst lookup_pml4_slot_eq)
    apply (auto simp: bit_simps)
  done


lemma decode_page_inv_corres:
  "\<lbrakk>cap = arch_cap.PageCap d p R mt sz opt; acap_relation cap cap';
    list_all2 cap_relation (map fst excaps) (map fst excaps');
    list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps') \<rbrakk> \<Longrightarrow>
     corres (ser \<oplus> archinv_relation)
            (invs and valid_cap (cap.ArchObjectCap cap) and
             cte_wp_at (is_arch_diminished (cap.ArchObjectCap cap)) slot and
             (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>_. True) (snd x) s))
            (invs' and valid_cap' (capability.ArchObjectCap cap') and
             (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' (fst x) s \<and> cte_wp_at' (\<lambda>_. True) (snd x) s))
            (decode_page_invocation l args slot cap excaps)
            (decodeX64FrameInvocation l args (cte_map slot) cap' excaps')"
  apply (simp add: decode_page_invocation_def decodeX64FrameInvocation_def Let_def isCap_simps split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel X64PageMap")
   apply (case_tac "\<not>(2 < length args \<and> excaps \<noteq> [])")
    apply (auto split: list.split)[1]
   apply (simp add: Let_def neq_Nil_conv)
   apply (elim exE conjE)
   apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
   apply (rule corres_guard_imp)
     apply (rule whenE_throwError_corres)
       apply simp
      apply simp
     apply (simp split: cap.split, intro conjI impI allI, simp_all)[1]
     apply (rename_tac arch_capa)
     apply (case_tac arch_capa, simp_all)[1]
     apply (rename_tac wd opt')
     apply (case_tac opt', simp_all)[1]
     apply (rename_tac optv)
     apply (rule corres_splitEE)
        prefer 2
        apply (rule corres_lookup_error)
        apply (rule_tac P="valid_arch_state and valid_vspace_objs and
                             pspace_aligned and equal_kernel_mappings and valid_global_objs and
                             valid_cap (cap.ArchObjectCap
                                         (arch_cap.PML4Cap wd (Some optv)))"
                     in corres_guard_imp)
          apply (rule find_vspace_for_asid_corres[OF refl])
         apply (clarsimp simp: valid_cap_def)
         apply (simp add: mask_def)
        apply assumption
       apply (rule whenE_throwError_corres, simp, simp)
       apply (rule_tac R="\<lambda>_ s. valid_vspace_objs s \<and> pspace_aligned s
                                  \<and> (hd args && user_vtop) + (2 ^ pageBitsForSize sz - 1) \<le> user_vtop \<and>
                                  valid_arch_state s \<and> equal_kernel_mappings s \<and> valid_global_objs s \<and>
                                  s \<turnstile> (fst (hd excaps)) \<and> (\<exists>\<rhd> (lookup_pml4_slot (obj_ref_of (fst (hd excaps))) (hd args) && ~~ mask pml4_bits)) s \<and>
                                  (\<exists>\<rhd> rv') s \<and> page_map_l4_at rv' s"
                     and R'="\<lambda>_ s. s \<turnstile>' (fst (hd excaps')) \<and> valid_objs' s \<and>
                                    pspace_aligned' s \<and> pspace_distinct' s \<and>
                                    valid_arch_state' s"
                         in corres_splitEE)
          prefer 2
          apply (rule corres_whenE)
            apply (simp add: pptr_base_def X64.pptrBase_def pptrBase_def shiftl_t2n mask_def)
           apply (rule corres_trivial, simp)
          apply simp
         apply (rule corres_guard_imp)
           apply (rule corres_splitEE)
              prefer 2
              apply (rule check_vp_corres)
             apply (rule corres_splitEE)
                prefer 2
                apply (simp only: addrFromPPtr_def)
                apply (rule create_mapping_entries_corres)
                 apply (simp add: mask_vmrights_corres)
                apply (simp add: vm_attributes_corres)
               apply (rule corres_splitEE)
                  prefer 2
                  apply (erule ensure_safe_mapping_corres)
                 apply (rule corres_trivial)
                 apply (rule corres_returnOk)
                 apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
                apply (wpsimp wp: hoare_whenE_wp check_vp_wpR createMappingEntries_wf)+
          apply (clarsimp simp: valid_cap_def  dest!: vmsz_aligned_less_kernel_base_eq)
          apply (frule_tac vptr="hd args && user_vtop" in page_map_l4_pml4e_at_lookupI, assumption)
          apply (clarsimp simp: vmsz_aligned_def pageBitsForSize_def is_aligned_pml4
                         split: vmpage_size.splits)
         apply (clarsimp simp: valid_cap'_def)
        apply (simp add: mask_def)
        apply (rule whenE_throwError_wp[unfolded validE_R_def])
       apply (wp hoare_whenE_wp)+
      apply (rule hoare_drop_imps)+
      apply (simp add:mask_def not_less)
      apply (wp hoare_drop_imps find_vspace_for_asid_lookup_slot[unfolded mask_def, simplified])+
    apply (clarsimp simp: invs_def valid_state_def valid_pspace_def)
   apply fastforce
    -- "PageRemap"
  apply (cases "invocation_type l = ArchInvocationLabel X64PageRemap")
   apply (case_tac "\<not>(1 < length args \<and> excaps \<noteq> [])")
    subgoal by (auto split: list.split)
   apply (simp add: Let_def split: list.split)
   apply (case_tac args, simp)
   apply (clarsimp simp: split_def)
   apply (rename_tac w1 w2 w3)
   apply (case_tac excaps', simp)
   apply clarsimp
   apply (rule corres_guard_imp)
     apply (rule whenE_throwError_corres, simp, simp)
     apply (rule corres_splitEE [where r' = "op ="])
        prefer 2
        apply (clarsimp simp: list_all2_Cons2)
        apply (case_tac "fst (hd excaps)", simp_all)[1]
        apply clarsimp
        apply (rename_tac arch_capa arch_capb)
        apply (case_tac arch_capa, simp_all)[1]
        apply (rename_tac opt')
        apply (case_tac opt', simp_all)[1]
        apply (rule corres_returnOkTT)
        apply simp
       apply (simp add: Let_def split: list.split)
       apply (rule case_option_corresE)
        apply (rule corres_trivial)
        apply simp
       apply simp
       apply (rule corres_splitEE)
          prefer 2
          apply (rule corres_lookup_error, simp)
          apply (rule find_vspace_for_asid_corres[OF refl])
         apply (rule whenE_throwError_corres)
           apply simp
          apply simp
         apply simp
         apply (rule corres_splitEE)
            prefer 2
            apply (rule check_vp_corres)
           apply (rule corres_splitEE)
              prefer 2
              apply (simp only: addrFromPPtr_def)
              apply (rule create_mapping_entries_corres)
               apply (simp add: mask_vmrights_corres)
              apply (simp add: vm_attributes_corres)
             apply (rule corres_trivial)
             apply (rule corres_returnOk)
             apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
            apply (wp)+
          apply (subgoal_tac "valid_vspace_objs s \<and> pspace_aligned s \<and>
                                (snd v') < pptr_base \<and> canonical_address (snd v') \<and>
                                equal_kernel_mappings s \<and> valid_global_objs s \<and> valid_arch_state s \<and>
                                (*(\<exists>\<rhd> (lookup_pml4_slot (fst pa) (snd v') && ~~ mask pml4_bits)) s \<and>*)
                                page_map_l4_at (fst pa) s \<and> (\<exists>\<rhd> (fst pa)) s")
           prefer 2
           apply (case_tac v'; simp only: split_def)
          apply clarsimp
          apply (frule_tac pm = aa and vptr = bc in page_map_l4_pml4e_at_lookupI,assumption)
          apply (clarsimp simp: vmsz_aligned_def pageBitsForSize_def is_aligned_pml4
                         split: vmpage_size.splits)
         apply wp
        apply (wpc | wp throwE_R | wp_once hoare_drop_imps)+
    apply clarsimp
    apply (drule bspec [where x = "excaps ! 0"])
     apply simp
    apply (clarsimp simp: valid_cap_def split: option.split)
    apply (fastforce simp: invs_def valid_state_def valid_pspace_def mask_def)
   apply (clarsimp split: option.split)
   apply fastforce
  -- "PageUnmap"
  apply (simp split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel X64PageUnmap")
   apply simp
   apply (rule corres_returnOk)
   apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
  -- "PageGetAddress"
  apply (cases "invocation_type l = ArchInvocationLabel X64PageGetAddress")
   apply simp
   apply (rule corres_returnOk)
   apply (clarsimp simp: archinv_relation_def page_invocation_map_def)
  by (clarsimp split: invocation_label.splits arch_invocation_label.splits split del: if_split)

lemma VMReadWrite_vmrights_map[simp]: "vmrights_map vm_read_write = VMReadWrite"
  by (simp add: vmrights_map_def vm_read_write_def)

lemma decode_page_table_inv_corres:
  "\<lbrakk>cap = arch_cap.PageTableCap p opt; acap_relation cap cap';
    list_all2 cap_relation (map fst excaps) (map fst excaps');
    list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps') \<rbrakk> \<Longrightarrow>
     corres (ser \<oplus> archinv_relation)
            (invs and valid_cap (cap.ArchObjectCap cap) and
             cte_wp_at (is_arch_diminished (cap.ArchObjectCap cap)) slot and
             (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>_. True) (snd x) s))
            (invs' and valid_cap' (capability.ArchObjectCap cap') and
             (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' (fst x) s \<and> cte_wp_at' (\<lambda>_. True) (snd x) s))
            (decode_page_table_invocation l args slot cap excaps)
            (decodeX64PageTableInvocation l args (cte_map slot) cap' excaps')"
  apply (simp add: decode_page_table_invocation_def decodeX64PageTableInvocation_def Let_def
      isCap_simps
      split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel X64PageTableMap")
   apply (simp split: invocation_label.split arch_invocation_label.splits split del: if_split)
   apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
   apply (clarsimp simp: neq_Nil_conv Let_def)
   apply (rule whenE_throwError_corres_initial, simp+)
   apply (simp split: cap.split arch_cap.split option.split,
             intro conjI allI impI, simp_all)[1]
   apply (rule whenE_throwError_corres_initial, simp+)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE)
        prefer 2
        apply (rule corres_lookup_error)
        apply (rule find_vspace_for_asid_corres[OF refl])
       apply (rule whenE_throwError_corres, simp, simp)
       apply (rule corres_splitEE)
          prefer 2
          apply (rule corres_lookup_error)
          apply (rule lookup_pd_slot_corres)
         apply (rule corres_splitEE)
            prefer 2
            apply simp
            apply (rule get_pde_corres')
           apply (simp add: unlessE_whenE)
           apply (rule corres_splitEE)
              prefer 2
              apply (rule corres_whenE)
                apply clarsimp
                apply (case_tac old_pde; simp )[1]
               apply (rule corres_trivial)
               apply simp
              apply simp
             apply (rule corres_trivial)
             apply (rule corres_returnOk)
             apply (clarsimp simp: archinv_relation_def page_table_invocation_map_def)
             apply (clarsimp simp: attribs_from_word_def filter_frame_attrs_def
                                   attribsFromWord_def Let_def)
            apply ((clarsimp cong: if_cong
                     | wp hoare_whenE_wp hoare_vcg_all_lift_R getPDE_wp get_pde_wp
                     | wp_once hoare_drop_imps)+)[6]
      apply (clarsimp intro!: validE_R_validE)
      apply (rule_tac Q'="\<lambda>rv s.  pspace_aligned s \<and> valid_vspace_objs s \<and> valid_arch_state s \<and>
                           equal_kernel_mappings s \<and> valid_global_objs s \<and>
                           (\<exists>ref. (ref \<rhd> rv) s) \<and> typ_at (AArch APageMapL4) rv s \<and>
                           is_aligned rv pml4_bits"
                       in hoare_post_imp_R[rotated])
       apply fastforce
      apply (wpsimp | wp_once hoare_drop_imps)+
    apply (fastforce simp: valid_cap_def mask_def)
   apply (clarsimp simp: valid_cap'_def)
   apply fastforce
    -- "PageTableUnmap"
  apply (clarsimp simp: isCap_simps)+
  apply (cases "invocation_type l = ArchInvocationLabel X64PageTableUnmap")
   apply (clarsimp simp: unlessE_whenE liftE_bindE)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_symb_exec_r_conj)
        apply (rule_tac F="isArchCap isPageTableCap (cteCap cteVal)"
                                 in corres_gen_asm2)
        apply (rule corres_split[OF _ final_cap_corres[where ptr=slot]])
          apply (drule mp)
           apply (clarsimp simp: isCap_simps final_matters'_def)
          apply (rule whenE_throwError_corres)
            apply simp
           apply simp
          apply (rule corres_trivial, simp add: returnOk_def archinv_relation_def
                                 page_table_invocation_map_def)
         apply (wp getCTE_wp' | wp_once hoare_drop_imps)+
      apply (clarsimp)
     apply (rule no_fail_pre, rule no_fail_getCTE)
     apply (erule conjunct2)
    apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_diminished_def
                          cap_rights_update_def acap_rights_update_def)
    apply (frule diminished_is_update[rotated])
     apply (frule (2) caps_of_state_valid)
    apply (clarsimp simp add: cap_rights_update_def acap_rights_update_def)
   apply (clarsimp simp: cte_wp_at_ctes_of is_arch_diminished_def
                         cap_rights_update_def acap_rights_update_def
                         cte_wp_at_caps_of_state)
   apply (frule diminished_is_update[rotated])
    apply (frule (2) caps_of_state_valid)
   apply (clarsimp simp add: cap_rights_update_def acap_rights_update_def)
   apply (drule pspace_relation_ctes_ofI[OF _ caps_of_state_cteD, rotated],
                erule invs_pspace_aligned', clarsimp+)
   apply (simp add: isCap_simps)
  apply (simp add: isCap_simps split del: if_split)
  by (clarsimp split: invocation_label.splits arch_invocation_label.splits)

lemma decode_page_directory_inv_corres:
  "\<lbrakk>cap = arch_cap.PageDirectoryCap p opt; acap_relation cap cap';
    list_all2 cap_relation (map fst excaps) (map fst excaps');
    list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps') \<rbrakk> \<Longrightarrow>
     corres (ser \<oplus> archinv_relation)
            (invs and valid_cap (cap.ArchObjectCap cap) and
             cte_wp_at (is_arch_diminished (cap.ArchObjectCap cap)) slot and
             (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>_. True) (snd x) s))
            (invs' and valid_cap' (capability.ArchObjectCap cap') and
             (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' (fst x) s \<and> cte_wp_at' (\<lambda>_. True) (snd x) s))
            (decode_page_directory_invocation l args slot cap excaps)
            (decodeX64PageDirectoryInvocation l args (cte_map slot) cap' excaps')"
  apply (simp add: decode_page_directory_invocation_def decodeX64PageDirectoryInvocation_def Let_def
                   isCap_simps
      split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel X64PageDirectoryMap")
   apply (simp split: invocation_label.split arch_invocation_label.splits split del: if_split)
   apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
   apply (clarsimp simp: neq_Nil_conv Let_def)
   apply (rule whenE_throwError_corres_initial, simp+)
   apply (simp split: cap.split arch_cap.split option.split,
      intro conjI allI impI, simp_all)[1]
   apply (rule whenE_throwError_corres_initial, simp+)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE)
        prefer 2
        apply (rule corres_lookup_error)
        apply (rule find_vspace_for_asid_corres[OF refl])
       apply (rule whenE_throwError_corres, simp, simp)
       apply (rule corres_splitEE)
          prefer 2
          apply (rule corres_lookup_error)
          apply (rule lookup_pdpt_slot_corres)
         apply (rule corres_splitEE)
            prefer 2
            apply simp
            apply (rule get_pdpte_corres')
           apply (simp add: unlessE_whenE)
           apply (rule corres_splitEE)
              prefer 2
              apply (rule corres_whenE)
                apply clarsimp
                apply (case_tac old_pdpte; simp )[1]
               apply (rule corres_trivial)
               apply simp
              apply simp
             apply (rule corres_trivial)
             apply (rule corres_returnOk)
             apply (clarsimp simp: archinv_relation_def page_directory_invocation_map_def)
             apply (clarsimp simp: attribs_from_word_def filter_frame_attrs_def
                                   attribsFromWord_def Let_def)
            apply ((clarsimp cong: if_cong
                        | wp hoare_whenE_wp hoare_vcg_all_lift_R getPDPTE_wp get_pdpte_wp
                        | wp_once hoare_drop_imps)+)[6]
      apply (clarsimp intro!: validE_R_validE)
      apply (rule_tac Q'="\<lambda>rv s.  pspace_aligned s \<and> valid_vspace_objs s \<and> valid_arch_state s \<and>
                           equal_kernel_mappings s \<and> valid_global_objs s \<and>
                           (\<exists>ref. (ref \<rhd> rv) s) \<and> typ_at (AArch APageMapL4) rv s \<and>
                           is_aligned rv pml4_bits"
                        in hoare_post_imp_R[rotated])
       apply fastforce
      apply (wpsimp | wp_once hoare_drop_imps)+
    apply (fastforce simp: valid_cap_def mask_def)
   apply (clarsimp simp: valid_cap'_def)
   apply fastforce
    -- "PageDirectoryUnmap"
  apply (clarsimp simp: isCap_simps)+
  apply (cases "invocation_type l = ArchInvocationLabel X64PageDirectoryUnmap")
   apply (clarsimp simp: unlessE_whenE liftE_bindE)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_symb_exec_r_conj)
        apply (rule_tac F="isArchCap isPageDirectoryCap (cteCap cteVal)"
      in corres_gen_asm2)
        apply (rule corres_split[OF _ final_cap_corres[where ptr=slot]])
          apply (drule mp)
           apply (clarsimp simp: isCap_simps final_matters'_def)
          apply (rule whenE_throwError_corres)
            apply simp
           apply simp
          apply (rule corres_trivial, simp add: returnOk_def archinv_relation_def
                        page_directory_invocation_map_def)
         apply (wp getCTE_wp' | wp_once hoare_drop_imps)+
      apply (clarsimp)
     apply (rule no_fail_pre, rule no_fail_getCTE)
     apply (erule conjunct2)
    apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_diminished_def
                          cap_rights_update_def acap_rights_update_def)
    apply (frule diminished_is_update[rotated])
     apply (frule (2) caps_of_state_valid)
    apply (clarsimp simp add: cap_rights_update_def acap_rights_update_def)
   apply (clarsimp simp: cte_wp_at_ctes_of is_arch_diminished_def
                         cap_rights_update_def acap_rights_update_def
                         cte_wp_at_caps_of_state)
   apply (frule diminished_is_update[rotated])
    apply (frule (2) caps_of_state_valid)
   apply (clarsimp simp add: cap_rights_update_def acap_rights_update_def)
   apply (drule pspace_relation_ctes_ofI[OF _ caps_of_state_cteD, rotated],
      erule invs_pspace_aligned', clarsimp+)
   apply (simp add: isCap_simps)
  apply (simp add: isCap_simps split del: if_split)
  by (clarsimp split: invocation_label.splits arch_invocation_label.splits)

lemma decode_pdpt_inv_corres:
  "\<lbrakk>cap = arch_cap.PDPointerTableCap p opt; acap_relation cap cap';
    list_all2 cap_relation (map fst excaps) (map fst excaps');
    list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps') \<rbrakk> \<Longrightarrow>
     corres (ser \<oplus> archinv_relation)
            (invs and valid_cap (cap.ArchObjectCap cap) and
             cte_wp_at (is_arch_diminished (cap.ArchObjectCap cap)) slot and
             (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_wp_at (\<lambda>_. True) (snd x) s))
            (invs' and valid_cap' (capability.ArchObjectCap cap') and
             (\<lambda>s. \<forall>x\<in>set excaps'. valid_cap' (fst x) s \<and> cte_wp_at' (\<lambda>_. True) (snd x) s))
            (decode_pdpt_invocation l args slot cap excaps)
            (decodeX64PDPointerTableInvocation l args (cte_map slot) cap' excaps')"
  apply (simp add: decode_pdpt_invocation_def decodeX64PDPointerTableInvocation_def Let_def
                   isCap_simps
      split del: if_split)
  apply (cases "invocation_type l = ArchInvocationLabel X64PDPTMap")
   apply (simp split: invocation_label.split arch_invocation_label.splits split del: if_split)
   apply (simp split: list.split, intro conjI impI allI, simp_all)[1]
   apply (clarsimp simp: neq_Nil_conv Let_def)
   apply (rule whenE_throwError_corres_initial, simp+)
   apply (simp split: cap.split arch_cap.split option.split,
      intro conjI allI impI, simp_all)[1]
   apply (rule whenE_throwError_corres_initial, simp+)
   apply (rule corres_guard_imp)
     apply (rule corres_splitEE)
        prefer 2
        apply (rule corres_lookup_error)
        apply (rule find_vspace_for_asid_corres[OF refl])
       apply (rule whenE_throwError_corres, simp, simp)
         apply (rule corres_splitEE)
            prefer 2
            apply simp
            apply (rule get_pml4e_corres')
           apply (simp add: unlessE_whenE)
           apply (rule corres_splitEE)
              prefer 2
              apply (rule corres_whenE)
                apply clarsimp
                apply (case_tac old_pml4e; simp )[1]
               apply (rule corres_trivial)
               apply simp
              apply simp
             apply (rule corres_trivial)
             apply (rule corres_returnOk)
             apply (clarsimp simp: archinv_relation_def pdpt_invocation_map_def)
             apply (clarsimp simp: attribs_from_word_def filter_frame_attrs_def
                                   attribsFromWord_def Let_def)
            apply ((clarsimp cong: if_cong
                    | wp hoare_whenE_wp hoare_vcg_all_lift_R getPML4E_wp get_pml4e_wp
                    | wp_once hoare_drop_imps)+)
    apply (fastforce simp: valid_cap_def mask_def intro!: page_map_l4_pml4e_at_lookupI)
   apply (clarsimp simp: valid_cap'_def)
   apply fastforce
    -- "PDPTUnmap"
  apply (clarsimp simp: isCap_simps)+
  apply (cases "invocation_type l = ArchInvocationLabel X64PDPTUnmap")
   apply (clarsimp simp: unlessE_whenE liftE_bindE)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_symb_exec_r_conj)
        apply (rule_tac F="isArchCap isPDPointerTableCap (cteCap cteVal)"
                     in corres_gen_asm2)
        apply (rule corres_split[OF _ final_cap_corres[where ptr=slot]])
          apply (drule mp)
           apply (clarsimp simp: isCap_simps final_matters'_def)
          apply (rule whenE_throwError_corres)
            apply simp
           apply simp
          apply (rule corres_trivial, simp add: returnOk_def archinv_relation_def
                        pdpt_invocation_map_def)
         apply (wp getCTE_wp' | wp_once hoare_drop_imps)+
      apply (clarsimp)
     apply (rule no_fail_pre, rule no_fail_getCTE)
     apply (erule conjunct2)
    apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_diminished_def
                          cap_rights_update_def acap_rights_update_def)
    apply (frule diminished_is_update[rotated])
     apply (frule (2) caps_of_state_valid)
    apply (clarsimp simp add: cap_rights_update_def acap_rights_update_def)
   apply (clarsimp simp: cte_wp_at_ctes_of is_arch_diminished_def
                         cap_rights_update_def acap_rights_update_def
                         cte_wp_at_caps_of_state)
   apply (frule diminished_is_update[rotated])
    apply (frule (2) caps_of_state_valid)
   apply (clarsimp simp add: cap_rights_update_def acap_rights_update_def)
   apply (drule pspace_relation_ctes_ofI[OF _ caps_of_state_cteD, rotated],
                   erule invs_pspace_aligned', clarsimp+)
   apply (simp add: isCap_simps)
  apply (simp add: isCap_simps split del: if_split)
  by (clarsimp split: invocation_label.splits arch_invocation_label.splits)

lemma ensure_port_op_allowed_corres:
  "\<lbrakk>cap = arch_cap.IOPortCap f l; acap_relation cap cap'\<rbrakk> \<Longrightarrow>
   corres (ser \<oplus> dc) (valid_cap (cap.ArchObjectCap cap)) (valid_cap' (ArchObjectCap cap'))
     (ensure_port_operation_allowed cap w x)
     (ensurePortOperationAllowed cap' w x)"
  apply (simp add: ensure_port_operation_allowed_def ensurePortOperationAllowed_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqrE)
       apply (rule whenE_throwError_corres, simp, simp)
       apply (rule corres_whenE, simp)
        apply clarsimp
       apply clarsimp
      apply (rule corres_assertE_assume)
       apply (rule impI, assumption)+
     apply (wp)+
   apply (auto simp: valid_cap_def)[1]
  apply (auto simp: valid_cap'_def)
  done

lemma decode_port_inv_corres:
  "\<lbrakk>cap = arch_cap.IOPortCap f l; acap_relation cap cap' \<rbrakk> \<Longrightarrow>
     corres (ser \<oplus> archinv_relation)
            (invs and valid_cap (cap.ArchObjectCap cap))
            (invs' and valid_cap' (capability.ArchObjectCap cap'))
            (decode_port_invocation label args cap)
            (decodeX64PortInvocation label args cap')"
  apply (simp add: decode_port_invocation_def decodeX64PortInvocation_def)
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortIn8")
   apply (simp add: Let_def isCap_simps whenE_def)
   apply (intro conjI impI)
   apply (clarsimp simp: neq_Nil_conv)
   apply (rule corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule corres_returnOkTT)
        apply (clarsimp simp: archinv_relation_def ioport_invocation_map_def ioport_data_relation_def)
       apply (rule ensure_port_op_allowed_corres, simp, simp)
      apply wpsimp+
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortIn16")
   apply (simp add: Let_def isCap_simps whenE_def)
   apply (intro conjI impI)
   apply (clarsimp simp: neq_Nil_conv)
   apply (rule corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule corres_returnOkTT)
        apply (clarsimp simp: archinv_relation_def ioport_invocation_map_def ioport_data_relation_def)
       apply (rule ensure_port_op_allowed_corres, simp, simp)
      apply wpsimp+
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortIn32")
   apply (simp add: Let_def isCap_simps whenE_def)
   apply (intro conjI impI)
   apply (clarsimp simp: neq_Nil_conv)
   apply (rule corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule corres_returnOkTT)
        apply (clarsimp simp: archinv_relation_def ioport_invocation_map_def ioport_data_relation_def)
       apply (rule ensure_port_op_allowed_corres, simp, simp)
      apply wpsimp+
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortOut8")
   apply (simp add: Let_def isCap_simps whenE_def)
   apply (clarsimp simp: neq_Nil_conv split: list.splits)+
   apply (rule corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule corres_returnOkTT)
        apply (clarsimp simp: archinv_relation_def ioport_invocation_map_def ioport_data_relation_def)
       apply (rule ensure_port_op_allowed_corres, simp, simp)
      apply wpsimp+
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortOut16")
   apply (simp add: Let_def isCap_simps whenE_def)
   apply (clarsimp simp: neq_Nil_conv split: list.splits)+
   apply (rule corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule corres_returnOkTT)
        apply (clarsimp simp: archinv_relation_def ioport_invocation_map_def ioport_data_relation_def)
       apply (rule ensure_port_op_allowed_corres, simp, simp)
      apply wpsimp+
  apply (cases "invocation_type label = ArchInvocationLabel X64IOPortOut32")
   apply (simp add: Let_def isCap_simps whenE_def)
   apply (clarsimp simp: neq_Nil_conv split: list.splits)+
   apply (rule corres_guard_imp)
     apply (rule corres_split_norE)
        apply (rule corres_returnOkTT)
        apply (clarsimp simp: archinv_relation_def ioport_invocation_map_def ioport_data_relation_def)
       apply (rule ensure_port_op_allowed_corres, simp, simp)
      apply wpsimp+
  apply (clarsimp simp: isCap_simps Let_def split: arch_invocation_label.splits invocation_label.splits)
  done

lemma dec_arch_inv_corres:
notes check_vp_inv[wp del] check_vp_wpR[wp] [[goals_limit = 1]]
  (* FIXME: check_vp_inv shadowed check_vp_wpR.  Instead,
     check_vp_wpR should probably be generalised to replace check_vp_inv. *)
shows
  "\<lbrakk> acap_relation arch_cap arch_cap';
     list_all2 cap_relation (map fst excaps) (map fst excaps');
     list_all2 (\<lambda>s s'. s' = cte_map s) (map snd excaps) (map snd excaps') \<rbrakk> \<Longrightarrow>
   corres
   (ser \<oplus> archinv_relation)
   (invs and valid_cap (cap.ArchObjectCap arch_cap) and
        cte_wp_at (is_arch_diminished (cap.ArchObjectCap arch_cap)) slot and
     (\<lambda>s. \<forall>x\<in>set excaps. s \<turnstile> fst x \<and> cte_at (snd x) s))
   (invs' and valid_cap' (capability.ArchObjectCap arch_cap') and
     (\<lambda>s. \<forall>x\<in>set excaps'. s \<turnstile>' fst x \<and> cte_at' (snd x) s))
   (arch_decode_invocation (mi_label mi) args (to_bl cptr') slot
      arch_cap excaps)
   (Arch.decodeInvocation (mi_label mi) args cptr'
     (cte_map slot) arch_cap' excaps')"
  apply (simp add: arch_decode_invocation_def
                   X64_H.decodeInvocation_def
                   decodeX64MMUInvocation_def
              split del: if_split)
  apply (cases arch_cap)
      -- "ASIDPoolCap"
      apply (simp add: isCap_simps isIOCap_def decodeX64MMUInvocation_def
                       decodeX64ASIDPoolInvocation_def Let_def
            split del: if_split)
      apply (cases "invocation_type (mi_label mi) \<noteq> ArchInvocationLabel X64ASIDPoolAssign")
       apply (simp split: invocation_label.split arch_invocation_label.split)
      apply (rename_tac word1 word2)
      apply (cases "excaps", simp)
      apply (cases "excaps'", simp)
      apply clarsimp
      apply (case_tac a, simp_all)[1]
      apply (rename_tac arch_capa)
      apply (case_tac arch_capa, simp_all)[1]
      apply (rename_tac word3 option)
      apply (case_tac option, simp_all)[1]
      apply (rule corres_guard_imp)
        apply (rule corres_splitEE)
           prefer 2
           apply (rule corres_trivial [where r="ser \<oplus> (\<lambda>p p'. p = p' o ucast)"])
           apply (clarsimp simp: state_relation_def arch_state_relation_def)
          apply (rule whenE_throwError_corres, simp)
            apply (simp add: lookup_failure_map_def)
           apply simp
          apply (rule_tac P="\<lambda>s. asid_table (asid_high_bits_of word2) = Some word1 \<longrightarrow> asid_pool_at word1 s" and
                          P'="pspace_aligned' and pspace_distinct'" in corres_inst)
          apply (simp add: liftME_return)
          apply (rule whenE_throwError_corres_initial, simp)
           apply auto[1]
          apply (rule corres_guard_imp)
            apply (rule corres_splitEE)
               prefer 2
               apply simp
               apply (rule get_asid_pool_corres_inv'[OF refl])
              apply (simp add: bindE_assoc)
              apply (rule corres_splitEE)
                 prefer 2
                 apply (rule corres_whenE)
                   apply (subst conj_assoc [symmetric])
                   apply (subst assocs_empty_dom_comp [symmetric])
                   apply (rule dom_ucast_eq)
                  apply (rule corres_trivial)
                  apply simp
                 apply simp
                apply (rule_tac F="- dom pool \<inter> {x. x \<le> 2 ^ asid_low_bits - 1 \<and> ucast x + word2 \<noteq> 0} \<noteq> {}" in corres_gen_asm)
                apply (frule dom_hd_assocsD)
                apply (simp add: select_ext_fap[simplified free_asid_pool_select_def]
                                 free_asid_pool_select_def)
                apply (simp add: returnOk_liftE[symmetric])
                apply (rule corres_returnOk)
                apply (simp add: archinv_relation_def asid_pool_invocation_map_def)
               apply (wp hoare_whenE_wp)
               apply (clarsimp simp: ucast_fst_hd_assocs)
              apply (wp hoareE_TrueI hoare_whenE_wp getASID_wp | simp)+
           apply ((clarsimp simp: p2_low_bits_max | rule TrueI impI)+)[2]
         apply (wp hoare_whenE_wp getASID_wp)+
       apply (clarsimp simp: valid_cap_def)
      apply auto[1]
     -- "ASIDControlCap"
     apply (simp add: isCap_simps isIOCap_def decodeX64MMUInvocation_def
                      Let_def decodeX64ASIDControlInvocation_def
           split del: if_split)
     apply (cases "invocation_type (mi_label mi) \<noteq> ArchInvocationLabel X64ASIDControlMakePool")
      apply (simp split: invocation_label.split arch_invocation_label.split)
     apply (subgoal_tac "length excaps' = length excaps")
      prefer 2
      apply (simp add: list_all2_iff)
     apply (cases args, simp)
     apply (rename_tac a0 as)
     apply (case_tac as, simp)
     apply (rename_tac a1 as')
     apply (cases excaps, simp)
     apply (rename_tac excap0 exs)
     apply (case_tac exs)
      apply (auto split: list.split)[1]
     apply (rename_tac excap1 exss)
     apply (case_tac excap0)
     apply (rename_tac c0 slot0)
     apply (case_tac excap1)
     apply (rename_tac c1 slot1)
     apply (clarsimp simp: Let_def split del: if_split)
     apply (cases excaps', simp)
     apply (case_tac list, simp)
     apply (rename_tac c0' exs' c1'  exss')
     apply (clarsimp split del: if_split)
     apply (rule corres_guard_imp)
       apply (rule corres_splitEE [where r'="\<lambda>p p'. p = p' o ucast"])
          prefer 2
          apply (rule corres_trivial)
          apply (clarsimp simp: state_relation_def arch_state_relation_def)
         apply (simp only: bindE_assoc)
         apply (rule corres_splitEE)
            prefer 2
            apply (rule corres_whenE)
              apply (subst assocs_empty_dom_comp [symmetric])
              apply (simp add: o_def)
              apply (rule dom_ucast_eq_8)
             apply (rule corres_trivial, simp, simp)
           apply (simp split del: if_split)
           apply (rule_tac F="- dom (asidTable \<circ> ucast) \<inter> {x. x \<le> 2 ^ asid_high_bits - 1} \<noteq> {}" in corres_gen_asm)
           apply (drule dom_hd_assocsD)
           apply (simp add: select_ext_fa[simplified free_asid_select_def]
                      free_asid_select_def o_def returnOk_liftE[symmetric] split del: if_split)
           apply (thin_tac "fst a \<notin> b \<and> P" for a b P)
           apply (case_tac "isUntypedCap a \<and> capBlockSize a = objBits (makeObject::asidpool) \<and> \<not> capIsDevice a")
            prefer 2
            apply (rule corres_guard_imp)
              apply (rule corres_trivial)
              apply (case_tac ad, simp_all add: isCap_simps
                                     split del: if_split)[1]
              apply (case_tac x21, simp_all split del: if_split)[1]
               apply (clarsimp simp: objBits_simps archObjSize_def
                          split del: if_split)
              apply clarsimp
             apply (rule TrueI)+
           apply (clarsimp simp: isCap_simps cap_relation_Untyped_eq lookupTargetSlot_def
                                 objBits_simps archObjSize_def bindE_assoc split_def)
           apply (rule corres_splitEE)
              prefer 2
              apply (fold ser_def)
              apply (rule ensure_no_children_corres, rule refl)
             apply (rule corres_splitEE)
                prefer 2
                apply (erule lsfc_corres, rule refl)
               apply (rule corres_splitEE)
                  prefer 2
                  apply (rule ensure_empty_corres)
                  apply clarsimp
                 apply (rule corres_returnOk[where P="\<top>"])
                 apply (clarsimp simp add: archinv_relation_def asid_ci_map_def split_def)
                 apply (clarsimp simp add: ucast_assocs[unfolded o_def] split_def
                                           filter_map asid_high_bits_def)
                 apply (simp add: ord_le_eq_trans [OF word_n1_ge])
                apply wp+
          apply (simp add: o_def validE_R_def)
          apply (wp hoare_whenE_wp)+
      apply fastforce
     apply clarsimp
     apply (simp add: null_def split_def asid_high_bits_def
                      word_le_make_less)
     apply (subst hd_map, assumption)
                   (* need abstract guard to show list nonempty *)
     apply (simp add: word_le_make_less)
     apply (subst ucast_ucast_len)
      apply (drule hd_in_set)
      apply simp
     apply fastforce
    -- "IOPortCap"
    apply (simp add: isCap_simps isIOCap_def Let_def split del: if_split)
    apply (rule corres_guard_imp, rule decode_port_inv_corres; simp)

    -- "PageCap"
    apply (rename_tac word cap_rights vmpage_size option)
    apply (simp add: isCap_simps isIOCap_def decodeX64MMUInvocation_def Let_def
          split del: if_split)
        apply (rule decode_page_inv_corres; simp)

   -- "PageTableCap"
   apply (simp add: isCap_simps isIOCap_def decodeX64MMUInvocation_def Let_def
         split del: if_split)
   apply (rule decode_page_table_inv_corres; simp)

  -- "PageDirectoryCap"
  apply (simp add: isCap_simps isIOCap_def decodeX64MMUInvocation_def Let_def
        split del: if_split)
  apply (rule decode_page_directory_inv_corres; simp)

  -- "PDPointerTableCap"
  apply (simp add: isCap_simps isIOCap_def decodeX64MMUInvocation_def Let_def
        split del: if_split)
  apply (rule decode_pdpt_inv_corres; simp)

  -- "PML4Cap - no invocations"
  apply (clarsimp simp: isCap_simps isIOCap_def decodeX64MMUInvocation_def Let_def
              split del: if_split)
  done

lemma not_InvokeIOPort_rel:"\<lbrakk>archinv_relation ai ai'; \<forall>x. ai \<noteq> arch_invocation.InvokeIOPort x\<rbrakk> \<Longrightarrow>
          \<forall>y. ai' \<noteq> InvokeIOPort y"
  by (clarsimp simp: archinv_relation_def split: arch_invocation.splits)

lemma not_InvokeIOPort_perform_simp':"\<forall>y. ai' \<noteq> InvokeIOPort y \<Longrightarrow>
    (case ai' of invocation.InvokeIOPort x \<Rightarrow> performX64PortInvocation ai'
             | _ \<Rightarrow> performX64MMUInvocation ai') = performX64MMUInvocation ai'"
  by (case_tac ai'; clarsimp)

lemmas not_InvokeIOPort_perform_simp[simp] = not_InvokeIOPort_perform_simp'[OF not_InvokeIOPort_rel]

thm corres_machine_op[no_vars]

lemma corresK_machine_op[corresK]: "corres_underlyingK Id False True F r P Q x x' \<Longrightarrow>
   corres_underlyingK state_relation False True F r
    (P \<circ> machine_state) (Q \<circ> ksMachineState)
       (do_machine_op x) (doMachineOp x')"
  apply (clarsimp simp add: corres_underlyingK_def)
  by (erule corres_machine_op)

lemma port_in_corres[corres]:
  "no_fail \<top> a \<Longrightarrow> corres dc (einvs and ct_active) (invs' and ct_active') (port_in a) (portIn a)"
  apply (clarsimp simp: port_in_def portIn_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF _ gct_corres])
      apply (rule corres_split_eqr)
         apply (rule corres_split_eqr[OF set_mi_corres set_mrs_corres])
            apply wpsimp+
        apply (rule corres_machine_op[OF corres_Id], simp+)
       apply wpsimp+
  done

lemma port_out_corres[@lift_corres_args, corres]:
  "no_fail \<top> (a w) \<Longrightarrow> corres dc (einvs and ct_active) (invs' and ct_active')
                       (port_out a w) (portOut a w)"
  apply (clarsimp simp: port_out_def portOut_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_eqr[OF _ gct_corres])
      apply (rule corres_split_eqr[OF set_mi_corres])
         apply wpsimp+
        apply (rule corres_machine_op[OF corres_Id], simp+)
       apply wpsimp+
  done

(* FIXME x64: move *)
lemma no_fail_in8[wp]:
  "no_fail \<top> (in8 a)"
  by (wpsimp simp: in8_def wp: no_fail_machine_op_lift)

lemma no_fail_in16[wp]:
  "no_fail \<top> (in16 a)"
  by (wpsimp simp: in16_def wp: no_fail_machine_op_lift)

lemma no_fail_in32[wp]:
  "no_fail \<top> (in32 a)"
  by (wpsimp simp: in32_def wp: no_fail_machine_op_lift)

lemma no_fail_out8[wp]:
  "no_fail \<top> (out8 a w)"
  by (wpsimp simp: out8_def)

lemma no_fail_out16[wp]:
  "no_fail \<top> (out16 a w)"
  by (wpsimp simp: out16_def)

lemma no_fail_out32[wp]:
  "no_fail \<top> (out32 a w)"
  by (wpsimp simp: out32_def)

lemma perform_port_inv_corres:
  "\<lbrakk>archinv_relation ai ai'; ai = arch_invocation.InvokeIOPort x\<rbrakk>
  \<Longrightarrow> corres (intr \<oplus> (op =))
        (einvs and ct_active and valid_arch_inv ai)
        (invs' and ct_active' and valid_arch_inv' ai')
        (liftE (do perform_io_port_invocation x; return [] od))
        (performX64PortInvocation ai')"
  apply (clarsimp simp: perform_io_port_invocation_def performX64PortInvocation_def
                        archinv_relation_def ioport_invocation_map_def)
  apply (case_tac x; clarsimp)
  apply (corressimp corres: port_in_corres port_out_corres simp: ioport_data_relation_def)
  by (auto simp: no_fail_in8 no_fail_in16 no_fail_in32
                    no_fail_out8 no_fail_out16 no_fail_out32)


lemma inv_arch_corres:
  "archinv_relation ai ai' \<Longrightarrow>
   corres (intr \<oplus> op=)
     (einvs and ct_active and valid_arch_inv ai)
     (invs' and ct_active' and valid_arch_inv' ai')
     (arch_perform_invocation ai) (Arch.performInvocation ai')"
  apply (clarsimp simp: arch_perform_invocation_def
                        X64_H.performInvocation_def
                        performX64MMUInvocation_def)
  apply (cases "\<exists>x. ai = arch_invocation.InvokeIOPort x")
   apply (clarsimp simp: archinv_relation_def)
   apply (rule corres_guard_imp[OF perform_port_inv_corres[where ai=ai, simplified]];
                clarsimp simp: archinv_relation_def)
  apply (clarsimp simp: archinv_relation_def)
  apply (clarsimp simp: performX64MMUInvocation_def)
  apply (rule corres_split' [where r'=dc])
     prefer 2
     apply (rule corres_trivial)
     apply simp
    apply (cases ai)
          apply (clarsimp simp: archinv_relation_def)
          apply (erule corres_guard_imp [OF perform_page_table_corres])
           apply (fastforce simp: valid_arch_inv_def)
          apply (fastforce simp: valid_arch_inv'_def)
         apply (clarsimp simp: archinv_relation_def)
         apply (erule corres_guard_imp [OF perform_page_directory_corres])
          apply (fastforce simp: valid_arch_inv_def)
         apply (fastforce simp: valid_arch_inv'_def)
        apply (clarsimp simp: archinv_relation_def)
        apply (erule corres_guard_imp [OF perform_pdpt_corres])
         apply (fastforce simp: valid_arch_inv_def)
        apply (fastforce simp: valid_arch_inv'_def)
       apply (clarsimp simp: archinv_relation_def)
       apply (erule corres_guard_imp [OF perform_page_corres])
        apply (fastforce simp: valid_arch_inv_def)
       apply (fastforce simp: valid_arch_inv'_def)
      apply (clarsimp simp: archinv_relation_def)
      apply (rule corres_guard_imp [OF pac_corres], rule refl)
       apply (fastforce simp: valid_arch_inv_def)
      apply (fastforce simp: valid_arch_inv'_def)
     apply (clarsimp simp: archinv_relation_def)
     apply (rule corres_guard_imp [OF pap_corres], rule refl)
      apply (fastforce simp: valid_arch_inv_def)
     apply (fastforce simp: valid_arch_inv'_def)
    apply clarsimp
   apply wp+
  done

lemma asid_pool_typ_at_ext':
  "asid_pool_at' = obj_at' (\<top>::asidpool \<Rightarrow> bool)"
  apply (rule ext)+
  apply (simp add: typ_at_to_obj_at_arches)
  done

lemma st_tcb_strg':
  "st_tcb_at' P p s \<longrightarrow> tcb_at' p s"
  by (auto simp: pred_tcb_at')

lemma performASIDControlInvocation_tcb_at':
  "\<lbrace>st_tcb_at' active' p and invs' and ct_active' and valid_aci' aci\<rbrace>
  performASIDControlInvocation aci
  \<lbrace>\<lambda>y. tcb_at' p\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: performASIDControlInvocation_def split: asidcontrol_invocation.splits)
  apply (clarsimp simp: valid_aci'_def cte_wp_at_ctes_of cong: conj_cong)
  apply (wp static_imp_wp  |simp add:placeNewObject_def2)+
      apply (wp createObjects_orig_obj_at2' updateFreeIndex_pspace_no_overlap' getSlotCap_wp static_imp_wp)+
   apply (clarsimp simp: projectKO_opts_defs)
   apply (strengthen st_tcb_strg' [where P=\<top>])
   apply (wp deleteObjects_invs_derivatives[where p="makePoolParent aci"]
     hoare_vcg_ex_lift deleteObjects_cte_wp_at'[where d=False]
     deleteObjects_st_tcb_at'[where p="makePoolParent aci"] static_imp_wp
     updateFreeIndex_pspace_no_overlap' deleteObject_no_overlap[where d=False])+
  apply (case_tac ctea)
  apply (clarsimp)
  apply (frule ctes_of_valid_cap')
   apply (simp add:invs_valid_objs')+
  apply (clarsimp simp:valid_cap'_def capAligned_def cte_wp_at_ctes_of)
  apply (strengthen refl order_refl
                    pred_tcb'_weakenE[mk_strg I E])
  apply (clarsimp simp: conj_comms invs_valid_pspace' isCap_simps
                        descendants_range'_def2 empty_descendants_range_in')
  apply (frule ctes_of_valid', clarsimp, simp,
    drule capFreeIndex_update_valid_cap'[where fb="2 ^ pageBits", rotated -1],
    simp_all)
   apply (simp add: pageBits_def is_aligned_def untypedBits_defs)
  apply (simp add: valid_cap_simps' range_cover_def objBits_simps archObjSize_def untypedBits_defs
                   capAligned_def unat_eq_0 and_mask_eq_iff_shiftr_0[symmetric]
                   word_bw_assocs)
  apply clarsimp
  apply (drule(1) cte_cap_in_untyped_range,
         fastforce simp add: cte_wp_at_ctes_of, assumption, simp_all)
   apply (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
  apply clarsimp
  done

crunch tcb_at'[wp]: performX64PortInvocation "tcb_at' t"

lemma invokeArch_tcb_at':
  "\<lbrace>invs' and valid_arch_inv' ai and ct_active' and st_tcb_at' active' p\<rbrace>
     Arch.performInvocation ai
   \<lbrace>\<lambda>rv. tcb_at' p\<rbrace>"
  apply (simp add: X64_H.performInvocation_def performX64MMUInvocation_def)
  apply (wpsimp simp: performX64MMUInvocation_def pred_tcb_at' valid_arch_inv'_def
                  wp: performASIDControlInvocation_tcb_at')
  done

(* FIXME random place to have these *)
lemma pspace_no_overlap_queuesL1 [simp]:
  "pspace_no_overlap' w sz (ksReadyQueuesL1Bitmap_update f s) = pspace_no_overlap' w sz s"
  by (simp add: pspace_no_overlap'_def)

(* FIXME random place to have these *)
lemma pspace_no_overlap_queuesL2 [simp]:
  "pspace_no_overlap' w sz (ksReadyQueuesL2Bitmap_update f s) = pspace_no_overlap' w sz s"
  by (simp add: pspace_no_overlap'_def)

crunch pspace_no_overlap'[wp]: setThreadState "pspace_no_overlap' w s"
  (simp: unless_def)

lemma sts_cte_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_to' p\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. ex_cte_cap_to' p\<rbrace>"
  by (wp ex_cte_cap_to'_pres)


lemma ko_wp_at'_cong:
 "ksPSpace s = ksPSpace m \<Longrightarrow> ko_wp_at' P p s = ko_wp_at' P p m"
  by (simp add:ko_wp_at'_def ps_clear_def)

lemma valid_slots_lift':
  assumes t: "\<And>T p. \<lbrace>typ_at' T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at' T p\<rbrace>"
  shows "\<lbrace>valid_slots' x\<rbrace> f \<lbrace>\<lambda>rv. valid_slots' x\<rbrace>"
  apply (clarsimp simp: valid_slots'_def)
  apply (case_tac x, clarsimp split: vmpage_entry.splits)
  apply safe
   apply (rule hoare_pre, wp hoare_vcg_const_Ball_lift t valid_pde_lift' valid_pte_lift' valid_pdpte_lift', simp)+
  done

lemma sts_valid_arch_inv':
  "\<lbrace>valid_arch_inv' ai\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_arch_inv' ai\<rbrace>"
  apply (cases ai, simp_all add: valid_arch_inv'_def)
        apply (clarsimp simp: valid_pdpti'_def split: pdptinvocation.splits)
        apply (intro allI conjI impI)
         apply wpsimp+
       apply (clarsimp simp: valid_pdi'_def split: page_directory_invocation.splits)
       apply (intro allI conjI impI)
        apply wpsimp+
      apply (clarsimp simp: valid_pti'_def split: page_table_invocation.splits)
      apply (intro allI conjI impI)
       apply (wp | simp)+
     apply (rename_tac page_invocation)
     apply (case_tac page_invocation, simp_all add: valid_page_inv'_def)[1]
        apply (wp valid_slots_lift' |simp)+
    apply (clarsimp simp: valid_aci'_def split: asidcontrol_invocation.splits)
    apply (clarsimp simp: cte_wp_at_ctes_of)
    apply (rule hoare_pre, wp)
    apply clarsimp
   apply (clarsimp simp: valid_apinv'_def split: asidpool_invocation.splits)
   apply (rule hoare_pre, wp)
   apply simp
  apply wp
  done

lemma inv_ASIDPool: "inv ASIDPool = (\<lambda>v. case v of ASIDPool a \<Rightarrow> a)"
  apply (rule ext)
  apply (case_tac v)
  apply simp
  apply (rule inv_f_f, rule inj_onI)
  apply simp
  done

lemma findVSpaceForASID_aligned[wp]:
  "\<lbrace>valid_objs'\<rbrace> findVSpaceForASID p \<lbrace>\<lambda>rv s. is_aligned rv pml4Bits\<rbrace>,-"
  apply (simp add: findVSpaceForASID_def assertE_def cong: option.case_cong
                      split del: if_split)
  apply (rule hoare_pre)
   apply (wp getASID_wp | wpc)+
  apply clarsimp
  apply (drule(1) obj_at_valid_objs')
  apply (clarsimp simp: projectKOs valid_obj'_def inv_ASIDPool ranI
                 split: asidpool.split_asm)
  done

lemma diminished_arch_update':
  "diminished' (ArchObjectCap cp) (cteCap cte) \<Longrightarrow> is_arch_update' (ArchObjectCap cp) cte"
  by (clarsimp simp: is_arch_update'_def isCap_simps
                     diminished'_def)

lemma lookup_pdpt_slot_no_fail_corres[simp]:
  "lookupPDPTSlotFromPDPT pt vptr
    = (do stateAssert (pd_pointer_table_at' pt) []; return (lookup_pdpt_slot_no_fail pt vptr) od)"
  by (simp add: lookup_pdpt_slot_no_fail_def lookupPDPTSlotFromPDPT_def
                mask_def checkPDPTAt_def word_size_bits_def)

lemma lookup_pd_slot_no_fail_corres[simp]:
  "lookupPDSlotFromPD pt vptr
    = (do stateAssert (page_directory_at' pt) []; return (lookup_pd_slot_no_fail pt vptr) od)"
  by (simp add: lookup_pd_slot_no_fail_def lookupPDSlotFromPD_def
                mask_def checkPDAt_def word_size_bits_def)

lemma lookup_pt_slot_no_fail_corres[simp]:
  "lookupPTSlotFromPT pt vptr
    = (do stateAssert (page_table_at' pt) []; return (lookup_pt_slot_no_fail pt vptr) od)"
  by (simp add: lookup_pt_slot_no_fail_def lookupPTSlotFromPT_def
                mask_def checkPTAt_def word_size_bits_def)

lemma lookupPDPTSlot_pd_pointer_table_at':
  "\<lbrace>valid_objs'\<rbrace> lookupPDPTSlot pm vptr
  \<lbrace>\<lambda>rv s. pd_pointer_table_at' (rv && ~~ mask pdptBits) s\<rbrace>,-"
  apply (simp add: lookupPDPTSlot_def)
  apply (wp getPML4E_wp|wpc|simp add:checkPDPTAt_def)+
  apply (clarsimp simp:ptBits_def lookup_pdpt_slot_no_fail_def lookup_pml4_slot_def)
  apply (subst pdpt_shifting(2)[simplified])
   apply (simp add: pd_pointer_table_at'_def bit_simps)
  apply simp
  done

lemma lookupPDSlot_page_directory_at':
  "\<lbrace>valid_objs'\<rbrace> lookupPDSlot pm vptr
  \<lbrace>\<lambda>rv s. page_directory_at' (rv && ~~ mask pdBits) s\<rbrace>,-"
  apply (simp add: lookupPDSlot_def)
  apply (wp getPDPTE_wp hoare_vcg_all_lift_R hoare_vcg_const_imp_lift_R
           | wpc
           | simp add:checkPDAt_def
           | wp_once hoare_drop_imps)+
  apply (clarsimp simp:pdBits_def lookup_pd_slot_no_fail_def)
  apply (subst pd_shifting(2)[simplified])
   apply (simp add: page_directory_at'_def bit_simps)
  apply simp
  done

lemma lookupPTSlot_page_table_at':
  "\<lbrace>valid_objs'\<rbrace> lookupPTSlot pm vptr
  \<lbrace>\<lambda>rv s. page_table_at' (rv && ~~ mask ptBits) s\<rbrace>,-"
    apply (simp add: lookupPTSlot_def)
  apply (wp getPDE_wp hoare_vcg_all_lift_R hoare_vcg_const_imp_lift_R
           | wpc
           | simp add:checkPTAt_def
           | wp_once hoare_drop_imps)+
  apply (clarsimp simp:ptBits_def lookup_pt_slot_no_fail_def)
  apply (subst pt_shifting(2)[simplified])
   apply (simp add: page_table_at'_def bit_simps)
  apply simp
  done

lemma findVSpaceForASID_page_map_l4_at':
  shows "\<lbrace>\<top>\<rbrace> findVSpaceForASID asid
    \<lbrace>\<lambda>rv s. page_map_l4_at' (lookup_pml4_slot rv vptr && ~~ mask pml4Bits) s\<rbrace>,-"
  apply (simp add:findVSpaceForASID_def)
   apply (wp getASID_wp|simp add:checkPML4At_def | wpc)+
  apply (clarsimp simp: lookup_pml4_slot_def pml4Bits_def)
  apply (subst pml4_shifting'[simplified])
   apply (simp add: page_map_l4_at'_def bit_simps)
  apply simp
  done

lemma decode_page_inv_wf[wp]:
  "cap = (arch_capability.PageCap word vmrights mt vmpage_size d option) \<Longrightarrow>
      \<lbrace>invs' and valid_cap' (capability.ArchObjectCap cap ) and
        cte_wp_at' (diminished' (capability.ArchObjectCap cap) \<circ> cteCap) slot and
        (\<lambda>s. \<forall>x\<in>set excaps. cte_wp_at' (diminished' (fst x) \<circ> cteCap) (snd x) s) and
        sch_act_simple\<rbrace>
       decodeX64FrameInvocation label args slot cap excaps
       \<lbrace>valid_arch_inv'\<rbrace>, -"
  apply (simp add: decodeX64FrameInvocation_def Let_def isCap_simps
             cong: if_cong split del: if_split)
  apply (cases "invocation_type label = ArchInvocationLabel X64PageMap")
   apply (simp add: split_def split del: if_split
              cong: list.case_cong prod.case_cong)
   apply (rule hoare_pre)
    apply (wp createMappingEntries_wf checkVP_wpR whenE_throwError_wp hoare_vcg_const_imp_lift_R
           |wpc|simp add:valid_arch_inv'_def valid_page_inv'_def | wp_once hoare_drop_imps)+
   apply (clarsimp simp: neq_Nil_conv invs_valid_objs' linorder_not_le
                           cte_wp_at_ctes_of)
   apply (drule ctes_of_valid', fastforce)+
   apply (clarsimp simp: diminished_valid' [symmetric])
   apply (clarsimp simp: valid_cap'_def ptBits_def pageBits_def)
   apply (clarsimp simp: is_arch_update'_def isCap_simps capAligned_def
                           vmsz_aligned'_def
                    dest!: diminished_capMaster)
   apply (rule conjI)
    apply (erule is_aligned_addrFromPPtr_n, case_tac vmpage_size, simp_all add: bit_simps)[1]
   apply (simp add: user_vtop_def X64.pptrBase_def)
   apply (word_bitwise)
  apply (cases "invocation_type label = ArchInvocationLabel X64PageRemap")
   apply (simp add: split_def invs_valid_objs' split del: if_split
              cong: list.case_cong prod.case_cong)
   apply (rule hoare_pre)
    apply (wp createMappingEntries_wf checkVP_wpR whenE_throwError_wp hoare_vcg_const_imp_lift_R
               |wpc|simp add:valid_arch_inv'_def valid_page_inv'_def
               | wp_once hoare_drop_imps)+
   apply (clarsimp simp: invs_valid_objs' linorder_not_le
                           cte_wp_at_ctes_of)
   apply (drule ctes_of_valid', fastforce)+
   apply (clarsimp simp: diminished_valid' [symmetric])
   apply (clarsimp simp: valid_cap'_def ptBits_def pageBits_def)
   apply (clarsimp simp: is_arch_update'_def isCap_simps capAligned_def
                           vmsz_aligned'_def pdBits_def pageBits_def vmsz_aligned_def
                    dest!: diminished_capMaster)
   apply (erule is_aligned_addrFromPPtr_n, case_tac vmpage_size, simp_all add: bit_simps)[1]
  apply (cases "invocation_type label = ArchInvocationLabel X64PageUnmap")
   apply (simp split del: if_split)
   apply (rule hoare_pre, wp)
   apply (clarsimp simp: valid_arch_inv'_def valid_page_inv'_def)
   apply (thin_tac "Ball S P" for S P)
   apply (erule cte_wp_at_weakenE')
   apply (clarsimp simp: is_arch_update'_def isCap_simps dest!: diminished_capMaster)
  apply (cases "invocation_type label = ArchInvocationLabel X64PageGetAddress")
   apply (simp split del: if_split)
   apply (rule hoare_pre, wp)
   apply (clarsimp simp: valid_arch_inv'_def valid_page_inv'_def)
  by (simp add:throwError_R'
              split: invocation_label.splits arch_invocation_label.splits)

lemma decode_page_table_inv_wf[wp]:
  "arch_cap = PageTableCap word option \<Longrightarrow>
       \<lbrace>invs' and valid_cap' (capability.ArchObjectCap arch_cap) and
        cte_wp_at' (diminished' (capability.ArchObjectCap arch_cap) \<circ> cteCap) slot and
        (\<lambda>s. \<forall>x\<in>set excaps. cte_wp_at' (diminished' (fst x) \<circ> cteCap) (snd x) s) and
        sch_act_simple\<rbrace>
       decodeX64PageTableInvocation label args slot arch_cap excaps
       \<lbrace>valid_arch_inv'\<rbrace>, - "
  apply (simp add: decodeX64PageTableInvocation_def Let_def isCap_simps split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply ((wp whenE_throwError_wp isFinalCapability_inv getPDE_wp
        | wpc
        | simp add: valid_arch_inv'_def valid_pti'_def unlessE_whenE
        | wp_once hoare_drop_imps)+)
  apply (clarsimp simp: linorder_not_le isCap_simps
                        cte_wp_at_ctes_of diminished_arch_update')
  apply (simp add: valid_cap'_def capAligned_def)
  apply (rule conjI)
   apply (clarsimp simp: is_arch_update'_def isCap_simps
                  dest!: diminished_capMaster)
  apply (clarsimp simp: neq_Nil_conv invs_valid_objs'
                        ptBits_def pageBits_def is_aligned_addrFromPPtr_n)
  apply (thin_tac "Ball S P" for S P)+
  apply (drule ctes_of_valid', fastforce)+
  apply (clarsimp simp: diminished_valid' [symmetric])
  apply (clarsimp simp: valid_cap'_def bit_simps is_aligned_addrFromPPtr_n
                        invs_valid_objs' and_not_mask[symmetric])
  apply (clarsimp simp: mask_def X64.pptrBase_def user_vtop_def)
  apply word_bitwise
  apply auto
  done

lemma decode_page_directory_inv_wf[wp]:
  "arch_cap = PageDirectoryCap word option \<Longrightarrow>
       \<lbrace>invs' and valid_cap' (capability.ArchObjectCap arch_cap) and
        cte_wp_at' (diminished' (capability.ArchObjectCap arch_cap) \<circ> cteCap) slot and
        (\<lambda>s. \<forall>x\<in>set excaps. cte_wp_at' (diminished' (fst x) \<circ> cteCap) (snd x) s) and
        sch_act_simple\<rbrace>
       decodeX64PageDirectoryInvocation label args slot arch_cap excaps
       \<lbrace>valid_arch_inv'\<rbrace>, - "
  apply (simp add: decodeX64PageDirectoryInvocation_def Let_def isCap_simps split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply ((wp whenE_throwError_wp isFinalCapability_inv getPDPTE_wp
        | wpc
        | simp add: valid_arch_inv'_def valid_pdi'_def unlessE_whenE
        | wp_once hoare_drop_imps)+)
  apply (clarsimp simp: linorder_not_le isCap_simps
                        cte_wp_at_ctes_of diminished_arch_update')
  apply (simp add: valid_cap'_def capAligned_def)
  apply (rule conjI)
   apply (clarsimp simp: is_arch_update'_def isCap_simps
                  dest!: diminished_capMaster)
  apply (clarsimp simp: neq_Nil_conv invs_valid_objs'
                        pdBits_def pageBits_def is_aligned_addrFromPPtr_n)
  apply (thin_tac "Ball S P" for S P)+
  apply (drule ctes_of_valid', fastforce)+
  apply (clarsimp simp: diminished_valid' [symmetric])
  apply (clarsimp simp: valid_cap'_def bit_simps is_aligned_addrFromPPtr_n
                        invs_valid_objs' and_not_mask[symmetric])
  apply (clarsimp simp: mask_def X64.pptrBase_def user_vtop_def)
  apply word_bitwise
  apply auto
  done

lemma decode_pdpt_inv_wf[wp]:
  "arch_cap = PDPointerTableCap word option \<Longrightarrow>
       \<lbrace>invs' and valid_cap' (capability.ArchObjectCap arch_cap) and
        cte_wp_at' (diminished' (capability.ArchObjectCap arch_cap) \<circ> cteCap) slot and
        (\<lambda>s. \<forall>x\<in>set excaps. cte_wp_at' (diminished' (fst x) \<circ> cteCap) (snd x) s) and
        sch_act_simple\<rbrace>
       decodeX64PDPointerTableInvocation label args slot arch_cap excaps
       \<lbrace>valid_arch_inv'\<rbrace>, - "
  apply (simp add: decodeX64PDPointerTableInvocation_def Let_def isCap_simps split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply ((wp whenE_throwError_wp isFinalCapability_inv getPML4E_wp
        | wpc
        | simp add: valid_arch_inv'_def valid_pdpti'_def unlessE_whenE
        | wp_once hoare_drop_imps)+)
  apply (clarsimp simp: linorder_not_le isCap_simps
                        cte_wp_at_ctes_of diminished_arch_update')
  apply (simp add: valid_cap'_def capAligned_def)
  apply (rule conjI)
   apply (clarsimp simp: is_arch_update'_def isCap_simps
                  dest!: diminished_capMaster)
  apply (clarsimp simp: neq_Nil_conv invs_valid_objs'
                        pdBits_def pageBits_def is_aligned_addrFromPPtr_n)
  apply (thin_tac "Ball S P" for S P)+
  apply (drule ctes_of_valid', fastforce)+
  apply (clarsimp simp: diminished_valid' [symmetric])
  apply (clarsimp simp: valid_cap'_def bit_simps is_aligned_addrFromPPtr_n
                        invs_valid_objs' and_not_mask[symmetric])
  apply (clarsimp simp: mask_def X64.pptrBase_def user_vtop_def)
  apply word_bitwise
  apply auto
  done

lemma decode_port_inv_wf[wp]:
  "arch_cap = IOPortCap f l \<Longrightarrow>
       \<lbrace>\<top>\<rbrace>
       decodeX64PortInvocation label args arch_cap
       \<lbrace>valid_arch_inv'\<rbrace>, - "
  apply (clarsimp simp: decodeX64PortInvocation_def Let_def isCap_simps split del: if_split cong: if_cong)
  by (wpsimp simp: valid_arch_inv'_def)

lemma arch_decodeInvocation_wf[wp]:
  notes ensureSafeMapping_inv[wp del]
  shows "\<lbrace>invs' and valid_cap' (ArchObjectCap arch_cap) and
    cte_wp_at' (diminished' (ArchObjectCap arch_cap) o cteCap) slot and
    (\<lambda>s. \<forall>x \<in> set excaps. cte_wp_at' (diminished' (fst x) o cteCap) (snd x) s) and
    sch_act_simple\<rbrace>
   Arch.decodeInvocation label args cap_index slot arch_cap excaps
   \<lbrace>valid_arch_inv'\<rbrace>,-"
  apply (cases arch_cap)
      -- "ASIDPool cap"
      apply (simp add: decodeX64MMUInvocation_def X64_H.decodeInvocation_def
                       Let_def split_def isCap_simps isIOCap_def decodeX64ASIDPoolInvocation_def
                  cong: if_cong split del: if_split)
      apply (rule hoare_pre)
       apply ((wp whenE_throwError_wp getASID_wp|
               wpc|
               simp add: valid_arch_inv'_def valid_apinv'_def)+)[1]
      apply (clarsimp simp: word_neq_0_conv valid_cap'_def)
      apply (rule conjI)
       apply (erule cte_wp_at_weakenE')
       apply (clarsimp simp: diminished_isPML4Cap')
      apply (subst (asm) conj_assoc [symmetric])
      apply (subst (asm) assocs_empty_dom_comp [symmetric])
      apply (drule dom_hd_assocsD)
      apply (simp add: capAligned_def)
      apply (elim conjE)
      apply (subst field_simps, erule is_aligned_add_less_t2n)
        apply assumption
       apply (simp add: asid_low_bits_def asid_bits_def)
      apply assumption
     -- "ASIDControlCap"
     apply (simp add: decodeX64MMUInvocation_def X64_H.decodeInvocation_def
                       Let_def split_def isCap_simps isIOCap_def decodeX64ASIDControlInvocation_def
                  cong: if_cong invocation_label.case_cong arch_invocation_label.case_cong list.case_cong prod.case_cong
                  split del: if_split)
     apply (rule hoare_pre)
      apply ((wp whenE_throwError_wp ensureEmptySlot_stronger|
              wpc|
              simp add: valid_arch_inv'_def valid_aci'_def is_aligned_shiftl_self
                           split del: if_split)+)[1]
          apply (rule_tac Q'=
                      "\<lambda>rv. K (fst (hd [p\<leftarrow>assocs asidTable . fst p \<le> 2 ^ asid_high_bits - 1 \<and> snd p = None])
                               << asid_low_bits \<le> 2 ^ asid_bits - 1) and
                            real_cte_at' rv and
                            ex_cte_cap_to' rv and
                            cte_wp_at' (\<lambda>cte. \<exists>idx. cteCap cte = (UntypedCap False frame pageBits idx)) (snd (excaps!0)) and
                            sch_act_simple and
                            (\<lambda>s. descendants_of' (snd (excaps!0)) (ctes_of s) = {}) "
                            in hoare_post_imp_R)
           apply (simp add: lookupTargetSlot_def)
           apply wp
          apply (clarsimp simp: cte_wp_at_ctes_of)
         apply (simp split del: if_split)
         apply (wp ensureNoChildren_sp whenE_throwError_wp|wpc)+
     apply clarsimp
     apply (rule conjI)
      apply (clarsimp simp: null_def neq_Nil_conv)
      apply (drule filter_eq_ConsD)
      apply clarsimp
      apply (rule shiftl_less_t2n)
       apply (simp add: asid_bits_def asid_low_bits_def asid_high_bits_def)
       apply unat_arith
      apply (simp add: asid_bits_def)
     apply clarsimp
     apply (rule conjI, fastforce)
     apply (clarsimp simp: cte_wp_at_ctes_of objBits_simps archObjSize_def)
     apply (rule conjI)
      apply (case_tac cteb)
      apply clarsimp
      apply (drule ctes_of_valid_cap', fastforce)
      apply (simp add: diminished_valid')
     apply clarsimp
     apply (simp add: ex_cte_cap_to'_def cte_wp_at_ctes_of)
     apply (rule_tac x=ba in exI)
     apply (simp add: diminished_cte_refs')
    -- "IOPortCap"
    apply (simp add: decodeX64MMUInvocation_def X64_H.decodeInvocation_def
                       Let_def split_def isCap_simps isIOCap_def valid_arch_inv'_def
                cong: if_cong split del: if_split)
    apply (wp, simp+)

    -- "PageCap"
        apply (simp add: decodeX64MMUInvocation_def isCap_simps X64_H.decodeInvocation_def Let_def isIOCap_def
                   cong: if_cong split del: if_split)
        apply (wp, simp+)

    -- "PageTableCap"
    apply (simp add: decodeX64MMUInvocation_def isCap_simps X64_H.decodeInvocation_def isIOCap_def Let_def
               cong: if_cong split del: if_split)
    apply (wpsimp, simp+)

    -- "PageDirectoryCap"
    apply (simp add: decodeX64MMUInvocation_def isCap_simps X64_H.decodeInvocation_def isIOCap_def Let_def
               cong: if_cong split del: if_split)
    apply (wpsimp, simp+)

    -- "PDPointerTableCap"
    apply (simp add: decodeX64MMUInvocation_def isCap_simps X64_H.decodeInvocation_def isIOCap_def Let_def
               cong: if_cong split del: if_split)
    apply (wpsimp, simp+)

      -- "PML4Cap"
  apply (simp add: decodeX64MMUInvocation_def isCap_simps X64_H.decodeInvocation_def isIOCap_def Let_def
               cong: if_cong split del: if_split)
  by (wpsimp)

lemma setObject_cte_nosch [wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject p (cte::cte) \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  apply (rule setObject_nosch)
  apply (simp add: updateObject_cte)
  apply (rule hoare_pre)
   apply (wp|wpc|simp add: unless_def)+
  done

lemma setObject_pte_nosch [wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject p (pte::pte) \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  apply (rule setObject_nosch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

lemma setObject_pde_nosch [wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace> setObject p (pde::pde) \<lbrace>\<lambda>_ s. P (ksSchedulerAction s)\<rbrace>"
  apply (rule setObject_nosch)
  apply (simp add: updateObject_default_def)
  apply wp
  apply simp
  done

crunch nosch[wp]: setMRs "\<lambda>s. P (ksSchedulerAction s)"
    (ignore: getRestartPC setRegister transferCapsToSlots
   wp: hoare_drop_imps hoare_vcg_split_case_option
        mapM_wp'
   simp: split_def zipWithM_x_mapM)

crunch nosch [wp]: performX64MMUInvocation, performX64PortInvocation "\<lambda>s. P (ksSchedulerAction s)"
  (ignore: getObject setObject
   wp: crunch_wps getObject_cte_inv getASID_wp)

lemma arch_pinv_nosch[wp]:
  "\<lbrace>\<lambda>s. P (ksSchedulerAction s)\<rbrace>
     Arch.performInvocation invok
   \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
  by (simp add: X64_H.performInvocation_def | wpc | wp)+

lemmas setObject_cte_st_tcb_at' [wp] = setCTE_pred_tcb_at' [unfolded setCTE_def]

crunch st_tcb_at': performPageDirectoryInvocation, performPageTableInvocation,
                   performPageInvocation, performPDPTInvocation,
                   performASIDPoolInvocation, performX64PortInvocation "st_tcb_at' P t"
  (ignore: getObject setObject
   wp: crunch_wps getASID_wp getObject_cte_inv simp: crunch_simps)

lemma performASIDControlInvocation_st_tcb_at':
  "\<lbrace>st_tcb_at' (P and op \<noteq> Inactive and op \<noteq> IdleThreadState) t and
    valid_aci' aci and invs' and ct_active'\<rbrace>
    performASIDControlInvocation aci
  \<lbrace>\<lambda>y. st_tcb_at' P t\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: performASIDControlInvocation_def split: asidcontrol_invocation.splits)
  apply (clarsimp simp: valid_aci'_def cte_wp_at_ctes_of cong: conj_cong)
  apply (rule hoare_pre)
   apply (wp createObjects_orig_obj_at'[where P="P \<circ> tcbState", folded st_tcb_at'_def]
             updateFreeIndex_pspace_no_overlap' getSlotCap_wp
             hoare_vcg_ex_lift
             deleteObjects_cte_wp_at' deleteObjects_invs_derivatives
             deleteObjects_st_tcb_at'
             static_imp_wp
        | simp add: placeNewObject_def2)+
  apply (case_tac ctea)
  apply (clarsimp)
  apply (frule ctes_of_valid_cap')
   apply (simp add:invs_valid_objs')+
  apply (clarsimp simp:valid_cap'_def capAligned_def cte_wp_at_ctes_of)
  apply (rule conjI)
    apply clarsimp
    apply (drule (1) cte_cap_in_untyped_range)
        apply (fastforce simp add: cte_wp_at_ctes_of)
       apply assumption+
      subgoal by (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
     subgoal by fastforce
    apply simp
   apply (rule conjI,assumption)
  apply (clarsimp simp:invs_valid_pspace' objBits_simps archObjSize_def
    range_cover_full descendants_range'_def2 isCap_simps)
  apply (intro conjI)
               apply (fastforce simp:empty_descendants_range_in')+
       apply clarsimp
       apply (drule (1) cte_cap_in_untyped_range)
           apply (fastforce simp add: cte_wp_at_ctes_of)
          apply assumption+
         apply (clarsimp simp: invs'_def valid_state'_def if_unsafe_then_cap'_def cte_wp_at_ctes_of)
        apply fastforce
       apply simp
  apply auto
  done

lemma arch_pinv_st_tcb_at':
  "\<lbrace>valid_arch_inv' ai and st_tcb_at' (P and op \<noteq> Inactive and op \<noteq> IdleThreadState) t and
    invs' and ct_active'\<rbrace>
     Arch.performInvocation ai
   \<lbrace>\<lambda>rv. st_tcb_at' P t\<rbrace>" (is "?pre (pgi ai) ?post")
proof(cases ai)
  txt {* The preservation rules for each invocation have already been proved by crunch, so
    this just becomes a case distinction. *}
  case InvokePage thus ?thesis
    by (simp add: X64_H.performInvocation_def performX64MMUInvocation_def,
        wp performPageInvocation_st_tcb_at', fastforce elim!: pred_tcb'_weakenE)
next
  case InvokeASIDControl thus ?thesis
    by (simp add: X64_H.performInvocation_def performX64MMUInvocation_def
                  valid_arch_inv'_def,
        wp performASIDControlInvocation_st_tcb_at', fastforce elim!: pred_tcb'_weakenE)
next
  case InvokeASIDPool thus ?thesis
    by (simp add: X64_H.performInvocation_def performX64MMUInvocation_def
                  valid_arch_inv'_def,
        wp performASIDPoolInvocation_st_tcb_at', fastforce elim!: pred_tcb'_weakenE)
next
  case InvokePageTable thus ?thesis
    by (simp add: X64_H.performInvocation_def performX64MMUInvocation_def
                  valid_arch_inv'_def,
        wp performPageTableInvocation_st_tcb_at', fastforce elim!: pred_tcb'_weakenE)
next
  case InvokePageDirectory thus ?thesis
    by (simp add: X64_H.performInvocation_def performX64MMUInvocation_def
                  valid_arch_inv'_def,
        wp performPageDirectoryInvocation_st_tcb_at', fastforce elim!: pred_tcb'_weakenE)
next
  case InvokePDPT thus ?thesis
    by (simp add: X64_H.performInvocation_def performX64MMUInvocation_def
                  valid_arch_inv'_def,
        wp performPDPTInvocation_st_tcb_at', fastforce elim!: pred_tcb'_weakenE)
next
  case InvokeIOPort thus ?thesis
    by (simp add: X64_H.performInvocation_def performX64MMUInvocation_def
                  valid_arch_inv'_def,
        wp performX64PortInvocation_st_tcb_at', fastforce elim!: pred_tcb'_weakenE)
qed

crunch aligned': "Arch.finaliseCap" pspace_aligned'
  (ignore: getObject wp: crunch_wps getASID_wp simp: crunch_simps)

lemmas arch_finalise_cap_aligned' = finaliseCap_aligned'

crunch distinct': "Arch.finaliseCap" pspace_distinct'
  (ignore: getObject wp: crunch_wps getASID_wp simp: crunch_simps)

lemmas arch_finalise_cap_distinct' = finaliseCap_distinct'

crunch nosch [wp]: "Arch.finaliseCap" "\<lambda>s. P (ksSchedulerAction s)"
  (ignore: getObject wp: crunch_wps getASID_wp simp: crunch_simps updateObject_default_def)


crunch st_tcb_at' [wp]: "Arch.finaliseCap" "st_tcb_at' P t"
  (ignore: getObject setObject wp: crunch_wps getASID_wp simp: crunch_simps)

crunch typ_at' [wp]: "Arch.finaliseCap" "\<lambda>s. P (typ_at' T p s)"
  (ignore: getObject setObject wp: crunch_wps getASID_wp simp: crunch_simps)

crunch cte_wp_at':  "Arch.finaliseCap" "cte_wp_at' P p"
  (ignore: getObject setObject wp: crunch_wps getASID_wp simp: crunch_simps)

lemma invs_asid_table_strengthen':
  "invs' s \<and> asid_pool_at' ap s \<and> asid \<le> 2 ^ asid_high_bits - 1 \<longrightarrow>
   invs' (s\<lparr>ksArchState :=
            x64KSASIDTable_update (\<lambda>_. (x64KSASIDTable \<circ> ksArchState) s(asid \<mapsto> ap)) (ksArchState s)\<rparr>)"
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_global_refs'_def global_refs'_def)
  apply (clarsimp simp: valid_arch_state'_def)
  apply (clarsimp simp: valid_asid_table'_def ran_def)
  apply (rule conjI)
   apply (clarsimp split: if_split_asm)
   apply fastforce
  apply (rule conjI)
   apply (clarsimp simp: valid_pspace'_def)
  apply (simp add: valid_machine_state'_def)
  done

lemma freeIndexUpdate_ex_cte:
  "\<lbrace>\<lambda>s. ex_cte_cap_wp_to' (\<lambda>_. True) slot s \<and>
        cte_wp_at' (\<lambda>c. cteCap c = pcap) src s \<and> isUntypedCap pcap\<rbrace>
   updateCap src (capFreeIndex_update (\<lambda>_. idx) pcap)
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to' (\<lambda>_. True) slot s\<rbrace>"
  apply (clarsimp simp:ex_cte_cap_wp_to'_def)
  apply (rule hoare_pre)
  apply (wps)
  apply (wp hoare_vcg_ex_lift updateCap_cte_wp_at_cases)
  apply (clarsimp simp:cte_wp_at_ctes_of isCap_simps)
  apply (rule_tac x = cref in exI)
   apply clarsimp
  done

lemma ex_cte_not_in_untyped_range:
  "\<lbrakk>(ctes_of s) cref = Some (CTE (capability.UntypedCap d ptr bits idx) mnode);
    descendants_of' cref (ctes_of s) = {}; invs' s;
    ex_cte_cap_wp_to' (\<lambda>_. True) x s; valid_global_refs' s\<rbrakk>
   \<Longrightarrow> x \<notin> {ptr .. ptr + 2 ^ bits - 1}"
  apply clarsimp
  apply (drule(1) cte_cap_in_untyped_range)
   apply (fastforce simp:cte_wp_at_ctes_of)+
  done

lemma ucast_asid_high_btis_of_le [simp]:
  "ucast (asid_high_bits_of w) \<le> (2 ^ asid_high_bits - 1 :: machine_word)"
  apply (simp add: asid_high_bits_of_def)
  apply (rule word_less_sub_1)
  apply (rule order_less_le_trans)
  apply (rule ucast_less)
   apply simp
  apply (simp add: asid_high_bits_def)
  done

lemma performASIDControlInvocation_invs' [wp]:
  "\<lbrace>invs' and ct_active' and valid_aci' aci\<rbrace>
  performASIDControlInvocation aci \<lbrace>\<lambda>y. invs'\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: performASIDControlInvocation_def valid_aci'_def
    placeNewObject_def2 cte_wp_at_ctes_of
    split: asidcontrol_invocation.splits)
  apply (rename_tac w1 w2 w3 w4 cte ctea idx)
  apply (case_tac ctea)
  apply (clarsimp)
  apply (frule ctes_of_valid_cap')
   apply fastforce
  apply (rule hoare_pre)
   apply (wp hoare_vcg_const_imp_lift)
       apply (strengthen invs_asid_table_strengthen')
       apply (wp cteInsert_simple_invs)
      apply (wp createObjects'_wp_subst[OF
                createObjects_no_cte_invs[where sz = pageBits and ty="Inl (KOArch (KOASIDPool pool))" for pool]]
                createObjects_orig_cte_wp_at'[where sz = pageBits]  hoare_vcg_const_imp_lift
         |simp add: makeObjectKO_def projectKOs asid_pool_typ_at_ext' valid_cap'_def cong: rev_conj_cong
         |strengthen safe_parent_strg'[where idx= "2^ pageBits"])+
      apply (rule hoare_vcg_conj_lift)
       apply (rule descendants_of'_helper)
       apply (wp createObjects_null_filter'
                  [where sz = pageBits and ty="Inl (KOArch (KOASIDPool ap))" for ap]
                 createObjects_valid_pspace'
                  [where sz = pageBits and ty="Inl (KOArch (KOASIDPool ap))" for ap]
          | simp add: makeObjectKO_def projectKOs asid_pool_typ_at_ext' valid_cap'_def
                cong: rev_conj_cong)+
       apply (simp add: objBits_simps archObjSize_def valid_cap'_def capAligned_def range_cover_full)
      apply (wp  createObjects'_wp_subst[OF createObjects_ex_cte_cap_to[where sz = pageBits]]
                 createObjects_orig_cte_wp_at'[where sz = pageBits]
                 hoare_vcg_const_imp_lift
         |simp add: makeObjectKO_def projectKOs asid_pool_typ_at_ext' valid_cap'_def cong: rev_conj_cong
         |strengthen safe_parent_strg'[where idx = "2^ pageBits"])+
     apply (simp add:asid_pool_typ_at_ext'[symmetric])
     apply (wp createObject_typ_at')
    apply (simp add: objBits_simps archObjSize_def valid_cap'_def
         capAligned_def range_cover_full makeObjectKO_def
         projectKOs asid_pool_typ_at_ext'
         cong: rev_conj_cong)
    apply (clarsimp simp:conj_comms
                         descendants_of_null_filter'
      | strengthen invs_pspace_aligned' invs_pspace_distinct'
          invs_pspace_aligned' invs_valid_pspace')+
    apply (wp updateFreeIndex_forward_invs'
           updateFreeIndex_cte_wp_at
           updateFreeIndex_pspace_no_overlap'
           updateFreeIndex_caps_no_overlap''
           updateFreeIndex_descendants_of2
           updateFreeIndex_caps_overlap_reserved
           updateCap_cte_wp_at_cases freeIndexUpdate_ex_cte static_imp_wp
           getSlotCap_wp)+
  apply (clarsimp simp:conj_comms ex_disj_distrib is_aligned_mask
           | strengthen invs_valid_pspace' invs_pspace_aligned'
                        invs_pspace_distinct' empty_descendants_range_in')+
  apply (wp deleteObjects_invs'[where p="makePoolParent aci"]
            hoare_vcg_ex_lift
            deleteObjects_caps_no_overlap''[where slot="makePoolParent aci"]
            deleteObject_no_overlap
            deleteObjects_cap_to'[where p="makePoolParent aci"]
            deleteObjects_ct_active'[where cref="makePoolParent aci"]
            deleteObjects_descendants[where p="makePoolParent aci"]
            deleteObjects_cte_wp_at'
            deleteObjects_null_filter[where p="makePoolParent aci"])
  apply (frule valid_capAligned)
  apply (clarsimp simp: invs_mdb' invs_valid_pspace' capAligned_def
                        cte_wp_at_ctes_of is_simple_cap'_def isCap_simps)
  apply (strengthen refl ctes_of_valid_cap'[mk_strg I E])
  apply (clarsimp simp: conj_comms invs_valid_objs')
  apply (frule_tac ptr="w1" in descendants_range_caps_no_overlapI'[where sz = pageBits])
    apply (fastforce simp:is_aligned_neg_mask_eq cte_wp_at_ctes_of)
   apply (simp add:empty_descendants_range_in')
  apply (frule(1) if_unsafe_then_capD'[OF _ invs_unsafe_then_cap',rotated])
   apply (fastforce simp:cte_wp_at_ctes_of)
  apply (drule ex_cte_not_in_untyped_range[rotated -2])
      apply (simp add:invs_valid_global')+
  apply (drule ex_cte_not_in_untyped_range[rotated -2])
      apply (simp add:invs_valid_global')+
  apply (subgoal_tac "is_aligned (2 ^ pageBits) minUntypedSizeBits")
   prefer 2
   apply (rule is_aligned_weaken)
    apply (rule is_aligned_shiftl_self[unfolded shiftl_t2n,where p = 1, simplified])
   apply (simp add: pageBits_def untypedBits_defs)
  apply (frule_tac cte="CTE (capability.UntypedCap False a b c) m" for a b c m in valid_global_refsD', clarsimp)
  apply (simp add: is_aligned_neg_mask_eq Int_commute)
  by (auto simp:empty_descendants_range_in' objBits_simps max_free_index_def
                    archObjSize_def asid_low_bits_def word_bits_def
                    range_cover_full descendants_range'_def2 is_aligned_mask
                    null_filter_descendants_of'[OF null_filter_simp'] bit_simps
                    valid_cap_simps' mask_def)+


(* FIXME: move *)
lemma dmo_invs'_simple:
  "no_irq f \<Longrightarrow>
   (\<And>p um. \<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace> f \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>) \<Longrightarrow>
   \<lbrace> invs' \<rbrace> doMachineOp f \<lbrace> \<lambda>y. invs' \<rbrace>"
  by (rule hoare_pre, rule dmo_invs', wp no_irq, simp_all add:valid_def split_def)

lemma dmo_out8_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (out8 a b) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_out8 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: out8_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_out16_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (out16 a b) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_out16 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: out16_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_out32_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (out32 a b) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_out32 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: out32_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_in8_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (in8 a) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_in8 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: in8_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_in16_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (in16 a) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_in16 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: in16_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma dmo_in32_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (in32 a) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (wp dmo_invs' no_irq_in32 no_irq)
  apply clarsimp
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = underlying_memory m p"
         in use_valid[where P=P and Q="\<lambda>_. P" for P])
    apply (simp add: in32_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+
  done

lemma arch_performInvocation_invs':
  "\<lbrace>invs' and ct_active' and valid_arch_inv' invocation\<rbrace>
  Arch.performInvocation invocation
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  unfolding X64_H.performInvocation_def
  apply (cases invocation, simp_all add: performX64MMUInvocation_def valid_arch_inv'_def,
      (wp|wpc|simp)+)
   apply (clarsimp simp: performX64PortInvocation_def)
   apply (wpsimp simp: portIn_def portOut_def)
  by (clarsimp simp: invs'_def cur_tcb'_def)

end

end
