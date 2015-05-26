(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_floor2_examp.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Sud, France
 *               2013-2015 IRT SystemX, France
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

header{* Part ... *}

theory  OCL_compiler_floor2_examp
imports OCL_compiler_floor1_examp
begin

section{* Translation of AST *}

subsection{* example *}

definition "print_examp_def_st_locale = (\<lambda> OclDefSt n l \<Rightarrow> \<lambda>ocl.
 (\<lambda>d. (d, ocl))
  \<lparr> HolThyLocale_name = \<open>state_\<close> @@ n
  , HolThyLocale_header = [] \<rparr>)"

definition "print_examp_def_st_defassoc_typecheck_gen l ocl =
 ([ raise_ml
      (case
         List.fold
           (\<lambda> OclDefCoreBinding name \<Rightarrow>
            \<lambda>(l, rbt).
             ( ( (if List.assoc name (D_instance_rbt ocl) = None then
                    Cons (Error, name)
                  else
                    id)
               o (if lookup rbt name = None then
                    id
                  else
                    Cons (Warning, name))) l
             , insert name () rbt))
           l
           ([], RBT.empty)
       of
         ([], _) \<Rightarrow> []
       | (l, _) \<Rightarrow> rev_map (\<lambda> (Error, n) \<Rightarrow> (Error, \<open>Extra variables on rhs: \<close> @@ n)
                            | (Warning, n) \<Rightarrow> (Warning, \<open>Duplicate variables on rhs: \<close> @@ n)) l)
      \<open> error(s)\<close> ])"

definition "print_examp_def_st_defassoc_typecheck = (\<lambda> OclDefSt _ l \<Rightarrow> \<lambda> ocl.
  (\<lambda>l_res. (List_map Thy_ml' l_res, ocl \<lparr> D_import_compiler := True \<rparr>))
  (print_examp_def_st_defassoc_typecheck_gen
    l
    ocl))"

definition "print_examp_def_st_mapsto_gen f ocl =
  List_map
    (\<lambda>(cpt, ocore).
        let b = \<lambda>s. Expr_basic [s]
          ; (ocli, exp) = case ocore of
               OclDefCoreBinding (name, ocli) \<Rightarrow>
                 (ocli, Some (b (print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) name))) in
        f (cpt, ocore) ocli exp)"

definition "print_examp_def_st_mapsto ocl l = list_bind id id
 (print_examp_def_st_mapsto_gen
    (\<lambda>(cpt, _) ocli. map_option (\<lambda>exp.
      Expr_binop (Expr_oid var_oid_uniq (oidGetInh cpt)) \<open>\<mapsto>\<close> (Expr_apply (datatype_in @@ isub_of_str (Inst_ty ocli)) [exp])))
    ocl
    l)"

definition "print_examp_def_st2 = (\<lambda> OclDefSt name l \<Rightarrow> \<lambda>ocl.
 (\<lambda>(l, l_st). (List_map Thy_definition_hol' l, ocl \<lparr> D_state_rbt := (String_to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e name, l_st) # D_state_rbt ocl \<rparr>))
  (let b = \<lambda>s. Expr_basic [s]
     ; l = List_map (\<lambda> OclDefCoreBinding name \<Rightarrow> map_option (Pair name) (List.assoc name (D_instance_rbt ocl))) l
     ; (rbt, (map_self, map_username)) =
         (init_map_class 
           (ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr>)
           (List_map (\<lambda> Some (_, ocli, _) \<Rightarrow> ocli | None \<Rightarrow> ocl_instance_single_empty) l)
          :: (_ \<Rightarrow> _ \<times> _ \<times> (_ \<Rightarrow> ((_ \<Rightarrow> nat \<Rightarrow> _ \<Rightarrow> _) \<Rightarrow> _
                        \<Rightarrow> (ocl_ty_class option \<times> (ocl_ty \<times> ocl_data_shallow) option) list) option)) \<times> _ \<times> _)
     ; (l_st, l_assoc) = fold_list (\<lambda> o_n l_assoc.
           case o_n of
              Some (name, ocli, cpt) \<Rightarrow> ([(cpt, OclDefCoreBinding (name, ocli))], (ocli, cpt) # l_assoc)
            | None \<Rightarrow> ([], l_assoc)) l []
     ; l_st = List_unique oidGetInh (List_flatten l_st) in

   ( [ Definition (Expr_rewrite (b name) \<open>=\<close> (Expr_apply \<open>state.make\<close>
        ( Expr_apply \<open>Map.empty\<close> (case print_examp_def_st_mapsto ocl l_st of None \<Rightarrow> [] | Some l \<Rightarrow> l)
        # [ print_examp_def_st_assoc (snd o rbt) map_self map_username l_assoc ]))) ]
   , l_st)))"

definition "print_examp_def_st_dom_name name = flatten [\<open>dom_\<close>, name]"
definition "print_examp_def_st_dom = (\<lambda> _ ocl.
 (\<lambda> l. (List_map Thy_lemma_by' l, ocl))
  (let (name, l_st) = map_prod String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_to_String id (hd (D_state_rbt ocl))
     ; a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition in
   [ Lemma_by
       (print_examp_def_st_dom_name name)
       [Expr_rewrite (a \<open>dom\<close> (a \<open>heap\<close> (b name))) \<open>=\<close> (Expr_set (List_map (\<lambda>(cpt, _). Expr_oid var_oid_uniq (oidGetInh cpt)) l_st))]
       []
       (Tacl_by [Tac_auto_simp_add [d name]])]))"

definition "print_examp_def_st_dom_lemmas = (\<lambda> _ ocl.
 (\<lambda> l. (List_map Thy_lemmas_simp' l, ocl))
  (let (name, _) = hd (D_state_rbt ocl) in
   [ Lemmas_simp \<open>\<close>
       [Thm_str (print_examp_def_st_dom_name (String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_to_String name))] ]))"

definition "print_examp_def_st_perm_name name = flatten [\<open>perm_\<close>, name]"
definition "print_examp_def_st_perm = (\<lambda> _ ocl.
 (\<lambda> l. (List_map Thy_lemma_by' l, ocl))
  (let (name, l_st) = map_prod String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_to_String id (hd (D_state_rbt ocl))
     ; expr_app = let ocl = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr> in
                  print_examp_def_st_mapsto
                    ocl
                    (rev l_st)
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition
     ; (l_app, l_last) =
         case l_st of [] \<Rightarrow> ([], Tacl_by [Tac_simp_add [d name]])
         | [_] \<Rightarrow> ([], Tacl_by [Tac_simp_add [d name]])
         | _ \<Rightarrow>
           ( [ Tac_simp_add (List_map d (name # List_map (\<lambda>(cpt, _). var_oid_uniq @@ natural_of_str (case oidGetInh cpt of Oid i \<Rightarrow> i)) l_st))]
             # List_flatten (List_map (\<lambda>i_max. List_map (\<lambda>i. [Tac_subst_l (List_map nat_of_str [i_max - i]) (Thm_str \<open>fun_upd_twist\<close>), Tac_simp]) (List.upt 0 i_max)) (List.upt 1 (List.length l_st)))
           , Tacl_by [Tac_simp]) in
   case expr_app of None \<Rightarrow> [] | Some expr_app \<Rightarrow>
   [ Lemma_by
       (print_examp_def_st_perm_name name)
       [Expr_rewrite (b name) \<open>=\<close> (Expr_apply \<open>state.make\<close>
          (let s_empty = \<open>Map.empty\<close> in
           Expr_apply s_empty expr_app # [Expr_apply var_assocs [b name]]))]
       l_app
       l_last ]))"

definition "extract_state ocl name_st l_st =
 (let b = \<lambda>s. Expr_basic [s]
    ; ocl = ocl \<lparr> D_oid_start := oidReinitInh (D_oid_start ocl) \<rparr> in
  print_examp_def_st_mapsto_gen
                    (\<lambda>(_, ocore) ocli exp.
                      ( ocore
                      , ocli
                      , case ocore of
                          OclDefCoreBinding (name, ocli) \<Rightarrow>
                            b name))
                    ocl
                    l_st)"

definition "print_examp_def_st_allinst = (\<lambda> _ ocl.
 (\<lambda> l. (List_map Thy_lemma_by' l, ocl))
  (let (name_st, l_st) = map_prod String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_to_String id (hd (D_state_rbt ocl))
     ; b = \<lambda>s. Expr_basic [s]
     ; expr_app = extract_state ocl name_st l_st
     ; a = \<lambda>f x. Expr_apply f [x]
     ; d = hol_definition
     ; l_st_oid = List_map (\<lambda>(cpt, _). var_oid_uniq @@ natural_of_str (case oidGetInh cpt of Oid i \<Rightarrow> i)) l_st in
   map_class_gen_h'_inh (\<lambda> isub_name name compare.
     let expr_app = List_map (\<lambda>(ocore, ocli, exp).
              ( ocore
              , let exp_annot = [(Expr_postunary (case ocore of OclDefCoreBinding _ \<Rightarrow> exp) (b (dot_astype name)), True, ocore)] in
                case compare (Inst_ty ocli) of
                  EQ \<Rightarrow> [(exp, False, ocore)]
                | LT \<Rightarrow> exp_annot
                | GT \<Rightarrow> (case Inst_attr ocli of OclAttrCast name2 _ _ \<Rightarrow>
                           if String_equal name name2 then exp_annot
                           else [] | _ \<Rightarrow> [])
                | UN' \<Rightarrow> [])) expr_app
       ; (l_spec, l_body) = List_split (List_flatten (List_map snd expr_app)) in
     gen_pre_post
       (\<lambda>s. flatten [ name_st, \<open>_\<close>, s, \<open>_exec_\<close>, name ])
       (\<lambda>f_expr f_mk _. Expr_binop
            (f_mk (b name_st))
            \<open>\<Turnstile>\<close>
            (Expr_binop (f_expr [b name]) \<open>\<doteq>\<close> (Expr_oclset l_spec)))
       (\<lambda>lem_tit lem_spec var_pre_post var_mk _. Lemma_by_assum
         lem_tit
         [(\<open>\<close>, True, Expr_And \<open>a\<close> (\<lambda>var_a. Expr_rewrite (a var_pre_post (a var_mk (b var_a))) \<open>=\<close> (b var_a)))]
         lem_spec
         (List_map App
           (List_flatten
            [ [[Tac_subst (Thm_str (print_examp_def_st_perm_name name_st))]]
            , [[Tac_simp_only
                 (List_map
                   (Thm_str o d)
                   (List_flatten
                      [ [\<open>state.make\<close>]
                      , l_st_oid
                      , List_flatten (List_map (\<lambda>(_, ocore).
                          case ocore of
                            OclDefCoreBinding (n, ocli) \<Rightarrow>
                              [if D_design_analysis ocl = Gen_only_design then
                                 print_examp_def_st_inst_var_name ocli name_st
                               else
                                 n]) l_body)
                      , List_flatten (List_map (\<lambda>(cast, ocore).
                          if cast then
                            case
                              case\<^sub>S\<^sub>c\<^sub>a\<^sub>l\<^sub>a ocore of OclDefCoreBinding (_, ocli) \<Rightarrow> Some ocli
                            of Some ocli \<Rightarrow> [print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) (inst_name ocli)]
                             | None \<Rightarrow> []
                          else []) l_body) ]))]]
            , fst (fold_list (\<lambda> expr l_spec.
                let mk_StrictRefEq_including = \<lambda>l.
                      Tac_rule (Thm_str \<open>const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_including\<close>)
                      # Tac_simp # Tac_simp # Tac_simp # l
                  ; (state_update_vs_allInstances_generic, l_spec, l_print_examp, l_OclIncluding_cong) =
                  case expr of (ocore, []) \<Rightarrow>
                    ( \<open>state_update_vs_allInstances_generic_ntc\<close>
                    , l_spec
                    , case ocore of OclDefCoreBinding (_, ocli) \<Rightarrow> [print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) (inst_name ocli)]
                    , if l_spec = [] then
                        [Tac_rule (Thm_str \<open>const_StrictRefEq\<^sub>S\<^sub>e\<^sub>t_empty\<close>), Tac_simp]
                      else
                        mk_StrictRefEq_including [])
                  | _ \<Rightarrow>
                    ( \<open>state_update_vs_allInstances_generic_tc\<close>
                    , tl l_spec
                    , []
                    , mk_StrictRefEq_including [ Tac_rule (Thm_str \<open>OclIncluding_cong\<close>), Tac_simp, Tac_simp ]) in
                ( Tac_subst (Thm_str state_update_vs_allInstances_generic)
                  # Tac_simp # Tac_simp
                  # Tac_simp_add (List_map d ((flatten [isub_name const_oclastype, \<open>_\<AA>\<close>]) # l_print_examp))
                  # Tac_simp
                  # l_OclIncluding_cong
                , l_spec) ) expr_app l_spec)
            , [[Tac_rule (Thm_str \<open>state_update_vs_allInstances_generic_empty\<close>)]] ]))
         (Tacl_by [ if l_spec = [] then Tac_simp
                    else Tac_simp_all_add [d (flatten [isub_name const_oclastype, \<open>_\<AA>\<close>])]]) )
       [Tac_simp])
     (case D_class_spec ocl of Some class_spec \<Rightarrow> class_spec)))"

definition "merge_unique_gen f l = List.fold (List.fold (\<lambda>x. case f x of Some (x, v) \<Rightarrow> RBT.insert x v | None \<Rightarrow> id)) l RBT.empty"
definition "merge_unique f l = RBT.entries (merge_unique_gen f l)"
definition "merge_unique' f l = List_map (map_prod (\<lambda>s. \<lless>s\<ggreater>) id)
                                        (merge_unique (map_option (map_prod String_to_list id) o f) l)"

definition "get_state f = (\<lambda> OclDefPP _ s_pre s_post \<Rightarrow> \<lambda> ocl. 
  let l_st = D_state_rbt ocl
    ; get_state = \<lambda>OclDefPPCoreBinding s \<Rightarrow> (s, case List.assoc s l_st of None \<Rightarrow> [] | Some l \<Rightarrow> l)
    ; (s_pre, l_pre) = get_state s_pre in
  f (s_pre, l_pre) (case s_post of None \<Rightarrow> (s_pre, l_pre) | Some s_post \<Rightarrow> get_state s_post) ocl)"

definition "l_const_oid_of ocl =
          (* over-approximation of classes to unfold (inherited ones need to be taken into account) *)
          (* NOTE can be moved to a global ''lemmas'' *)
          List_map
            (\<lambda> isub_name. const_oid_of (isub_name datatype_name))
            (snd (fold_class (\<lambda>isub_name _ _ _ _ _ l. Pair () (isub_name # l))
                             []
                             (case D_class_spec ocl of Some c \<Rightarrow> c)))"

definition "print_pre_post_locale = get_state (\<lambda> (s_pre, l_pre) (s_post, l_post). Pair
  \<lparr> HolThyLocale_name = \<open>pre_post_\<close> @@ s_pre @@ \<open>_\<close> @@ s_post
  , HolThyLocale_header = [] \<rparr>)"

definition "print_pre_post_wff = get_state (\<lambda> (s_pre, l_pre) (s_post, l_post) ocl.
 (\<lambda> l. (List_map Thy_lemma_by' l, ocl))
  (let a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition in
   [ Lemma_by
      (flatten [\<open>basic_\<close>, s_pre, \<open>_\<close>, s_post, \<open>_wff\<close>])
      [a \<open>WFF\<close> (Expr_pair (b s_pre) (b s_post))]
      []
      (Tacl_by [Tac_simp_add (List_map d (List_flatten
        [ [ \<open>WFF\<close>, s_pre, s_post, const_oid_of \<open>\<AA>\<close> ]
        , List_map
            (\<lambda>(cpt, _). var_oid_uniq @@ natural_of_str (case cpt of Oid i \<Rightarrow> i))
            (merge_unique ((\<lambda>x. Some (x, ())) o oidGetInh o fst) [l_pre, l_post])
        , List_map fst
            (merge_unique'
              (\<lambda>(_, ocore). case ocore of OclDefCoreBinding (_, ocli) \<Rightarrow>
                Some (print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) (inst_name ocli), ()))
              [l_pre, l_post])
        , l_const_oid_of ocl ]))]) ] ))"

definition "print_pre_post_where = get_state (\<lambda> (s_pre, l_pre) (s_post, l_post) ocl.
 (\<lambda> l. ((List_map Thy_lemma_by' o List_flatten) l, ocl))
  (let a = \<lambda>f x. Expr_apply f [x]
     ; b = \<lambda>s. Expr_basic [s]
     ; d = hol_definition in
   let f_name = \<lambda>(cpt, ocore). Some (oidGetInh cpt, ocore)
     ; rbt_pre = merge_unique_gen f_name [l_pre]
     ; rbt_post = merge_unique_gen f_name [l_post]
     ; filter_ocore = \<lambda>x_pers_oid. case (RBT.lookup rbt_pre x_pers_oid, RBT.lookup rbt_post x_pers_oid) of
             (Some ocore1, Some ocore2) \<Rightarrow> (\<open>OclIsMaintained\<close>, case (ocore1, ocore2) of (OclDefCoreBinding _, OclDefCoreBinding _) \<Rightarrow>
                                                                 let l = [(ocore1, s_pre), (ocore2, s_post)] in
                                                                 if String_to_list s_pre = String_to_list s_post then [hd l] else l)
           | (Some ocore, None) \<Rightarrow> (\<open>OclIsDeleted\<close>, [(ocore, s_pre)])
           | (None, Some ocore) \<Rightarrow> (\<open>OclIsNew\<close>, [(ocore, s_post)])
     ; l_oid_of = l_const_oid_of ocl in
   List_map
     (\<lambda>x_pers_oid.
       let (x_where, l_ocore) = filter_ocore x_pers_oid in
       List_map (\<lambda>(ocore, name_st).
         let (x_where, x_name, x_pers_expr) =
           ( x_where
           , case ocore of OclDefCoreBinding (name, ocli) \<Rightarrow>
               let name =
                 if D_design_analysis ocl = Gen_only_design then
                   print_examp_def_st_inst_var_name ocli name_st
                 else
                   name in
               (Some (name, print_examp_instance_name (\<lambda>s. s @@ isub_of_str (Inst_ty ocli)) (inst_name ocli)), b name)) in
         Lemma_by (flatten [var_oid_uniq, natural_of_str (case x_pers_oid of Oid i \<Rightarrow> i), s_pre, s_post, \<open>_\<close>, name_st, \<open>_\<close>, x_where])
          [Expr_binop (Expr_pair (b s_pre) (b s_post)) \<open>\<Turnstile>\<close> (a x_where (x_pers_expr))]
          []
          (Tacl_by [Tac_simp_add (List_map d (List_flatten
            [ case x_name of Some (x_pers, x_name) \<Rightarrow> [x_pers, x_name] | _ \<Rightarrow> []
            , [ x_where, \<open>OclValid\<close>, s_pre, s_post, const_oid_of \<open>option\<close> ]
            , List_map
                (\<lambda>(cpt, _). var_oid_uniq @@ natural_of_str (case cpt of Oid i \<Rightarrow> i))
                (merge_unique ((\<lambda>x. Some (x, ())) o oidGetInh o fst) [l_pre, l_post])
            , l_oid_of ]))])) l_ocore)
     (filter (\<lambda>x_pers_oid. list_ex (\<lambda> (OclDefCoreBinding _, _) \<Rightarrow> True)
       (snd (filter_ocore x_pers_oid)))
       (RBT.keys (RBT.union rbt_pre rbt_post))) ))"
end
