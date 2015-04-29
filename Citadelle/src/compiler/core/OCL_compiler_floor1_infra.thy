(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_floor1_infra.thy ---
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

theory  OCL_compiler_floor1_infra
imports OCL_compiler_core_init
begin

section{* Translation of AST *}

subsection{* infrastructure *}

definition "print_infra_enum_synonym _ ocl =
 (List.map_filter (\<lambda> OclAstClassSynonym (OclClassSynonym n1 n2) \<Rightarrow> Some (Thy_ty_synonym (Type_synonym n1 (Ty_base (str_hol_of_ty_all (\<lambda>a _. a) id n2))))
                   | _ \<Rightarrow> None)
                  (fst (find_class_ass ocl)), ocl)"

definition "print_infra_datatype_class = start_map'' Thy_dataty o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited)
      ; map_ty = List_map ((\<lambda>x. Ty_apply (Ty_base \<open>option\<close>) [str_hol_of_ty_all Ty_apply Ty_base x]) o snd) in
    [ Datatype
        (isub_name datatype_ext_name)
        (  (rev_map (\<lambda>x. ( datatype_ext_constr_name @@ mk_constr_name name x
                         , [Raw (datatype_name @@ isub_of_str x)])) (of_sub l_cons))
        @@@@ [(isub_name datatype_ext_constr_name, Raw const_oid # List_maps map_ty l_inherited)])
    , Datatype
        (isub_name datatype_name)
        [ (isub_name datatype_constr_name, Raw (isub_name datatype_ext_name) # map_ty l_attr ) ] ]) expr)"

definition' \<open>print_latex_infra_datatype_class = start_map'' Thy_dataty o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited)
      ; map_ty = List_map ((\<lambda>x. Ty_apply (Ty_base \<open>option\<close>) [str_hol_of_ty_all Ty_apply Ty_base x]) o snd)
      ; n1 = \<open>{ext}\<close>
      ; n2 = \<open>{ty}\<close> in
    [ Datatype
        (\<open>\operatorname{\<close> @@ name @@ \<open>}_\<close> @@ n1 @@ \<open>\<close>)
        (  (rev_map (\<lambda>x. ( \<open>\operatorname{mk}_\text{\<close> @@ name @@ \<open>\_\<close> @@ x @@ \<open>}\<close>
                         , [Raw (\<open>\operatorname{\<close> @@ x @@ \<open>}_\<close> @@ n2 @@ \<open>\<close>)])) (of_sub l_cons))
        @@@@ [(\<open>\operatorname{mk}_\text{\<close> @@ name @@ \<open>}\<close>, Raw const_oid # List_maps map_ty l_inherited)])
    , Datatype
        (\<open>\operatorname{\<close> @@ name @@ \<open>}_\<close> @@ n2 @@ \<open>\<close>)
        [ (\<open>\operatorname{mkoid}_\text{\<close> @@ name @@ \<open>}\<close>, Raw (\<open>\operatorname{\<close> @@ name @@ \<open>}_\<close> @@ n1 @@ \<open>\<close>) # map_ty l_attr ) ] ]) expr)\<close>

definition "print_infra_datatype_universe expr = start_map Thy_dataty
  [ Datatype \<open>\<AA>\<close>
      (map_class (\<lambda>isub_name _ _ _ _ _. (isub_name datatype_in, [Raw (isub_name datatype_name)])) expr) ]"

definition "print_infra_enum _ ocl = (\<lambda>f. (f (D_ocl_env ocl), ocl))
 (List.map_filter
    (\<lambda> OclAstEnum (OclEnum name_ty _) \<Rightarrow>
         Some (Thy_ty_synonym (Type_synonym name_ty (Ty_apply (Ty_base (print_enum_generic name_ty)) [Ty_base \<open>\<AA>\<close>])))
     | _ \<Rightarrow> None))"

definition "print_infra_type_synonym_class _ = start_map id
  (List_map Thy_ty_synonym
    (let ty = \<lambda> t s. Type_synonym (str_of_ty t) (Ty_apply (Ty_base s) [Ty_base \<open>\<AA>\<close>]) in
     (* base type *)
     ty OclTy_base_void ty_void #
     ty OclTy_base_boolean ty_boolean #
     ty OclTy_base_integer ty_integer #
     (*ty OclTy_base_unlimitednatural ty_unlimitednatural #*)
     ty OclTy_base_real ty_real #
     ty OclTy_base_string ty_string #
     (* *)
     Type_synonym0 var_val' [\<open>'\<alpha>\<close>] (\<lambda> [alpha] \<Rightarrow> Ty_apply (Ty_base \<open>val\<close>) [Ty_base \<open>\<AA>\<close>, Ty_base alpha ]) #
     [])
   @@@@
   List_map Thy_ty_notation
     [ Type_notation var_val' \<open>\<cdot>(_)\<close> ])"

definition "print_infra_type_synonym_class_higher expr = start_map Thy_ty_synonym
 (let option = Ty_apply_paren \<open>\<langle>\<close> \<open>\<rangle>\<^sub>\<bottom>\<close> in
  List_flatten
    (map_class
      (\<lambda>isub_name name _ _ _ _.
        [ Type_synonym name
                       (option (option (Ty_base (isub_name datatype_name))))
        (*, Type_synonym name (Ty_apply_paren \<open>\<cdot>\<close> \<open>\<close> (Ty_base (name @@ \<open>'\<close>)))*)])
      expr))"

definition "print_infra_type_synonym_class_rec = (\<lambda>expr ocl.
  map_prod id (\<lambda> D_higher_order_ty. ocl \<lparr> D_higher_order_ty := D_higher_order_ty \<rparr>)
    (List_split (List_map (\<lambda>(tit, body). (Thy_ty_synonym (Type_synonym (String\<^sub>b\<^sub>a\<^sub>s\<^sub>e_to_String tit) body), tit))
                          (snd (fold_class (\<lambda>_ _ l_attr _ _ _.
                                             Pair () o List.fold
                                               (\<lambda>(_, t) l.
                                                 let f = (* WARNING we may test with RBT instead of List *)
                                                         \<lambda>t l.
                                                           let (tit, body) = print_infra_type_synonym_class_rec_aux t in
                                                           if List.assoc tit l = None then (String_to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e tit, body) # l else l in
                                                 case t of
                                                   OclTy_object (OclTyObj (OclTyCore obj) _) \<Rightarrow>
                                                     let t = \<lambda>ty. OclTy_collection (ocl_multiplicity_ext [] None [ty] ()) (OclTy_class_pre (TyObjN_role_ty (TyObj_to obj))) in
                                                     f (t Sequence) (f (t Set) l)
                                                 | OclTy_collection _ _ \<Rightarrow> f t l
                                                 | OclTy_pair _ _ \<Rightarrow> f t l
                                                 | _ \<Rightarrow> l)
                                               l_attr)
                                           []
                                           expr)))))"

definition "print_infra_instantiation_class = start_map'' Thy_instantiation_class o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited) in
    let oid_of = \<open>oid_of\<close> in
    [Instantiation
      (isub_name datatype_name)
      oid_of
      (Expr_rewrite
        (Expr_basic [oid_of])
        \<open>=\<close>
        (Expr_function
                   [ let var_oid = \<open>t\<close> in
                     ( Expr_basic (isub_name datatype_constr_name # var_oid # List_map (\<lambda>_. wildcard) l_attr)
                     , Expr_case
                         (Expr_basic [var_oid])
                         ( ( Expr_apply
                               (isub_name datatype_ext_constr_name)
                               (Expr_basic [var_oid] # List_flatten (List_map (List_map (\<lambda>_. Expr_basic [wildcard])) l_inherited))
                           , Expr_basic [var_oid])
                         # List_map (\<lambda>x. ( Expr_apply (datatype_ext_constr_name @@ mk_constr_name name x) [Expr_basic [var_oid]]
                                         , Expr_apply oid_of [Expr_basic [var_oid]])) (of_sub l_cons)))]))
    ]) expr)"

definition "print_infra_instantiation_universe expr = start_map Thy_instantiation_class
  [ let oid_of = \<open>oid_of\<close> in
    Instantiation \<open>\<AA>\<close> oid_of
      (Expr_rewrite
        (Expr_basic [oid_of])
        \<open>=\<close>
        (Expr_function (map_class (\<lambda>isub_name name _ _ _ _.
    let esc = (\<lambda>h. Expr_basic (h # [name])) in
    (esc (isub_name datatype_in), esc oid_of)) expr))) ]"


definition "print_instantia_def_strictrefeq_name mk_strict name = mk_strict [\<open>_\<close>, isub_of_str name]"
definition "print_instantia_def_strictrefeq = start_map Thy_defs_overloaded o
  map_class (\<lambda>isub_name name _ _ _ _.
    let mk_strict = (\<lambda>l. flatten (\<open>StrictRefEq\<close> # isub_of_str \<open>Object\<close> # l))
      ; s_strict = mk_strict [\<open>_\<close>, isub_of_str name]
      ; var_x = \<open>x\<close>
      ; var_y = \<open>y\<close> in
    Defs_overloaded
      (print_instantia_def_strictrefeq_name mk_strict name)
      (Expr_rewrite (Expr_binop (Expr_annot_ocl (Expr_basic [var_x]) name)
                                \<open>\<doteq>\<close>
                                (Expr_basic [var_y]))
                    \<open>\<equiv>\<close>
                    (Expr_basic [mk_strict [], var_x, var_y])) )"

definition "print_instantia_lemmas_strictrefeq = start_map'
  (if activate_simp_optimization then
     \<lambda>expr.
       let mk_strict = (\<lambda>l. flatten (\<open>StrictRefEq\<close> # isub_of_str \<open>Object\<close> # l))
         ; name_set = map_class (\<lambda>_ name _ _ _ _. print_instantia_def_strictrefeq_name mk_strict name) expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
         [ Lemmas_simp \<open>\<close> (List_map (Thm_str) name_set) ]
  else (\<lambda>_. []))"

end
