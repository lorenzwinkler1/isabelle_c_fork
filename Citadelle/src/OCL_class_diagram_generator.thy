(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_class_diagram_generator.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2014 Universite Paris-Sud, France
 *               2013-2014 IRT SystemX, France
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

theory OCL_class_diagram_generator
imports Main
  keywords "attr_base" "attr_object" "child"
           "oid_start" "thy_dir"
           "THEORY" "IMPORTS" "SECTION"
           "design" "analysis"
           "deep" "shallow"
           "skip" "self"
       and "Class" :: thy_decl
       and "Class.end" :: thy_decl
       and "Instance" :: thy_decl and "Instance_tmp" :: thy_decl
       and "Define_int" :: thy_decl
       and "Define_state" :: thy_decl and "Define_state_tmp" :: thy_decl
       and "generation_mode" :: thy_decl
begin

definition "bug_ocaml_extraction = id"
  (* In this theory, this identifier can be removed everywhere it is used.
     However without this, there is a syntax error when the code is extracted to OCaml. *)

datatype internal_oid = Oid nat
datatype internal_oids =
  Oids nat (* start *)
       nat (* oid for assoc (incremented from start) *)
       nat (* oid for inh (incremented from start) *)

definition "oidInit = (\<lambda> Oid n \<Rightarrow> Oids n n n)"

definition "oidSucAssoc = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 (Suc n2) (Suc n3))"
definition "oidSucInh = (\<lambda> Oids n1 n2 n3 \<Rightarrow> Oids n1 n2 (Suc n3))"
definition "oidGetAssoc = (\<lambda> Oids _ n _ \<Rightarrow> Oid n)"
definition "oidGetInh = (\<lambda> Oids _ _ n \<Rightarrow> Oid n)"

definition "oidReinitInh = (\<lambda>Oids n1 n2 _ \<Rightarrow> Oids n1 n2 n2)"

section{* AST Definition: OCL *}
subsection{* type definition *}

datatype ocl_collection = Set | Sequence

datatype ocl_ty = OclTy_base string
                | OclTy_object string
                | OclTy_collection ocl_collection ocl_ty
                | OclTy_base_raw string

record ocl_operation =
  Op_args :: "(string \<times> ocl_ty) list"
  Op_result :: ocl_ty
  Op_pre :: "(string \<times> string) list"
  Op_post :: "(string \<times> string) list"

datatype ocl_class =
  OclClass
    string (* name of the class *)
    "(string (* name *) \<times> ocl_ty) list" (* attribute *)
    (*"(string (* name *) \<times> ocl_operation) list" (* contract *)
    "(string (* name *) \<times> string) list" (* invariant *) *)
    "ocl_class option" (* link to subclasses *)

datatype ocl_data_shallow = Shall_str string
                          | Shall_binding string
                          | Shall_self internal_oid
                          | Shall_tmp (* FIXME : to remove *)

datatype ocl_list_inh = OclNoInh "(string (* name *) \<times> ocl_data_shallow) list"
                      | OclInh
                          "(string (* name *) \<times> ocl_data_shallow) list" (* inh *)
                          "(string (* name *) \<times> ocl_data_shallow) list" (* own *)
                          string (* cast from *)

datatype ocl_instance_single =
  OclInst
    string (* name *)
    string (* type *)
    ocl_list_inh (* attribute inh *)
    "(string (* name *) \<times> ocl_data_shallow) list" (* attribute own *)

datatype ocl_instance =
  OclInstance "ocl_instance_single list" (* mutual recursive *)

datatype ocl_def_int = OclDefI "string list"

datatype ocl_def_state_core = OclDefCoreAdd ocl_instance_single
                            | OclDefCoreSkip
                            | OclDefCoreBinding string (* name *) string (* type *)

datatype ocl_def_state = OclDefSt
                           string (* name *)
                           "ocl_def_state_core list"

datatype ocl_deep_embed_ast = OclAstClass ocl_class
                            | OclAstInstance ocl_instance
                            | OclAstDefInt ocl_def_int
                            | OclAstDefState ocl_def_state

datatype 'a ocl_deep_embed_input = OclDeepEmbed
                                     bool (* disable_thy_output *)
                                     "(string \<times> string) option" (* file_out_path_dep *)
                                     internal_oids
                                     "nat \<times> nat" (* output_position *)
                                     "nat option" (* None : activate design,
                                                     Some n : activate analysis (with n + 1 assocs) *)
                                     'a

record ocl_definition =
  Def_expr :: string
  Def_args :: "(string \<times> ocl_ty) list"
  Def_result :: ocl_ty

record ocl_association_end =
  Ass_coltyp :: "ocl_collection option"
  Ass_cardinality :: "(nat option \<times> nat option) option"
  Ass_role :: "string option"

record ocl_class_model =
  Mod_id :: string
  Mod_class :: "ocl_class list"
  Mod_assocs\<^sub>2 :: "(string \<times> (ocl_association_end \<times> ocl_association_end)) list"
  Mod_assocs\<^sub>3 :: "(string \<times> (ocl_association_end \<times> ocl_association_end \<times> ocl_association_end)) list"
  Mod_definition :: "(string \<times> ocl_definition) list"

subsection{* ... *}

definition "str_of_ty = (\<lambda> OclTy_base x \<Rightarrow> x | OclTy_object x \<Rightarrow> x)"

fun get_class_hierarchy_aux where
   "get_class_hierarchy_aux l_res (OclClass name l_attr dataty) =
   (let l_res = (name, l_attr) # l_res in
    case dataty of None \<Rightarrow> rev l_res
                 | Some dataty \<Rightarrow> get_class_hierarchy_aux l_res dataty)"
definition "get_class_hierarchy = get_class_hierarchy_aux []"

datatype position = EQ | LT | GT

fun less_than_hierarchy where
  "less_than_hierarchy l item1 item2 =
    (case l of x # xs \<Rightarrow>
               if x = item1 then GT
               else if x = item2 then LT
               else less_than_hierarchy xs item1 item2)"
definition "compare_hierarchy = (\<lambda>l x1 x2. if x1 = x2 then EQ else less_than_hierarchy l x1 x2)"

fun fold_less_gen where "fold_less_gen f_gen f_jump f l = (case l of
    x # xs \<Rightarrow> \<lambda>acc. fold_less_gen f_gen f_jump f xs (f_gen (f x) xs (f_jump acc))
  | [] \<Rightarrow> id)"

definition "fold_less2 = fold_less_gen fold"
definition "fold_less3 = fold_less_gen o fold_less2"

fun flip where "flip (a,b) = (b,a)"
definition "List_map f l = rev (foldl (\<lambda>l x. f x # l) [] l)"
definition "flatten l = foldl (\<lambda>acc l. foldl (\<lambda>acc x. x # acc) acc (rev l)) [] (rev l)"
definition List_append (infixr "@@" 65) where "List_append a b = flatten [a, b]"
definition "List_filter f l = rev (foldl (\<lambda>l x. if f x then x # l else l) [] l)"
definition "rev_map f = foldl (\<lambda>l x. f x # l) []"
definition "fold_list f l accu =
  (let (l, accu) = fold (\<lambda>x (l, accu). let (x, accu) = f x accu in (x # l, accu)) l ([], accu) in
   (rev l, accu))"
definition "char_escape = Char Nibble0 Nibble9"

section{* AST Definition: HOL *}
subsection{* type definition *}

datatype hol_simplety = Opt string | Raw string

datatype hol_dataty = Datatype string (* name *)
                           "(string (* name *) \<times> hol_simplety list (* arguments *)) list" (* constructors *)

datatype hol_raw_ty =
   Ty_apply hol_raw_ty "hol_raw_ty list"
 | Ty_base string

datatype hol_ty_synonym = Type_synonym string (* name *)
                                       hol_raw_ty (* content *)

datatype hol_expr = Expr_case hol_expr (* value *)
                              "(hol_expr (* pattern *) \<times> hol_expr (* to return *)) list"
                  | Expr_rewrite hol_expr (* left *) string (* symb rewriting *) hol_expr (* right *)
                  | Expr_basic "string list"
                  | Expr_oid string (* prefix *) internal_oid
                  | Expr_binop hol_expr string hol_expr
                  | Expr_annot hol_expr string (* type *)
                  | Expr_lambda string (* lambda var *) hol_expr
                  | Expr_lambdas "string list" hol_expr
                  | Expr_lambdas0 hol_expr hol_expr
                  | Expr_function "(hol_expr (* pattern *) \<times> hol_expr (* to return *)) list"
                  | Expr_apply string "hol_expr list"
                  | Expr_applys hol_expr "hol_expr list"
                  | Expr_some hol_expr (* with annotation \<lfloor> ... \<rfloor> *)
                  | Expr_preunary hol_expr hol_expr (* no parenthesis and separated with one space *)
                  | Expr_postunary hol_expr hol_expr (* no parenthesis and separated with one space *)
                  | Expr_warning_parenthesis hol_expr (* optional parenthesis that can be removed but a warning will be raised *)
                  | Expr_parenthesis hol_expr (* mandatory parenthesis *)

datatype hol_instantiation_class = Instantiation string (* name *)
                                                 string (* name in definition *)
                                                 hol_expr

datatype hol_defs_overloaded = Defs_overloaded string (* name *) hol_expr (* content *)

datatype hol_consts_class = Consts_raw string (* name *)
                                       hol_raw_ty (* type in *)
                                       hol_raw_ty (* type out *)
                                       string (* ocl 'post' mixfix *)

datatype hol_definition_hol = Definition hol_expr
                            | Definition_abbrev string (* name *) "hol_expr (* syntax extension *) \<times> nat (* priority *)" hol_expr
                            | Definition_abbrev0 string (* name *) hol_expr (* syntax extension *) hol_expr

datatype hol_ntheorem = Thm_str string
                      | Thm_strs string nat (* nth to select *)
                      | Thm_THEN hol_ntheorem hol_ntheorem
                      | Thm_simplified hol_ntheorem hol_ntheorem
                      | Thm_symmetric hol_ntheorem
                      | Thm_where hol_ntheorem "(string \<times> hol_expr) list"
                      | Thm_of hol_ntheorem "hol_expr list"
                      | Thm_OF hol_ntheorem hol_ntheorem

datatype hol_lemmas_simp = Lemmas_simp string (* name *)
                                       "hol_ntheorem list"

datatype hol_tactic = Tac_rule hol_ntheorem
                    | Tac_erule hol_ntheorem
                    | Tac_elim hol_ntheorem
                    | Tac_subst hol_ntheorem
                    | Tac_insert "hol_ntheorem list"
                    | Tac_plus "hol_tactic list"
                    | Tac_simp | Tac_simp_add "string list" | Tac_simp_only "hol_ntheorem list"
                    | Tac_simp_all | Tac_simp_all_add string
                    | Tac_auto_simp_add "string list"
                    | Tac_auto_simp_add_split "hol_ntheorem list" "string list"
                    | Tac_rename_tac "string list"
                    | Tac_case_tac hol_expr

datatype hol_tactic_last = Tacl_done
                         | Tacl_by "hol_tactic list"
                         | Tacl_sorry

datatype hol_tac_apply = App "hol_tactic list" (* apply (... ',' ...) *)
                       | App_using "hol_ntheorem list" (* using ... *)

datatype hol_lemma_by = Lemma_by string (* name *) "hol_expr list" (* specification to prove *)
                          "hol_tactic list list" (* tactics : apply (... ',' ...) '\n' apply ... *)
                          hol_tactic_last
                      | Lemma_by_assum string (* name *)
                          "(string (* name *) \<times> hol_expr) list" (* specification to prove (assms) *)
                          hol_expr (* specification to prove (conclusion) *)
                          "hol_tac_apply list"
                          hol_tactic_last

datatype hol_section_title = Section_title nat (* nesting level *)
                                           string (* content *)

datatype hol_thy = Thy_dataty hol_dataty
                 | Thy_ty_synonym hol_ty_synonym
                 | Thy_instantiation_class hol_instantiation_class
                 | Thy_defs_overloaded hol_defs_overloaded
                 | Thy_consts_class hol_consts_class
                 | Thy_definition_hol hol_definition_hol
                 | Thy_lemmas_simp hol_lemmas_simp
                 | Thy_lemma_by hol_lemma_by
                 | Thy_section_title hol_section_title

subsection{* ... *}

definition "wildcard = ''_''"

definition "escape_unicode c = flatten [[Char Nibble5 NibbleC], ''<'', c, ''>'']"

definition "isub_of_str = flatten o List_map (\<lambda>c. escape_unicode ''^sub'' @@ [c])"
definition "isup_of_str = flatten o List_map (\<lambda>c. escape_unicode [char_of_nat (nat_of_char c - 32)])"
definition "lowercase_of_str = List_map (\<lambda>c. let n = nat_of_char c in if n < 97 then char_of_nat (n + 32) else c)"
definition "number_of_str = flatten o List_map (\<lambda>c. escape_unicode ([''zero'', ''one'', ''two'', ''three'', ''four'', ''five'', ''six'', ''seven'', ''eight'', ''nine''] ! (nat_of_char c - 48)))"

definition "mk_constr_name name = (\<lambda> x. flatten [isub_of_str name, ''_'', isub_of_str x])"
definition "mk_dot = (\<lambda>s1 s2. flatten [''.'', s1, s2])"
definition "mk_dot_par = (\<lambda>dot s. flatten [dot, ''('', s, '')''])"

definition "hol_definition s = flatten [s, ''_def'']"
definition "hol_split s = flatten [s, ''.split'']"

subsection{* ... *}

definition "object = OclTy_object ''oid''"

definition "ty_boolean = ''Boolean''"

definition "unicode_equiv = escape_unicode ''equiv''"
definition "unicode_doteq = escape_unicode ''doteq''"
definition "unicode_tau = escape_unicode ''tau''"
definition "unicode_alpha = escape_unicode ''alpha''"
definition "unicode_delta = escape_unicode ''delta''"
definition "unicode_upsilon = escape_unicode ''upsilon''"
definition "unicode_bottom = escape_unicode ''bottom''"
definition "unicode_AA = escape_unicode ''AA''"
definition "unicode_Turnstile = escape_unicode ''Turnstile''"
definition "unicode_triangleq = escape_unicode ''triangleq''"
definition "unicode_not = escape_unicode ''not''"
definition "unicode_or = escape_unicode ''or''"
definition "unicode_circ = escape_unicode ''circ''"
definition "unicode_mapsto = escape_unicode ''mapsto''"

definition "datatype_ext_name = ''type''"
definition "datatype_name = datatype_ext_name @@ str_of_ty object"
definition "datatype_ext_constr_name = ''mk''"
definition "datatype_constr_name = datatype_ext_constr_name @@ str_of_ty object"
definition "datatype_in = ''in''"

definition "const_oclastype = ''OclAsType''"
definition "const_oclistypeof = ''OclIsTypeOf''"
definition "const_ocliskindof = ''OclIsKindOf''"
definition "const_mixfix dot_ocl name = (let t = \<lambda>s. Char Nibble2 Nibble7 # s in
                                         flatten [dot_ocl, t ''('', name, t '')''])"
definition "dot_oclastype = ''.oclAsType''"
definition "dot_oclistypeof = ''.oclIsTypeOf''"
definition "dot_ocliskindof = ''.oclIsKindOf''"
definition "dot_astype = mk_dot_par dot_oclastype"
definition "dot_istypeof = mk_dot_par dot_oclistypeof"
definition "dot_iskindof = mk_dot_par dot_ocliskindof"

definition "var_in_pre_state = ''in_pre_state''"
definition "var_in_post_state = ''in_post_state''"
definition "var_reconst_basetype = ''reconst_basetype''"
definition "var_oid_uniq = ''oid''"
definition "var_eval_extract = ''eval_extract''"
definition "var_deref = ''deref''"
definition "var_deref_oid = ''deref_oid''"
definition "var_deref_assocs = ''deref_assocs''"
definition "var_select = ''select''"
definition "var_select_object = ''select_object''"
definition "var_choose = ''choose''"
definition "var_switch = ''switch''"
definition "var_assocs = ''assocs''"
definition "var_at_when_hol_post = ''''"
definition "var_at_when_hol_pre = ''at_pre''"
definition "var_at_when_ocl_post = ''''"
definition "var_at_when_ocl_pre = ''@pre''"
definition "var_OclInt = ''OclInt''"

section{* Translation of AST *}

fun fold_class_gen_aux where
   "fold_class_gen_aux l_inherited l_res l_cons f accu (OclClass name l_attr dataty) = (
      let l_cons = tl l_cons
        ; (r, accu) = f (\<lambda>s. s @@ isub_of_str name) name l_attr l_inherited l_cons (dataty = None) accu in
      let l_res = r # l_res in
      case dataty
      of None \<Rightarrow> (flatten l_res, accu)
       | Some dataty \<Rightarrow> fold_class_gen_aux ((name, l_attr) # l_inherited) l_res l_cons f accu dataty)"
definition "fold_class_gen f accu expr = fold_class_gen_aux [] [] (List_map fst (get_class_hierarchy expr)) f accu expr"

definition "map_class_gen f = fst o fold_class_gen
  (\<lambda> isub_name name l_attr l_inh l_cons last_d. \<lambda> () \<Rightarrow>
    (f isub_name name l_attr l_inh l_cons last_d, ())) ()"

definition "add_hierarchy f x = (\<lambda>isub_name name _ _ _ _. f isub_name name (List_map fst (get_class_hierarchy x)))"
definition "add_hierarchy' f x = (\<lambda>isub_name name _ _ _ _. f isub_name name (get_class_hierarchy x))"
definition "add_hierarchy'' f x = (\<lambda>isub_name name l_attr _ _ _. f isub_name name (get_class_hierarchy x) l_attr)"
definition "add_hierarchy''' f x = (\<lambda>isub_name name l_attr l_inh _ last_dataty. f isub_name name (get_class_hierarchy x) l_attr (List_map snd l_inh) last_dataty)"
definition "add_hierarchy'''' f x = (\<lambda>isub_name name l_attr l_inh l_cons _. f isub_name name (get_class_hierarchy x) l_attr (List_map snd l_inh) l_cons)"
definition "map_class f = map_class_gen (\<lambda>isub_name name l_attr l_inh l_cons last_dataty. [f isub_name name l_attr l_inh l_cons last_dataty])"
definition "fold_class f = fold_class_gen (\<lambda>isub_name name l_attr l_inh l_cons last_dataty accu. let (x, accu) = f isub_name name l_attr l_inh l_cons last_dataty accu in ([x], accu))"
definition "map_class_gen_h f x = map_class_gen (add_hierarchy f x) x"
definition "map_class_gen_h' f x = map_class_gen (add_hierarchy' f x) x"
definition "map_class_gen_h'' f x = map_class_gen (add_hierarchy'' f x) x"
definition "map_class_gen_h''' f x = map_class_gen (add_hierarchy''' f x) x"
definition "map_class_gen_h'''' f x = map_class_gen (add_hierarchy'''' f x) x"
definition "map_class_h f x = map_class (add_hierarchy f x) x"
definition "map_class_h' f x = map_class (add_hierarchy' f x) x"
definition "map_class_h'' f x = map_class (add_hierarchy'' f x) x"
definition "map_class_h'''' f x = map_class (add_hierarchy'''' f x) x"
definition "map_class_arg_only f = map_class_gen (\<lambda> isub_name name l_attr _ _ _. case l_attr of [] \<Rightarrow> [] | l \<Rightarrow> f isub_name name l)"
definition "map_class_arg_only' f = map_class_gen (\<lambda> isub_name name l_attr l_inh l_cons _. case filter (\<lambda> (_, []) \<Rightarrow> False | _ \<Rightarrow> True) l_inh of [] \<Rightarrow> [] | l \<Rightarrow> f isub_name name (l_attr, l, l_cons))"
definition "map_class_arg_only0 f1 f2 u = map_class_arg_only f1 u @@ map_class_arg_only' f2 u"
definition "map_class_arg_only_var0 = (\<lambda>f_app f_lattr isub_name name l_attr.
    flatten (flatten (
    List_map (\<lambda>(var_in_when_state, dot_at_when, attr_when).
      flatten (List_map (\<lambda> (attr_orig, l_attr). List_map (\<lambda>(attr_name, attr_ty).
                  f_app
                    isub_name
                    name
                    (var_in_when_state, dot_at_when)
                    attr_orig
                    attr_ty
                    (\<lambda>s. s @@ isup_of_str attr_name)
                    (\<lambda>s. Expr_postunary s (Expr_basic [mk_dot attr_name attr_when]))) l_attr)
               (f_lattr l_attr)))
             [ (var_in_post_state, var_at_when_hol_post, var_at_when_ocl_post)
             , (var_in_pre_state, var_at_when_hol_pre, var_at_when_ocl_pre)])))"
definition "map_class_arg_only_var f1 f2 = map_class_arg_only0 (map_class_arg_only_var0 f1 (\<lambda>l. [(None :: string option, l)])) (map_class_arg_only_var0 f2 (\<lambda>(_, l, _). List_map (\<lambda>(s, l). (Some s, l)) l))"
definition "map_class_arg_only_var' f = map_class_arg_only0 (map_class_arg_only_var0 f (\<lambda>l. [(None, l)])) (map_class_arg_only_var0 f (\<lambda>(_, l, _). List_map (\<lambda>(s, l). (Some s, l)) l))"
definition "map_class_nupl2 f x = rev (fst (fold_less2 (\<lambda>(l, _). (l, None)) (\<lambda>x y (l, acc). (f x y acc # l, Some y)) (rev (get_class_hierarchy x)) ([], None)))"
definition "map_class_nupl3 f x = rev (fold_less3 id id (\<lambda>x y z l. f x y z # l) (rev (get_class_hierarchy x)) [])"
definition "map_class_nupl2' f = map_class_nupl2 (\<lambda>(x,_) (y,_) _. f x y)"
definition "map_class_nupl2'' f = map_class_nupl2 (\<lambda>(x,_) (y,_) opt. f x y (Option.map fst opt))"
definition "map_class_nupl2l f x = rev (fst (fold_less2 (\<lambda>(l, _). (l, [])) (\<lambda>x y (l, acc). (f x y acc # l, y # acc)) (rev (get_class_hierarchy x)) ([], [])))"
definition "map_class_nupl2l' f = map_class_nupl2l (\<lambda>(x,_) (y,_) l. f x y (List_map fst l))"
definition "map_class_nupl3' f = map_class_nupl3 (\<lambda>(x,_) (y,_) (z,_). f x y z)"
definition "map_class_nupl3l f x = rev (fst (fold_less3 (\<lambda>(l, _). (l, [])) id (\<lambda>x y z (l, acc). (f x y z acc # l, z # acc)) (rev (get_class_hierarchy x)) ([], [])))"
definition "map_class_nupl3l' f = map_class_nupl3l (\<lambda>(x,_) (y,_) (z,_) l. f x y z (List_map fst l))"
definition "map_class_nupl3'_GE f x = map_class_nupl2' (\<lambda>x y. f x y y) x @@ map_class_nupl3' f x"
definition "map_class_nupl3'_LE f x = map_class_nupl2' (\<lambda>x y. f x x y) x @@ map_class_nupl3' f x"
definition "map_class_nupl3'_LE' f x = map_class_nupl2l' (\<lambda>x y l. f x x y l) x @@ map_class_nupl3l' f x"
definition "get_hierarchy_fold f f_l x = flatten (flatten (
  let (l1, l2, l3) = f_l (List_map fst (get_class_hierarchy x)) in
  let (_, l) = foldl (\<lambda> (name1_last, l1) name1. (Some name1, List_map (\<lambda>name2. List_map (
  f (name1_last, name1) name2) l3) l2 # l1)) (None, []) l1 in rev l))"
definition "get_hierarchy_map f f_l x = flatten (flatten (
  let (l1, l2, l3) = f_l (List_map fst (get_class_hierarchy x)) in
  List_map (\<lambda>name1. List_map (\<lambda>name2. List_map (f name1 name2) l3) l2) l1))"
definition "split_ty name = List_map (\<lambda>s. hol_split (s @@ isub_of_str name)) [datatype_ext_name, datatype_name]"
definition "thm_OF s l = fold (\<lambda>x acc. Thm_OF acc x) l s"
definition "expr_binop s l = (case rev l of x # xs \<Rightarrow> fold (\<lambda>x. Expr_binop x s) xs x)"
definition "Consts s ty_out mix = Consts_raw s (Ty_base (Char Nibble2 Nibble7 # unicode_alpha)) ty_out mix"
definition "start_map f = fold_list (\<lambda>x acc. (f x, acc))"
definition "start_map' f x accu = (f x, accu)"
definition "start_map''' f fl = (\<lambda> ocl. case ocl of OclDeepEmbed disable_thy_output file_out_path_dep oid_start output_position design_analysis () \<Rightarrow>
  let base_attr = (if design_analysis = None then id else List_filter (\<lambda> (_, OclTy_object _) \<Rightarrow> False | _ \<Rightarrow> True))
    ; base_attr' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, List_map base_attr l_inh))
    ; base_attr'' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, base_attr l_inh)) in
  start_map f (fl design_analysis base_attr base_attr' base_attr'') ocl)"
definition "start_map'' f fl e = start_map''' f (\<lambda>_. fl) e"
definition "start_map'''' f fl = (\<lambda> ocl. case ocl of OclDeepEmbed disable_thy_output file_out_path_dep oid_start output_position design_analysis () \<Rightarrow>
  start_map f (fl design_analysis) ocl)"

subsection{* ... *}

definition "activate_simp_optimization = True"

definition "print_infra_datatype_class = start_map'' Thy_dataty o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, l_inherited) in
    [ Datatype
        (isub_name datatype_ext_name)
        (  (rev_map (\<lambda>x. ( datatype_ext_constr_name @@ mk_constr_name name x
                         , [Raw (datatype_name @@ isub_of_str x)])) l_cons)
        @@ [(isub_name datatype_ext_constr_name, Raw (str_of_ty object) # flatten ( List_map (List_map (\<lambda>(_, x). Opt (str_of_ty x))) l_inherited))])
    , Datatype
        (isub_name datatype_name)
        [ (isub_name datatype_constr_name, [ Raw (isub_name datatype_ext_name) ] @@ List_map (\<lambda>(_, x). Opt (str_of_ty x)) l_attr ) ] ]) expr)"

definition "print_infra_datatype_universe expr = start_map Thy_dataty
  [ Datatype unicode_AA
      (map_class (\<lambda>isub_name _ _ _ _ _. (isub_name datatype_in, [Raw (isub_name datatype_name)])) expr) ]"

definition "print_infra_type_synonym_class expr = start_map Thy_ty_synonym
  (Type_synonym ty_boolean (Ty_apply (Ty_base ty_boolean) [Ty_base unicode_AA]) #
   (map_class (\<lambda>isub_name name _ _ _ _.
     Type_synonym name (Ty_apply (Ty_base ''val'') [Ty_base unicode_AA,
     let option = (\<lambda>x. Ty_apply (Ty_base ''option'') [x]) in
     option (option (Ty_base (isub_name datatype_name))) ])) expr))"

definition "print_infra_instantiation_class = start_map'' Thy_instantiation_class o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, l_inherited) in
    let oid_of = ''oid_of'' in
    [Instantiation
      (isub_name datatype_name)
      oid_of
      (Expr_rewrite
        (Expr_basic [oid_of])
        ''=''
        (Expr_function
                   [ let var_oid = ''t'' in
                     ( Expr_basic (isub_name datatype_constr_name # var_oid # List_map (\<lambda>_. wildcard) l_attr)
                     , Expr_case
                         (Expr_basic [var_oid])
                         ( ( Expr_apply
                               (isub_name datatype_ext_constr_name)
                               (Expr_basic [var_oid] # flatten (List_map (List_map (\<lambda>_. Expr_basic [wildcard])) l_inherited))
                           , Expr_basic [var_oid])
                         # List_map (\<lambda>x. ( Expr_apply (datatype_ext_constr_name @@ mk_constr_name name x) [Expr_basic [var_oid]]
                                         , Expr_apply oid_of [Expr_basic [var_oid]])) l_cons))]))
    ]) expr)"

definition "print_infra_instantiation_universe expr = start_map Thy_instantiation_class
  [ let oid_of = ''oid_of'' in
    Instantiation unicode_AA oid_of
      (Expr_rewrite
        (Expr_basic [oid_of])
        ''=''
        (Expr_function (map_class (\<lambda>isub_name name _ _ _ _.
    let esc = (\<lambda>h. Expr_basic (h # [name])) in
    (esc (isub_name datatype_in), esc oid_of)) expr))) ]"


definition "print_instantia_def_strictrefeq_name mk_strict name = mk_strict [''_'', isub_of_str name]"
definition "print_instantia_def_strictrefeq = start_map Thy_defs_overloaded o
  map_class (\<lambda>isub_name name _ _ _ _.
    let mk_strict = (\<lambda>l. flatten (''StrictRefEq'' # isub_of_str ''Object'' # l))
      ; s_strict = mk_strict [''_'', isub_of_str name]
      ; var_x = ''x''
      ; var_y = ''y'' in
    Defs_overloaded
      (print_instantia_def_strictrefeq_name mk_strict name)
      (Expr_rewrite (Expr_binop (Expr_annot (Expr_basic [var_x]) name)
                                unicode_doteq
                                (Expr_basic [var_y]))
                    unicode_equiv
                    (Expr_basic [mk_strict [], var_x, var_y])) )"

definition "print_instantia_lemmas_strictrefeq = start_map'
  (if activate_simp_optimization then
     \<lambda>expr.
       let mk_strict = (\<lambda>l. flatten (''StrictRefEq'' # isub_of_str ''Object'' # l))
         ; name_set = map_class (\<lambda>_ name _ _ _ _. print_instantia_def_strictrefeq_name mk_strict name) expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
         [ Lemmas_simp '''' (List_map (Thm_str) name_set) ]
  else (\<lambda>_. []))"

subsection{* AsType *}

definition "print_astype_consts = start_map Thy_consts_class o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts (isub_name const_oclastype) (Ty_base name) (const_mixfix dot_oclastype name))"

definition "print_astype_class = start_map'' Thy_defs_overloaded o (\<lambda>expr base_attr _ _.
  map_class_gen_h'' (\<lambda>isub_name name l_hierarchy nl_attr.
    let nl_attr = base_attr nl_attr in
    List_map
      (let l_hierarchy = List_map fst l_hierarchy in (\<lambda> (h_name, hl_attr).
        let hl_attr = base_attr hl_attr in
        Defs_overloaded
          (flatten [isub_name const_oclastype, ''_'', h_name])
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_astype name]))
             unicode_equiv
             (case compare_hierarchy l_hierarchy h_name name
              of EQ \<Rightarrow>
                Expr_basic [var_x]
              | x \<Rightarrow>
                let var_tau = unicode_tau
                  ; val_invalid = Expr_apply ''invalid'' [Expr_basic [var_tau]] in
                Expr_lambda var_tau
                  (Expr_case
                    (Expr_apply var_x [Expr_basic [var_tau]])
                    ( (Expr_basic [unicode_bottom], val_invalid)
                    # (Expr_some (Expr_basic [unicode_bottom]), Expr_apply ''null'' [Expr_basic [var_tau]])
                    # (let pattern_complex = (\<lambda>h_name name l_extra.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; isub_n = (\<lambda>s. isub_name (s @@ ''_''))
                              ; var_name = name in
                             Expr_apply (isub_h datatype_constr_name)
                                        ( Expr_apply (isub_n (isub_h datatype_ext_constr_name)) [Expr_basic [var_name]]
                                        # l_extra) )
                         ; pattern_simple = (\<lambda> name.
                            let isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; var_name = name in
                             Expr_basic [var_name])
                         ; some_some = (\<lambda>x. Expr_some (Expr_some x)) in
                       if x = LT then
                         [ (some_some (pattern_simple h_name), some_some (pattern_complex name h_name (List_map (\<lambda>_. Expr_basic [''None'']) nl_attr))) ]
                       else
                         [ (some_some (pattern_complex h_name name (List_map (\<lambda>_. Expr_basic [wildcard]) hl_attr)), some_some (pattern_simple name))
                         , (Expr_basic [wildcard], val_invalid) ]) ) ))) ))
      l_hierarchy) expr)"

definition "print_astype_from_universe = start_map Thy_definition_hol o
  map_class_h (\<lambda>isub_name name l_hierarchy.
    let const_astype = flatten [const_oclastype, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [const_astype]) ''=''
   (
   (Expr_function (List_map (\<lambda>h_name.
     let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
     ( Expr_apply (isub_h datatype_in) [Expr_basic [h_name]]
     , Expr_warning_parenthesis
       (Expr_postunary (Expr_annot (Expr_applys (bug_ocaml_extraction (let var_x = ''x'' in
                                                      Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))) [Expr_basic [h_name]])
                                   h_name)
                       (Expr_basic [dot_astype name])))) l_hierarchy)))))"

definition "print_astype_from_universe' = start_map'' Thy_definition_hol o (\<lambda>expr base_attr _ _.
  map_class_h'' (\<lambda>isub_name name l_hierarchy nl_attr.
    let nl_attr = base_attr nl_attr in
    let const_astype = flatten [const_oclastype, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [const_astype]) ''=''
   (let ((finish_with_some1, finish_with_some2), last_case_none) =
     let (f, r) = (if (fst o hd) l_hierarchy = name then (id, []) else (flip, [(Expr_basic [wildcard], Expr_basic [''None''])])) in
     (f (id, Expr_some), r) in
   finish_with_some2
   (Expr_function (flatten (List_map
   (let l_hierarchy = List_map fst l_hierarchy in (\<lambda>(h_name, hl_attr).
     let hl_attr = base_attr hl_attr in
     let isub_h = (\<lambda> s. s @@ isub_of_str h_name)
       ; pattern_complex = (\<lambda>h_name name l_extra.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name)
                              ; isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; isub_n = (\<lambda>s. isub_name (s @@ ''_''))
                              ; var_name = name in
                             Expr_apply (isub_h datatype_constr_name)
                                        ( Expr_apply (isub_n (isub_h datatype_ext_constr_name)) [Expr_basic [var_name]]
                                        # l_extra ))
       ; pattern_simple = (\<lambda> name.
                            let isub_name = (\<lambda>s. s @@ isub_of_str name)
                              ; var_name = name in
                             Expr_basic [var_name])
       ; case_branch = (\<lambda>pat res. (Expr_apply (isub_h datatype_in) [pat], finish_with_some1 res)) in
             case compare_hierarchy l_hierarchy h_name name
             of GT \<Rightarrow> case_branch (pattern_complex h_name name (List_map (\<lambda>_. Expr_basic [wildcard]) hl_attr)) (pattern_simple name)
              | EQ \<Rightarrow> let n = Expr_basic [name] in case_branch n n
              | LT \<Rightarrow> case_branch (pattern_simple h_name) (pattern_complex name h_name (List_map (\<lambda>_. Expr_basic [''None'']) nl_attr)))) l_hierarchy
   # [last_case_none])))))) expr)"

definition "print_astype_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_astype_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_astype_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp '''' (List_map (\<lambda>((isub_name, _), name).
    Thm_str (flatten [isub_name const_oclastype, ''_'', name])) name_set) ]))"

definition "print_astype_lemma_cp expr = (start_map Thy_lemma_by o get_hierarchy_map (
  let check_opt =
    let set = print_astype_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma_by
      (flatten [''cp_'', const_oclastype, isub_of_str name1, ''_'', name3, ''_'', name2])
      (bug_ocaml_extraction (let var_p = ''p''; var_x = ''x'' in
       List_map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lambda var_x
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_astype name1])))]))
      []
      (Tacl_by [Tac_rule (Thm_str ''cpI1''), if check_opt name1 name2 then Tac_simp
                                             else Tac_simp_add [flatten [const_oclastype, isub_of_str name1, ''_'', name2]]])
  )) (\<lambda>x. (x, x, x))) expr"

definition "print_astype_lemmas_cp = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [Lemmas_simp '''' (get_hierarchy_map
  (\<lambda>name1 name2 name3.
      Thm_str (flatten [''cp_'', const_oclastype, isub_of_str name1, ''_'', name3, ''_'', name2]))
  (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_astype_lemma_strict expr = (start_map Thy_lemma_by o
 get_hierarchy_map (
  let check_opt =
    let set = print_astype_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma_by
      (flatten [const_oclastype, isub_of_str name1, ''_'', name3, ''_'', name2])
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [name2]) name3)
               (Expr_basic [dot_astype name1])))
             ''=''
             (Expr_basic [name2])]
      []
      (Tacl_by (if check_opt name1 name3 then [Tac_simp]
                else [Tac_rule (Thm_str ''ext'')
                                      , Tac_simp_add (flatten [const_oclastype, isub_of_str name1, ''_'', name3]
                                                      # hol_definition ''bot_option''
                                                      # List_map hol_definition (if name2 = ''invalid'' then [''invalid'']
                                                         else [''null_fun'',''null_option'']))]))
  )) (\<lambda>x. (x, [''invalid'',''null''], x))) expr"

definition "print_astype_lemmas_strict = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [ Lemmas_simp '''' (get_hierarchy_map (\<lambda>name1 name2 name3.
        Thm_str (flatten [const_oclastype, isub_of_str name1, ''_'', name3, ''_'', name2])
      ) (\<lambda>x. (x, [''invalid'',''null''], x)) expr)])
  else (\<lambda>_. []))"

definition "print_astype_defined = start_map Thy_lemma_by o (\<lambda>expr. flatten (map_class_gen_h''' (\<lambda>isub_name name l_hierarchy _ _ _.
     (let l_hierarchy = List_map fst l_hierarchy
        ; var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply unicode_delta [e]) in
    List_map (\<lambda>h_name.
      case compare_hierarchy l_hierarchy h_name name of LT \<Rightarrow>
        [ Lemma_by_assum
          (flatten [isub_name const_oclastype, ''_'', h_name, ''_defined''])
          [(var_isdef, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_astype name])))
          [App_using [Thm_str var_isdef]]
          (Tacl_by [Tac_auto_simp_add (flatten [isub_name const_oclastype, ''_'', h_name]
                                        # ''foundation16''
                                        # List_map hol_definition [''null_option'', ''bot_option'' ])]) ]
      | _ \<Rightarrow> [])
      l_hierarchy)) expr))"

definition "print_astype_up_d_cast0_name name_any name_pers = flatten [''up'', isub_of_str name_any, ''_down'', isub_of_str name_pers, ''_cast0'']"
definition "print_astype_up_d_cast0 = start_map Thy_lemma_by o
  map_class_nupl2' (\<lambda>name_pers name_any.
    let var_X = ''X''
      ; var_isdef = ''isdef''
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (print_astype_up_d_cast0_name name_any name_pers)
        [(var_isdef, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_binop
             (bug_ocaml_extraction (let asty = \<lambda>x ty. Expr_warning_parenthesis (Expr_postunary x
               (Expr_basic [dot_astype ty])) in
               asty (asty (Expr_annot (Expr_basic [var_X]) name_pers) name_any) name_pers))
             unicode_triangleq (Expr_basic [var_X])))
        [App_using [Thm_str var_isdef]]
        (Tacl_by [Tac_auto_simp_add_split
                                    (map Thm_str
                                    ( flatten [const_oclastype, isub_of_str name_any, ''_'', name_pers]
                                    # flatten [const_oclastype, isub_of_str name_pers, ''_'', name_any]
                                    # ''foundation22''
                                    # ''foundation16''
                                    # List_map hol_definition [''null_option'', ''bot_option'' ]))
                                    (split_ty name_pers) ]))"

definition "print_astype_up_d_cast = start_map Thy_lemma_by o
  map_class_nupl2' (\<lambda>name_pers name_any.
    let var_X = ''X''
      ; var_tau = unicode_tau in
    Lemma_by_assum
        (flatten [''up'', isub_of_str name_any, ''_down'', isub_of_str name_pers, ''_cast''])
        []
        (Expr_binop
             (bug_ocaml_extraction (let asty = \<lambda>x ty. Expr_warning_parenthesis (Expr_postunary x
               (Expr_basic [dot_astype ty])) in
               asty (asty (Expr_annot (Expr_basic [var_X]) name_pers) name_any) name_pers))
             ''='' (Expr_basic [var_X]))
        (map App
          [[Tac_rule (Thm_str ''ext''), Tac_rename_tac [var_tau]]
          ,[Tac_rule (Thm_THEN (Thm_str ''foundation22'') (Thm_str ''iffD1''))]
          ,[Tac_case_tac (Expr_binop (Expr_basic [var_tau]) unicode_Turnstile
              (Expr_apply unicode_delta [Expr_basic [var_X]])), Tac_simp_add [print_astype_up_d_cast0_name name_any name_pers]]
          ,[Tac_simp_add [''def_split_local''], Tac_elim (Thm_str ''disjE'')]
          ,[Tac_plus [Tac_erule (Thm_str ''StrongEq_L_subst2_rev''), Tac_simp, Tac_simp]]])
        Tacl_done)"

subsection{* IsTypeOf *}

definition "print_istypeof_consts = start_map Thy_consts_class o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts (isub_name const_oclistypeof) (Ty_base ty_boolean) (const_mixfix dot_oclistypeof name))"

definition "print_istypeof_class = start_map'' Thy_defs_overloaded o (\<lambda>expr base_attr _ _.
  map_class_gen_h''' (\<lambda>isub_name name l_hierarchy _ l_inh _.
    let l_inh = List_map base_attr l_inh in
    List_map
      (let l_hierarchy = List_map fst l_hierarchy in
      (\<lambda> (h_name, hl_attr).
        let hl_attr = base_attr hl_attr in
        Defs_overloaded
          (flatten [isub_name const_oclistypeof, ''_'', h_name])
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_istypeof name]))
             unicode_equiv
             (let var_tau = unicode_tau
                ; ocl_tau = (\<lambda>v. Expr_apply v [Expr_basic [var_tau]]) in
                Expr_lambda var_tau
                  (Expr_case
                    (ocl_tau var_x)
                    ( (Expr_basic [unicode_bottom], ocl_tau ''invalid'')
                    # (Expr_some (Expr_basic [unicode_bottom]), ocl_tau ''true'')
                    # (let l_false = [(Expr_basic [wildcard], ocl_tau ''false'')]
                         ; pattern_complex_gen = (\<lambda>f1 f2.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
                             (Expr_some (Expr_some
                               (Expr_apply (isub_h datatype_constr_name)
                                           ( Expr_apply (f2 (\<lambda>s. isub_name (s @@ ''_'')) (isub_h datatype_ext_constr_name))
                                                        (Expr_basic [wildcard] # f1)
                                           # List_map (\<lambda>_. Expr_basic [wildcard]) hl_attr))), ocl_tau ''true'')
                             # (if h_name = last l_hierarchy then [] else l_false)) in
                       case compare_hierarchy l_hierarchy h_name name
                       of EQ \<Rightarrow> pattern_complex_gen (flatten (List_map (List_map (\<lambda>_. Expr_basic [wildcard])) l_inh)) (\<lambda>_. id)
                        | GT \<Rightarrow> pattern_complex_gen [] id
                        | _ \<Rightarrow> l_false) ) ))) ))
      l_hierarchy) expr)"

definition "print_istypeof_from_universe = start_map Thy_definition_hol o
  map_class_h (\<lambda>isub_name name l_hierarchy.
    let const_istypeof = flatten [const_oclistypeof, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [const_istypeof]) ''=''
   (
   (Expr_function (List_map (\<lambda>h_name.
     let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
     ( Expr_apply (isub_h datatype_in) [Expr_basic [h_name]]
     , Expr_warning_parenthesis
       (Expr_postunary (Expr_annot (Expr_applys (bug_ocaml_extraction (let var_x = ''x'' in
                                                      Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))) [Expr_basic [h_name]])
                                   h_name)
                       (Expr_basic [dot_istypeof name])))) l_hierarchy)))))"

definition "print_istypeof_from_universe' = start_map Thy_definition_hol o
  map_class_h' (\<lambda>isub_name name l_hierarchy.
    let const_istypeof = flatten [const_oclistypeof, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [const_istypeof]) ''=''
   (
   (Expr_function (flatten (flatten (List_map
   (let l_hierarchy = List_map fst l_hierarchy in
    (\<lambda>(h_name, l_attr).
     let pattern_complex_gen = (\<lambda>f1 f2.
                            let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
                            [ (Expr_apply (isub_h datatype_in)
                                [Expr_apply (isub_h datatype_constr_name)
                                            [ Expr_basic [wildcard]
                                            , Expr_apply (f2 (\<lambda>s. isub_name (s @@ ''_'')) (isub_h datatype_ext_constr_name))
                                                         f1]], Expr_basic [''true''])]) in
             case compare_hierarchy l_hierarchy h_name name
             of EQ \<Rightarrow> pattern_complex_gen (List_map (\<lambda>_. Expr_basic [wildcard]) l_attr) (\<lambda>_. id)
              | GT \<Rightarrow> pattern_complex_gen [Expr_basic [wildcard]] id
              | _ \<Rightarrow> [])) l_hierarchy)
   # [[(Expr_basic [wildcard], Expr_basic [''false''])]]))))))"

definition "print_istypeof_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_istypeof_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_istypeof_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp '''' (List_map (\<lambda>((isub_name, _), name).
    Thm_str (flatten [isub_name const_oclistypeof, ''_'', name] )) name_set) ]))"

definition "print_istypeof_lemma_cp expr = (start_map Thy_lemma_by o
  (get_hierarchy_map (
  let check_opt =
    let set = print_istypeof_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 name2 name3.
    Lemma_by
      (flatten [''cp_'', const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2])
      (bug_ocaml_extraction (let var_p = ''p''; var_x = ''x'' in
       List_map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lambda var_x
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_istypeof name1])))]))
      []
      (Tacl_by [Tac_rule (Thm_str ''cpI1''), if check_opt name1 name2 then Tac_simp
                                             else Tac_simp_add [flatten [const_oclistypeof, isub_of_str name1, ''_'', name2]]])
  )) (\<lambda>x. (x, x, x))) ) expr"

definition "print_istypeof_lemmas_cp = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
    (\<lambda>expr. [Lemmas_simp ''''
  (get_hierarchy_map (\<lambda>name1 name2 name3.
      Thm_str (flatten [''cp_'', const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2]))
   (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_istypeof_lemma_strict expr = (start_map Thy_lemma_by o
  get_hierarchy_map (
  let check_opt =
    let set = print_istypeof_lemma_cp_set expr in
    (\<lambda>n1 n2. list_ex (\<lambda>((_, name1), name2). name1 = n1 & name2 = n2) set) in
  (\<lambda>name1 (name2,name2') name3.
    Lemma_by
      (flatten [const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2])
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [name2]) name3)
               (Expr_basic [dot_istypeof name1])))
             ''=''
             (Expr_basic [name2'])]
      []
      (Tacl_by (let l = List_map hol_definition (''bot_option'' # (if name2 = ''invalid'' then [''invalid'']
                                                              else [''null_fun'',''null_option''])) in
                [Tac_rule (Thm_str ''ext''), Tac_simp_add (if check_opt name1 name3 then l
                                                           else flatten [const_oclistypeof, isub_of_str name1, ''_'', name3] # l)]))
  )) (\<lambda>x. (x, [(''invalid'',''invalid''),(''null'',''true'')], x))) expr"

definition "print_istypeof_lemmas_strict_set =
  (if activate_simp_optimization then
    get_hierarchy_map (\<lambda>name1 name2 name3. (name1, name3, name2)) (\<lambda>x. (x, [''invalid'',''null''], x))
   else (\<lambda>_. []))"

definition "print_istypeof_lemmas_strict expr = start_map Thy_lemmas_simp
  (case print_istypeof_lemmas_strict_set expr
   of [] \<Rightarrow> []
    | l \<Rightarrow> [ Lemmas_simp '''' (List_map
      (\<lambda>(name1, name3, name2).
        Thm_str (flatten [const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2]))
      l) ])"

definition "print_istypeof_defined_name isub_name h_name = flatten [isub_name const_oclistypeof, ''_'', h_name, ''_defined'']"
definition "print_istypeof_defined = start_map Thy_lemma_by o flatten o map_class_h (\<lambda>isub_name name l_hierarchy.
     (let var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>symb e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply symb [e]) in
      List_map (\<lambda>h_name.
        Lemma_by_assum
          (print_istypeof_defined_name isub_name h_name)
          [(var_isdef, f unicode_upsilon (Expr_basic [var_X]))]
          (f unicode_delta (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_istypeof name])))
          [App [Tac_insert [Thm_simplified (Thm_str var_isdef) (Thm_str (''foundation18'' @@ [Char Nibble2 Nibble7])) ]
               ,Tac_simp_only [Thm_str (hol_definition ''OclValid'')]
               ,Tac_subst (Thm_str ''cp_defined'')]]
          (Tacl_by [Tac_auto_simp_add_split ( Thm_symmetric (Thm_str ''cp_defined'')
                                            # List_map Thm_str ( hol_definition ''bot_option''
                                                          # [ flatten [isub_name const_oclistypeof, ''_'', h_name] ]))
                                            (''option.split'' # split_ty h_name) ]) )
        l_hierarchy))"

definition "print_istypeof_defined'_name isub_name h_name = flatten [isub_name const_oclistypeof, ''_'', h_name, ''_defined'',  [Char Nibble2 Nibble7]]"
definition "print_istypeof_defined' = start_map Thy_lemma_by o flatten o map_class_h (\<lambda>isub_name name l_hierarchy.
     (let var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply unicode_delta [e]) in
      List_map (\<lambda>h_name.
        Lemma_by_assum
          (print_istypeof_defined'_name isub_name h_name)
          [(var_isdef, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_istypeof name])))
          []
          (Tacl_by [Tac_rule (Thm_OF (Thm_str (print_istypeof_defined_name isub_name h_name))
                                     (Thm_THEN (Thm_str var_isdef) (Thm_str ''foundation20'')))]) )
        l_hierarchy))"

definition "print_istypeof_up_larger_name name_pers name_any = flatten [''actualType'', isub_of_str name_pers, ''_larger_staticType'', isub_of_str name_any]"
definition "print_istypeof_up_larger = start_map Thy_lemma_by o
  map_class_nupl2' (\<lambda>name_pers name_any.
    let var_X = ''X''
      ; var_isdef = ''isdef''
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (print_istypeof_up_larger_name name_pers name_any)
        [(var_isdef, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_binop (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_pers)
               (Expr_basic [dot_istypeof name_any]))
             ) unicode_triangleq (Expr_basic [''false''])))
        [App_using [Thm_str var_isdef]]
        (Tacl_by [Tac_auto_simp_add ( flatten [const_oclistypeof, isub_of_str name_any, ''_'', name_pers]
                                    # ''foundation22''
                                    # ''foundation16''
                                    # List_map hol_definition [''null_option'', ''bot_option'' ])]))"

definition "print_istypeof_up_d_cast_name name_mid name_any name_pers = flatten [''down_cast_type'', isub_of_str name_mid, ''_from_'', name_any, ''_to_'', name_pers]"
definition "print_istypeof_up_d_cast expr = (start_map Thy_lemma_by o
  map_class_nupl3'_GE (\<lambda>name_pers name_mid name_any.
    let var_X = ''X''
      ; var_istyp = ''istyp''
      ; var_isdef = ''isdef''
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (print_istypeof_up_d_cast_name name_mid name_any name_pers)
        [(var_istyp, f (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_any)
               (Expr_basic [dot_istypeof name_mid]))))
        ,(var_isdef, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_binop (Expr_warning_parenthesis (Expr_postunary
               (Expr_basic [var_X])
               (Expr_basic [dot_astype name_pers]))
             ) unicode_triangleq (Expr_basic [''invalid''])))
        [App_using (map Thm_str [var_istyp, var_isdef])
        ,App [Tac_auto_simp_add_split (map Thm_str
                                      ( flatten [const_oclastype, isub_of_str name_pers, ''_'', name_any]
                                      # ''foundation22''
                                      # ''foundation16''
                                      # List_map hol_definition [''null_option'', ''bot_option'' ]))
                                      (split_ty name_any) ]]
        (Tacl_by [Tac_simp_add (let l = List_map hol_definition [''OclValid'', ''false'', ''true''] in
                                if name_mid = name_any & ~(print_istypeof_lemma_cp_set expr = []) then
                                  l
                                else
                                  flatten [const_oclistypeof, isub_of_str name_mid, ''_'', name_any] # l)]))) expr"

subsection{* IsKindOf *}

definition "print_iskindof_consts = start_map Thy_consts_class o
  map_class (\<lambda>isub_name name _ _ _ _.
    Consts (isub_name const_ocliskindof) (Ty_base ty_boolean) (const_mixfix dot_ocliskindof name))"

definition "print_iskindof_class_name isub_name h_name = flatten [isub_name const_ocliskindof, ''_'', h_name]"
definition "print_iskindof_class = start_map Thy_defs_overloaded o map_class_gen_h''''
  (\<lambda>isub_name name l_hierarchy l_attr l_inherited l_cons. List_map (\<lambda> (h_name, _).
    Defs_overloaded
          (print_iskindof_class_name isub_name h_name)
          (let var_x = ''x'' in
           Expr_rewrite
             (Expr_postunary (Expr_annot (Expr_basic [var_x]) h_name) (Expr_basic [dot_iskindof name]))
             unicode_equiv
             (let isof = (\<lambda>f name. Expr_warning_parenthesis (Expr_postunary (Expr_basic [var_x]) (Expr_basic [f name]))) in
              case l_cons of [] \<Rightarrow> isof dot_istypeof name
                           | name_past # _ \<Rightarrow> Expr_binop (isof dot_istypeof name) ''or'' (isof dot_iskindof name_past))))
     l_hierarchy)"

definition "print_iskindof_from_universe = start_map Thy_definition_hol o
  map_class_h (\<lambda>isub_name name l_hierarchy.
    let const_iskindof = flatten [const_ocliskindof, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [const_iskindof]) ''=''
   (
   (Expr_function (List_map (\<lambda>h_name.
     let isub_h = (\<lambda> s. s @@ isub_of_str h_name) in
     ( Expr_apply (isub_h datatype_in) [Expr_basic [h_name]]
     , Expr_warning_parenthesis
       (Expr_postunary (Expr_annot (Expr_applys (bug_ocaml_extraction (let var_x = ''x'' in
                                                      Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))) [Expr_basic [h_name]])
                                   h_name)
                       (Expr_basic [dot_iskindof name])))) l_hierarchy)))))"

definition "print_iskindof_lemma_cp_set =
  (if activate_simp_optimization then
    map_class (\<lambda>isub_name name _ _ _ _. ((isub_name, name), name))
   else (\<lambda>_. []))"

definition "print_iskindof_lemmas_id = start_map' (\<lambda>expr.
  (let name_set = print_iskindof_lemma_cp_set expr in
   case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
  [ Lemmas_simp '''' (List_map (\<lambda>((isub_name, _), name).
    Thm_str (flatten [isub_name const_ocliskindof, ''_'', name] )) name_set) ]))"

definition "print_iskindof_lemma_cp expr = (start_map Thy_lemma_by o
  get_hierarchy_fold (\<lambda> (name1_previous, name1) name2 name3.
    let lemma_name = flatten [''cp_'', const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2]
      ; lemma_spec = let var_p = ''p''; var_x = ''x'' in
       List_map
         (\<lambda>x. Expr_apply ''cp'' [x])
         [ Expr_basic [var_p]
         , Expr_lambda var_x
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_apply var_p [Expr_annot (Expr_basic [var_x]) name3]) name2)
               (Expr_basic [dot_iskindof name1])))]
      ; lem_simp1 = Tac_simp_only [Thm_str (flatten [const_ocliskindof, isub_of_str name1, ''_'', name2])]
      ; lem_simp2 = Tac_simp_only [Thm_str (flatten [''cp_'', const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2])] in
    let (tac1, tac2) = case name1_previous
    of None \<Rightarrow> ([], Tacl_by [ lem_simp1 , lem_simp2 ])
     | Some name1_previous \<Rightarrow>
      ( [ [ lem_simp1 ]
        , [ Tac_rule (Thm_where (Thm_str ''cpI2'') [(''f'', Expr_preunary (Expr_basic [''op'']) (Expr_basic [''or'']))])
          , Tac_plus [Tac_rule (Thm_str ''allI'')]
          , Tac_rule (Thm_str ''cp_OclOr'') ] ]
      , Tacl_by [ lem_simp2 , Tac_simp_only [Thm_str (flatten [''cp_'', const_ocliskindof, isub_of_str name1_previous, ''_'', name3, ''_'', name2])] ])
    in Lemma_by lemma_name lemma_spec tac1 tac2
  ) (\<lambda>x. let rev_x = rev x in (rev_x, rev_x, x))) expr"

definition "print_iskindof_lemmas_cp = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
    (\<lambda>expr. [Lemmas_simp ''''
  (get_hierarchy_map (\<lambda>name1 name2 name3.
      Thm_str (flatten [''cp_'', const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2])
  ) (\<lambda>x. (x, x, x)) expr)])
  else (\<lambda>_. []))"

definition "print_iskindof_lemma_strict expr = (start_map Thy_lemma_by o
  get_hierarchy_fold (\<lambda> (name1_previous, name1) (name2,name2') name3.
    Lemma_by
      (flatten [const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2])
      [ Expr_rewrite
             (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [name2]) name3)
               (Expr_basic [dot_iskindof name1])))
             ''=''
             (Expr_basic [name2'])]
      []
      (Tacl_by
        (Tac_simp_only
           (map Thm_str (flatten
              [ [flatten [const_ocliskindof, isub_of_str name1, ''_'', name3]]
              , [flatten [const_oclistypeof, isub_of_str name1, ''_'', name3, ''_'', name2]]
              , case name1_previous
                of None \<Rightarrow> []
                 | Some name1_previous \<Rightarrow> [flatten [const_ocliskindof, isub_of_str name1_previous, ''_'', name3, ''_'', name2]] ]))
        # (if name1_previous = None then [] else [Tac_simp])) )
  ) (\<lambda>x. (rev x, [(''invalid'',''invalid''),(''null'',''true'')], x))) expr"

definition "print_iskindof_lemmas_strict = start_map'
 (if activate_simp_optimization then List_map Thy_lemmas_simp o
  (\<lambda>expr. [ Lemmas_simp '''' (get_hierarchy_map (\<lambda>name1 name2 name3.
      Thm_str (flatten [const_ocliskindof, isub_of_str name1, ''_'', name3, ''_'', name2])
  ) (\<lambda>x. (x, [''invalid'',''null''], x)) expr)])
  else (\<lambda>_. []))"

definition "print_iskindof_defined_name isub_name h_name = flatten [isub_name const_ocliskindof, ''_'', h_name, ''_defined'']"
definition "print_iskindof_defined = start_map Thy_lemma_by o flatten o map_class_h'''' (\<lambda>isub_name name l_hierarchy _ _ l_cons.
     (let var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>symb e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply symb [e]) in
      List_map (\<lambda>h_name.
        Lemma_by_assum
          (print_iskindof_defined_name isub_name h_name)
          [(var_isdef, f unicode_upsilon (Expr_basic [var_X]))]
          (f unicode_delta (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_iskindof name])))
          []
          (Tacl_by [ Tac_simp_only [Thm_str (flatten [isub_name const_ocliskindof, ''_'', h_name])]
                   , Tac_rule
                      (let mk_OF = \<lambda>f. Thm_OF (Thm_str (f h_name)) (Thm_str var_isdef) in
                       case l_cons of
                         n # _ \<Rightarrow>
                             thm_OF
                               (Thm_str ''defined_or_I'')
                               (List_map mk_OF
                                  [ print_istypeof_defined_name isub_name
                                  , print_iskindof_defined_name (\<lambda>name. name @@ isub_of_str n)])
                       | [] \<Rightarrow> mk_OF (print_istypeof_defined_name isub_name)) ]))
        (List_map fst l_hierarchy)))"

definition "print_iskindof_defined'_name isub_name h_name = flatten [isub_name const_ocliskindof, ''_'', h_name, ''_defined'', [Char Nibble2 Nibble7]]"
definition "print_iskindof_defined' = start_map Thy_lemma_by o flatten o map_class_h'''' (\<lambda>isub_name name l_hierarchy _ _ l_cons.
     (let var_X = ''X''
        ; var_isdef = ''isdef''
        ; f = \<lambda>e. Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile (Expr_apply unicode_delta [e]) in
      List_map (\<lambda>h_name.
        Lemma_by_assum
          (print_iskindof_defined'_name isub_name h_name)
          [(var_isdef, f (Expr_basic [var_X]))]
          (f (Expr_postunary (Expr_annot (Expr_basic [var_X]) h_name) (Expr_basic [dot_iskindof name])))
          []
          (Tacl_by [Tac_rule (Thm_OF (Thm_str (print_iskindof_defined_name isub_name h_name))
                                     (Thm_THEN (Thm_str var_isdef) (Thm_str ''foundation20'')))]) )
        (List_map fst l_hierarchy)))"

definition "print_iskindof_up_eq_asty_name name = (flatten [''actual_eq_static'', isub_of_str name])"
definition "print_iskindof_up_eq_asty = start_map Thy_lemma_by o map_class_gen_h''''
  (\<lambda> isub_name name _ _ _ l_cons.
    let var_X = ''X''
      ; var_isdef = ''isdef''
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    [Lemma_by_assum
        (print_iskindof_up_eq_asty_name name)
        [(var_isdef, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name)
               (Expr_basic [dot_iskindof name]))))
        [App [Tac_simp_only (map Thm_str [flatten [const_ocliskindof, isub_of_str name, ''_'', name], hol_definition ''OclValid''])
             ,Tac_insert [Thm_str var_isdef]]]
        (Tacl_by (let l = let l =
                           [Tac_auto_simp_add_split (bug_ocaml_extraction (let l =
                                                      List_map Thm_str (flatten ([''foundation16'', hol_definition ''bot_option'']
                                                    # List_map (\<lambda>n. flatten [const_ocliskindof, isub_of_str n, ''_'', name]
                                                             # flatten [const_oclistypeof, isub_of_str n, ''_'', name]
                                                             # []) l_cons)) in
                                                     if l_cons = [] then l else Thm_symmetric (Thm_str ''cp_OclOr'') # l))
                                                    (''option.split'' # flatten (split_ty name # List_map split_ty l_cons))] in
                            if l_cons = [] then l else Tac_subst (Thm_str ''cp_OclOr'') # l in
                  if l_cons = [] (* FIXME remove this condition if possible *) then l else [Tac_plus l]))])"

definition "print_iskindof_up_larger_name name_pers name_any = flatten [''actualKind'', isub_of_str name_pers, ''_larger_staticKind'', isub_of_str name_any]"
definition "print_iskindof_up_larger = start_map Thy_lemma_by o
  map_class_nupl2'' (\<lambda>name_pers name_any name_pred.
    let var_X = ''X''
      ; var_isdef = ''isdef''
      ; f = Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (print_iskindof_up_larger_name name_pers name_any)
        [(var_isdef, f (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_pers)
               (Expr_basic [dot_iskindof name_any]))))
        (map (\<lambda>s. App [s]) [ Tac_simp_only [Thm_str (flatten [const_ocliskindof, isub_of_str name_any, ''_'', name_pers])]
                           , Tac_insert (map (\<lambda>s. Thm_OF (Thm_str s) (Thm_str var_isdef))
                                           [ case name_pred of None => print_iskindof_up_eq_asty_name name_pers
                                                             | Some name_pred => print_iskindof_up_larger_name name_pers name_pred
                                           , print_istypeof_up_larger_name name_pers name_any])
                           , Tac_rule (Thm_THEN (Thm_str ''foundation11'') (Thm_str ''iffD2''))])
        (Tacl_by [Tac_plus [Tac_simp_add [''OclNot_defargs'', ''foundation6'', ''foundation14'']]]))"

definition "print_iskindof_up_istypeof_name name_pers name_any = flatten [''not_'', const_ocliskindof, isub_of_str name_pers, ''_then_'', name_any, ''_'', const_oclistypeof, ''_others'']"
definition "print_iskindof_up_istypeof = start_map Thy_lemma_by o
  map_class_nupl2l' (\<lambda>name_pers name_any name_pred.
    let var_X = ''X''
      ; var_iskin = ''iskin''
      ; var_isdef = ''isdef''
      ; f = \<lambda>f. f o Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (print_iskindof_up_istypeof_name name_pers name_any)
        [(var_iskin, f (Expr_preunary (Expr_basic [unicode_not])) (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_any)
               (Expr_basic [dot_iskindof name_pers]))))
        ,(var_isdef, f id (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (expr_binop unicode_or (map (\<lambda>name_pred. f id (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_any)
               (Expr_basic [dot_istypeof name_pred])))) (name_any # name_pred)))
        (bug_ocaml_extraction (let f_app = \<lambda>name_pred name_pred_pred.
            App [Tac_simp_only [Thm_str (print_iskindof_class_name (\<lambda>s. s @@ isub_of_str name_pred) name_any)
                               ,thm_OF (Thm_str ''foundation11'')
                                       (List_map (\<lambda>(pr, n). Thm_OF (Thm_str (pr (\<lambda>name. name @@ isub_of_str n) name_any)) (Thm_str var_isdef))
                                          [ (print_istypeof_defined'_name, name_pred)
                                          , (print_iskindof_defined'_name, name_pred_pred)])]] in
            App_using [Thm_OF (Thm_str (print_iskindof_up_eq_asty_name name_any)) (Thm_str var_isdef)]
          # f_app name_any (case name_pred of name_pers # _ \<Rightarrow> name_pers | [] \<Rightarrow> name_pers)
          # flatten (let map_pred = \<lambda>f l init. let (l, _) = fold (\<lambda> x (acc, pred). (f x pred # acc, x)) (rev l) ([], init) in l in
                     map_pred (\<lambda>name_pred name_pred_pred.
                       [App [Tac_erule (Thm_str ''disjE''), Tac_simp, Tac_rule (Thm_str ''disjI2'')]
                       ,f_app name_pred name_pred_pred ]) name_pred name_pers)))
        (Tacl_by [Tac_simp_add [var_iskin]]))"

definition "print_iskindof_up_d_cast expr = (start_map Thy_lemma_by o
  map_class_nupl3'_LE' (\<lambda>name_pers name_mid name_any name_pred.
    let var_X = ''X''
      ; var_iskin = ''iskin''
      ; var_isdef = ''isdef''
      ; f = \<lambda>f. f o Expr_binop (Expr_basic [unicode_tau]) unicode_Turnstile in
    Lemma_by_assum
        (flatten [''down_cast_kind'', isub_of_str name_mid, ''_from_'', name_any, ''_to_'', name_pers])
        [(var_iskin, f (Expr_preunary (Expr_basic [unicode_not])) (Expr_warning_parenthesis (Expr_postunary
               (Expr_annot (Expr_basic [var_X]) name_any)
               (Expr_basic [dot_iskindof name_mid]))))
        ,(var_isdef, f id (Expr_apply unicode_delta [Expr_basic [var_X]]))]
        (f id (Expr_binop (Expr_warning_parenthesis (Expr_postunary
               (Expr_basic [var_X])
               (Expr_basic [dot_astype name_pers]))
             ) unicode_triangleq (Expr_basic [''invalid''])))
        (map App
          ( let f = \<lambda>name_pred. [Tac_rule (Thm_str (print_istypeof_up_d_cast_name name_pred name_any name_pers))
                                ,Tac_simp_only [] (* FIXME use wildcard *)
                                ,Tac_simp_only [Thm_str var_isdef]] in
            ( Tac_insert [thm_OF (Thm_str (print_iskindof_up_istypeof_name name_mid name_any)) (map Thm_str [var_iskin, var_isdef])]
            # (case name_pred of [] \<Rightarrow> [] | _ \<Rightarrow> [ Tac_elim (Thm_str ''disjE'') ]))
          # List_map f (name_any # name_pred)))
        Tacl_done)) expr"

subsection{* allInstances *}

definition "print_allinst_def_id = start_map Thy_definition_hol o
  map_class_h (\<lambda>isub_name name l_hierarchy.
    let const_astype = flatten [const_oclastype, isub_of_str name, ''_'', unicode_AA] in
    Definition (Expr_rewrite (Expr_basic [name]) ''='' (Expr_basic [const_astype])))"

definition "print_allinst_lemmas_id = start_map'
  (if activate_simp_optimization then
     \<lambda>expr.
       let name_set = map_class (\<lambda>_ name _ _ _ _. name) expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
         [ Lemmas_simp '''' (List_map (Thm_str o hol_definition) name_set) ]
  else (\<lambda>_. []))"

subsection{* accessors *}

definition "print_access_oid_uniq_name isub_name attr = isub_name var_oid_uniq @@ isup_of_str attr"
definition "print_access_oid_uniq =
  (\<lambda>expr ocl. case ocl of OclDeepEmbed disable_thy_output file_out_path_dep oid_start output_position design_analysis () \<Rightarrow>
    if design_analysis = None then ([], ocl) else
      (\<lambda>(l, oid_start). (List_map Thy_definition_hol l, OclDeepEmbed disable_thy_output file_out_path_dep oid_start output_position design_analysis ()))
      (let (l, acc) = fold_class (\<lambda>isub_name name l_attr l_inh _ _ cpt.
         let l_inh = List_map snd l_inh in
         let (l, cpt) = fold_list (fold_list
           (\<lambda> (attr, OclTy_object _) \<Rightarrow> \<lambda>cpt.
             ([Definition (Expr_rewrite
                   (Expr_basic [print_access_oid_uniq_name isub_name attr])
                   ''=''
                   (Expr_oid '''' (oidGetAssoc cpt)))], oidSucAssoc cpt)
            | _ \<Rightarrow> \<lambda>cpt. ([], cpt)))
           (l_attr # l_inh) cpt in
         (flatten (flatten l), cpt)) oid_start expr in
       (flatten l, acc)))"

definition "print_access_eval_extract _ = start_map Thy_definition_hol
  (let lets = \<lambda>var def. Definition (Expr_rewrite (Expr_basic [var]) ''='' (Expr_basic [def])) in
  [ bug_ocaml_extraction
    (let var_x = ''x''
      ; var_f = ''f''
      ; var_tau = unicode_tau
      ; some_some = (\<lambda>x. Expr_some (Expr_some x))
      ; var_obj = ''obj'' in
    Definition (Expr_rewrite
                  (Expr_basic [var_eval_extract, var_x, var_f])
                  ''=''
                  (Expr_lambda
                     var_tau
                     (Expr_case (Expr_basic [var_x, var_tau])
                     [ (some_some (Expr_basic [var_obj]), Expr_apply var_f [Expr_apply ''oid_of'' [Expr_basic [var_obj]], Expr_basic [var_tau]])
                     , (Expr_basic [wildcard], Expr_basic [''invalid'', var_tau])]))))
  , lets var_in_pre_state ''fst''
  , lets var_in_post_state ''snd''
  , lets var_reconst_basetype ''id'' ])"

definition "print_access_choose = start_map'''' Thy_definition_hol o (\<lambda>expr design_analysis.
  (let lets = \<lambda>var def. Definition (Expr_rewrite (Expr_basic [var]) ''='' (Expr_basic [def]))
     ; lets' = \<lambda>var exp. Definition (Expr_rewrite (Expr_basic [var]) ''='' exp) in
  if design_analysis = None then \<lambda>_. [] else
  if design_analysis = Some 1 then (\<lambda>_.
  let mk_n = \<lambda>s. s @@ isub_of_str ''2'' in
  ( lets (flatten [mk_n var_choose, ''_1'']) ''fst''
  # lets (flatten [mk_n var_choose, ''_2'']) ''snd''
  # lets' (flatten [mk_n var_switch, ''_1'']) (Expr_basic [''id''])
  # lets' (flatten [mk_n var_switch, ''_2'']) (let cpl = \<lambda>x y. Expr_parenthesis (Expr_binop (Expr_basic [x]) '','' (Expr_basic [y]))
                                                 ; var_x = ''x''
                                                 ; var_y = ''y'' in
                                               Expr_lambdas0 (cpl var_x var_y) (cpl var_y var_x))
  # [ let var_pre_post = ''pre_post''
        ; var_to_from = ''to_from''
        ; var_assoc_oid = ''assoc_oid''
        ; var_f = ''f''
        ; var_oid = ''oid''
        ; var_tau = unicode_tau in
      Definition (Expr_rewrite
        (Expr_basic [mk_n var_deref_assocs, var_pre_post, var_to_from, var_assoc_oid, var_f, var_oid ])
        ''=''
        (Expr_lambda var_tau (Expr_case (Expr_apply (mk_n var_assocs) [Expr_apply var_pre_post [Expr_basic [var_tau]]
                                                                      ,Expr_basic [var_assoc_oid]])
                                        [ bug_ocaml_extraction (let var_S = ''S'' in
                                          ( Expr_some (Expr_basic [var_S])
                                          , Expr_apply var_f
                                              [ Expr_apply ''map''
                                                 [ Expr_binop
                                                     (Expr_basic [flatten [mk_n var_choose, ''_2'']])
                                                     unicode_circ
                                                     (Expr_basic [var_to_from])
                                                 , Expr_apply ''filter'' [ bug_ocaml_extraction (let var_p = ''p'' in Expr_lambda var_p (Expr_rewrite (Expr_applys (Expr_basic [flatten [mk_n var_choose, ''_1'']]) [Expr_apply var_to_from [Expr_basic [var_p]]]) ''='' (Expr_basic [var_oid])))
                                                                         , Expr_basic [var_S]]]
                                              , Expr_basic [var_oid]
                                              , Expr_basic [var_tau]]))
                                        , ( Expr_basic[wildcard], Expr_apply ''invalid'' [Expr_basic [var_tau]]) ]))) ] )) else (\<lambda>_. []) (* TO DO *)) expr)"

definition "print_access_deref_oid = start_map Thy_definition_hol o
  map_class (\<lambda>isub_name _ _ _ _ _.
    let var_fs = ''fst_snd''
      ; var_f = ''f''
      ; var_oid = ''oid''
      ; var_obj = ''obj''
      ; var_tau = unicode_tau in
    Definition (Expr_rewrite
                  (Expr_basic [isub_name var_deref_oid, var_fs, var_f, var_oid])
                  ''=''
                  (Expr_lambda
                     var_tau
                     (Expr_case (Expr_apply ''heap'' [Expr_basic [var_fs, var_tau], Expr_basic [var_oid]])
                     [ (Expr_some (Expr_basic [isub_name datatype_in, var_obj]), Expr_basic [var_f, var_obj, var_tau])
                     , (Expr_basic [wildcard], Expr_basic [''invalid'', var_tau]) ]))))"

definition "print_access_deref_assocs_name isub_name = flatten [var_deref, ''_'', isub_name var_assocs]"
definition "print_access_deref_assocs = start_map'''' Thy_definition_hol o (\<lambda>expr design_analysis. 
  (if design_analysis = None then \<lambda>_. [] else (\<lambda>expr. flatten (flatten (map_class (\<lambda>isub_name name l_attr l_inherited _ _.
  let l_inherited = List_map snd l_inherited in
  let mk_n = \<lambda>s. s @@ isub_of_str ''2''
    ; var_fst_snd = ''fst_snd''
    ; var_f = ''f''
    ; b = \<lambda>s. Expr_basic [s] in
    flatten (List_map (List_map
      (\<lambda> (attr, OclTy_object _) \<Rightarrow>
           [Definition (Expr_rewrite
                  (Expr_basic [(print_access_deref_assocs_name isub_name @@ isup_of_str attr), var_fst_snd, var_f])
                  ''=''
                  (Expr_binop
                    (Expr_apply
                      (mk_n var_deref_assocs)
                        (map b [ var_fst_snd
                               , flatten [mk_n var_switch, ''_1'']
                               , print_access_oid_uniq_name isub_name attr
                               , var_f ]))
                    unicode_circ
                    (b ''oid_of'')))]
       | _ \<Rightarrow> []))
      (l_attr # l_inherited))) expr)))) expr)"

definition "print_access_select_object = start_map'''' Thy_definition_hol o (\<lambda>expr design_analysis. 
  (if design_analysis = None then \<lambda>_. [] else (\<lambda>_. [
   (let var_mt = ''mt''
      ; var_incl = ''incl''
      ; var_smash = ''smash''
      ; var_deref = ''deref''
      ; var_l = ''l''
      ; var_oid = ''oid''
      ; b = \<lambda>s. Expr_basic [s] in
    Definition (Expr_rewrite
                  (Expr_basic [var_select_object, var_mt, var_incl, var_smash, var_deref, var_l, var_oid])
                  ''=''
                  (Expr_apply var_smash
                     [ Expr_apply ''foldl''
                         [ b var_incl
                         , b var_mt
                         , Expr_apply ''map''
                             [ b var_deref
                             , b var_l ] ]]))) ])) expr)"

definition "print_access_select = start_map'' Thy_definition_hol o (\<lambda>expr base_attr _ base_attr''.
  map_class_arg_only0 (\<lambda>isub_name name l_attr.
    let l_attr = base_attr l_attr in
    let var_f = ''f''
      ; wildc = Expr_basic [wildcard] in
    let (_, _, l) = (foldl
      (\<lambda>(l_wildl, l_wildr, l_acc) (attr, _).
        let isup_attr = (\<lambda>s. s @@ isup_of_str attr) in
        ( wildc # l_wildl
        , tl l_wildr
        , Definition (Expr_rewrite
                       (Expr_basic [isup_attr (isub_name var_select), var_f])
                       ''=''
                       (let var_attr = attr in
                        Expr_function
                          (List_map (\<lambda>(lhs,rhs). ( Expr_apply
                                                         (isub_name datatype_constr_name)
                                                         ( wildc
                                                         # flatten [l_wildl, [lhs], l_wildr])
                                                     , rhs))
                            [ ( Expr_basic [unicode_bottom], Expr_basic [''null''] )
                            , ( Expr_some (Expr_basic [var_attr])
                              , Expr_apply var_f [ bug_ocaml_extraction
                                                   (let var_x = ''x'' in
                                                      Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))
                                                 , Expr_basic [var_attr]]) ]))) # l_acc))
      ([], List_map (\<lambda>_. wildc) (tl l_attr), [])
      l_attr) in
    rev l)
  (\<lambda>isub_name name (l_attr, l_inherited, l_cons).
    let l_inherited = flatten (List_map snd l_inherited) in
    let (l_attr, l_inherited) = base_attr'' (l_attr, l_inherited) in
    let var_f = ''f''
      ; wildc = Expr_basic [wildcard] in
    let (_, _, l) = (foldl
      (\<lambda>(l_wildl, l_wildr, l_acc) (attr, _).
        let isup_attr = (\<lambda>s. s @@ isup_of_str attr) in
        ( wildc # l_wildl
        , tl l_wildr
        , Definition (Expr_rewrite
                       (Expr_basic [isup_attr (isub_name var_select), var_f])
                       ''=''
                       (let var_attr = attr in
                        Expr_function
                          (flatten (List_map (\<lambda>(lhs,rhs). ( Expr_apply
                                                         (isub_name datatype_constr_name)
                                                         ( Expr_apply (isub_name datatype_ext_constr_name)
                                                             (wildc # flatten [l_wildl, [lhs], l_wildr])
                                                         # List_map (\<lambda>_. wildc) l_attr)
                                                     , rhs))
                            [ ( Expr_basic [unicode_bottom], Expr_basic [''null''] )
                            , ( Expr_some (Expr_basic [var_attr])
                              , Expr_apply var_f [ bug_ocaml_extraction
                                                   (let var_x = ''x'' in
                                                      Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x]))))
                                                 , Expr_basic [var_attr]]) ]
                            # (List_map (\<lambda>x. let var_x = lowercase_of_str x in
                                             (Expr_apply
                                                         (isub_name datatype_constr_name)
                                                         ( Expr_apply (datatype_ext_constr_name @@ mk_constr_name name x)
                                                             [Expr_basic [var_x]]
                                                         # List_map (\<lambda>_. wildc) l_attr), (Expr_apply (isup_attr (var_select @@ isub_of_str x))
                                                                                                     (List_map (\<lambda>x. Expr_basic [x]) [var_f, var_x]) ))) l_cons)
                            # [])))) # l_acc))
      ([], List_map (\<lambda>_. wildc) (tl l_inherited), [])
      l_inherited) in
    rev l) expr)"

definition "print_access_select_obj = start_map'''' Thy_definition_hol o (\<lambda>expr design_analysis. 
  (if design_analysis = None then \<lambda>_. [] else (\<lambda>expr. flatten (flatten (map_class (\<lambda>isub_name name l_attr l_inh _ _.
    let l_inh = List_map snd l_inh in
    flatten (List_map (List_map
      (\<lambda> (attr, OclTy_object _) \<Rightarrow>
           [Definition (let var_f = ''f''
                          ; b = \<lambda>s. Expr_basic [s] in
              Expr_rewrite
                  (Expr_basic [isub_name var_select @@ isup_of_str attr, var_f])
                  ''=''
                  (Expr_apply var_select_object [b ''mtSet'', b ''OclIncluding'', b ''OclANY'', Expr_apply var_f [let var_x = ''x'' in
                                                      Expr_lambdas [var_x, wildcard] (Expr_some (Expr_some (Expr_basic [var_x])))]]))]
       | _ \<Rightarrow> []))
      (l_attr # l_inh))) expr)))) expr)"

definition "print_access_dot_consts = start_map Thy_consts_class o
  flatten o flatten o map_class (\<lambda>isub_name name l_attr _ _ _.
    List_map (\<lambda>(attr_n, attr_ty).
      List_map
        (\<lambda>(var_at_when_hol, var_at_when_ocl).
          Consts_raw
            (flatten [''dot'', isup_of_str attr_n, var_at_when_hol])
            (Ty_apply (Ty_base ''val'') [Ty_base unicode_AA, Ty_base (Char Nibble2 Nibble7 # unicode_alpha)])
            (case attr_ty of
                OclTy_base attr_ty \<Rightarrow> Ty_apply (Ty_base ''val'') [Ty_base unicode_AA,
                  let option = \<lambda>x. Ty_apply (Ty_base ''option'') [x] in
                  option (option (Ty_base attr_ty))]
              | OclTy_object _ \<Rightarrow> Ty_base name)
            (mk_dot attr_n var_at_when_ocl))
        [ (var_at_when_hol_post, var_at_when_ocl_post)
        , (var_at_when_hol_pre, var_at_when_ocl_pre)]) l_attr)"

definition "print_access_dot = start_map'''' Thy_defs_overloaded o (\<lambda>expr design_analysis. 
  map_class_arg_only_var'
    (\<lambda>isub_name name (var_in_when_state, dot_at_when) attr_orig attr_ty isup_attr dot_attr.
            [ Defs_overloaded
                (flatten [isup_attr (isub_name ''dot''), dot_at_when])
                (let var_x = ''x'' in
                 Expr_rewrite
                   (dot_attr (Expr_annot (Expr_basic [var_x]) name))
                   unicode_equiv
                   (Expr_apply var_eval_extract [Expr_basic [var_x],
                    let deref_oid = \<lambda>attr_orig l. Expr_apply (case attr_orig of None \<Rightarrow> isub_name var_deref_oid
                                                                              | Some orig_n \<Rightarrow> var_deref_oid @@ isub_of_str orig_n) (Expr_basic [var_in_when_state] # l) in
                    deref_oid None [ (case (design_analysis, attr_ty) of
                                   (Some _, OclTy_object _) \<Rightarrow>
                                     \<lambda>l. Expr_apply (isup_attr (print_access_deref_assocs_name isub_name)) (Expr_basic [var_in_when_state] # [l])
                                 | _ \<Rightarrow> id) (Expr_apply (isup_attr (isub_name var_select))
                          [case attr_ty of OclTy_base _ \<Rightarrow> Expr_basic [var_reconst_basetype]
                                         | OclTy_object _ \<Rightarrow> deref_oid attr_orig [] ]) ] ])) ]) expr)"

definition "print_access_dot_lemmas_id_set =
  (if activate_simp_optimization then
     map_class_arg_only_var'
       (\<lambda>isub_name _ (_, dot_at_when) _ _ isup_attr _. [flatten [isup_attr (isub_name ''dot''), dot_at_when]])
   else (\<lambda>_. []))"

definition "print_access_dot_lemmas_id = start_map' (\<lambda>expr.
       (let name_set = print_access_dot_lemmas_id_set expr in
       case name_set of [] \<Rightarrow> [] | _ \<Rightarrow> List_map Thy_lemmas_simp
         [ Lemmas_simp '''' (List_map Thm_str name_set) ]))"

definition "print_access_dot_cp_lemmas_set =
  (if activate_simp_optimization then [hol_definition var_eval_extract] else [])"

definition "print_access_dot_cp_lemmas = start_map' (\<lambda>_.
  List_map (\<lambda>x. Thy_lemmas_simp (Lemmas_simp '''' [Thm_str x])) print_access_dot_cp_lemmas_set)"

definition "print_access_dot_lemma_cp = start_map Thy_lemma_by o
  map_class_arg_only_var
    (\<lambda>isub_name name (_, dot_at_when) _ _ isup_attr dot_attr.
            [ Lemma_by
                (flatten [''cp_'', isup_attr (isub_name ''dot''), dot_at_when])
                (bug_ocaml_extraction
                (let var_x = ''X'' in
                 [Expr_apply ''cp'' [Expr_lambda var_x (dot_attr (Expr_annot (Expr_basic [var_x]) name)) ]]))
                []
                (Tacl_by [if print_access_dot_cp_lemmas_set = [] then
                            Tac_auto_simp_add (map hol_definition [''cp'', var_eval_extract, flatten [isup_attr (isub_name ''dot''), dot_at_when]])
                          else
                            Tac_auto_simp_add (map hol_definition [''cp''])]) ])
    (\<lambda>isub_name name (_, dot_at_when) _ _ isup_attr dot_attr.
            [ Lemma_by
                (flatten [''cp_'', isup_attr (isub_name ''dot''), dot_at_when])
                (bug_ocaml_extraction
                (let var_x = ''X'' in
                 [Expr_apply ''cp'' [Expr_lambda var_x (dot_attr (Expr_annot (Expr_basic [var_x]) name)) ]]))
                []
                (if print_access_dot_cp_lemmas_set = [] then Tacl_sorry (* fold l_hierarchy, take only subclass, unfold the corresponding definition *)
                 else Tacl_by [Tac_auto_simp_add (map hol_definition [''cp''])]) ])"

definition "print_access_dot_lemmas_cp = start_map Thy_lemmas_simp o (\<lambda>expr. [Lemmas_simp ''''
  (map_class_arg_only_var'
    (\<lambda>isub_name _ (_, dot_at_when) _ _ isup_attr _.
      [Thm_str (flatten [''cp_'', isup_attr (isub_name ''dot''), dot_at_when]) ])
    expr)])"

definition "print_access_lemma_strict expr = (start_map Thy_lemma_by o
  map_class_arg_only_var' (\<lambda>isub_name name (_, dot_at_when) _ _ isup_attr dot_attr.
            List_map (\<lambda>(name_invalid, tac_invalid). Lemma_by
                  (flatten [isup_attr (isub_name ''dot''), dot_at_when, ''_'', name_invalid])
                  [Expr_rewrite
                     (dot_attr (Expr_annot (Expr_basic [name_invalid]) name))
                     ''=''
                     (Expr_basic [''invalid''])]
                  []
                  (if print_access_dot_lemmas_id_set expr = [] | print_access_dot_cp_lemmas_set = [] then
                     Tacl_sorry else
                   Tacl_by [ Tac_rule (Thm_str ''ext''),
                             Tac_simp_add (map hol_definition
                                             (let l = (let l = (''bot_option'' # tac_invalid) in
                                              if print_access_dot_lemmas_id_set expr = [] then
                                                flatten [isup_attr (isub_name ''dot''), dot_at_when] # l
                                              else l) in
                                              if print_access_dot_cp_lemmas_set = []
                                              then
                                                ''eval_extract'' # l
                                              else l))]) )
                [(''invalid'', [''invalid'']), (''null'', [''null_fun'', ''null_option''])])) expr"

subsection{* example *}

definition "print_examp_oclint = (\<lambda> OclDefI l \<Rightarrow> (start_map Thy_definition_hol o
  List_map (\<lambda>nb.
    let name = var_OclInt @@ nb
      ; b = \<lambda>s. Expr_basic [s] in
    Definition_abbrev0
      name
      (b (number_of_str nb))
      (Expr_rewrite (b name) ''='' (Expr_lambda wildcard (Expr_some (Expr_some (b nb))))))) l)"

definition "print_examp_instance_app_constr oid_start b l = (\<lambda>isub_name app_x l_attr.
  Expr_apply
    (isub_name datatype_constr_name)
    ( app_x
    # (map (\<lambda>(_, ocl). case ocl of Shall_str s \<Rightarrow> Expr_some (b s)
                                 | Shall_binding n1 \<Rightarrow> (case flatten (fst (fold_list
                                         (\<lambda> OclInst n0 _ _ _ \<Rightarrow> \<lambda>cpt. ((if n1 = n0 then [Expr_some (Expr_oid var_oid_uniq (oidGetInh cpt))] else []), oidSucInh cpt))
                                         l oid_start)) of [s] \<Rightarrow> s)
                                 | Shall_self cpt1 \<Rightarrow> (case flatten (fst (fold_list
                                         (\<lambda> OclInst _ _ _ _ \<Rightarrow> \<lambda>cpt0. ((if oidGetInh cpt0 = cpt1 then [Expr_some (Expr_oid var_oid_uniq (oidGetInh cpt0))] else []), oidSucInh cpt0))
                                         l oid_start)) of [s] \<Rightarrow> s)
                                 | _ \<Rightarrow> b ''None'') l_attr)))"

definition "print_examp_instance_app_constr2 oid_start b l ty l_inh l_attr isub_name cpt =
  (let var_oid = Expr_oid var_oid_uniq (oidGetInh cpt) in
   print_examp_instance_app_constr oid_start b l isub_name
     (case l_inh of OclNoInh l_inh \<Rightarrow> Expr_apply (isub_name datatype_ext_constr_name) (var_oid # map (\<lambda>_. b ''None'') l_inh)
                  | OclInh l_inh l_attr x \<Rightarrow>
                      Expr_apply
                        (datatype_ext_constr_name @@ mk_constr_name ty x)
                        [ let isub_name = \<lambda>s. s @@ isub_of_str x in
                          print_examp_instance_app_constr oid_start b l isub_name (Expr_apply (isub_name datatype_ext_constr_name) (var_oid # map (\<lambda>_. b ''None'') l_inh)) l_attr ])
     l_attr)"

definition "print_examp_instance_tmp_name isub_name name = isub_name name"
definition "print_examp_instance_tmp = (\<lambda> OclInstance l \<Rightarrow> \<lambda> OclDeepEmbed disable_thy_output file_out_path_dep oid_start output_position design_analysis () \<Rightarrow>
      (\<lambda>(l, oid_start). ((List_map Thy_definition_hol o flatten) l, OclDeepEmbed disable_thy_output file_out_path_dep oid_start output_position design_analysis ()))
      (fold_list
      (\<lambda> (f1, f2) _.
        fold_list (\<lambda> OclInst name ty l_inh l_attr \<Rightarrow> \<lambda>cpt.
          let var_oid = Expr_oid var_oid_uniq (oidGetInh cpt)
            ; b = \<lambda>s. Expr_basic [s]
            ; isub_name = \<lambda>s. s @@ isub_of_str ty in
          ( Definition (Expr_rewrite (f1 var_oid b isub_name name ty) ''='' (f2 b l ty l_inh l_attr isub_name cpt name))
          , oidSucInh cpt)) l oid_start)
      [ ((\<lambda> var_oid _ _ _ _. var_oid),
         (\<lambda> _ _ _ _ _ _ cpt _. Expr_oid '''' (oidGetInh cpt)))
      , ((\<lambda> _ b isub_name name _. b (print_examp_instance_tmp_name isub_name name)),
         (\<lambda> b l ty l_inh l_attr isub_name cpt _. print_examp_instance_app_constr2 oid_start b l ty l_inh l_attr isub_name cpt))
      , ((\<lambda> _ b _ name ty. Expr_annot (b name) ty),
         (\<lambda> b _ _ _ _ isub_name _ name. Expr_lambda wildcard (Expr_some (Expr_some (b (print_examp_instance_tmp_name isub_name name)))))) ]
      oid_start))"

definition "print_examp_def_st_tmp = (\<lambda> OclDefSt name l \<Rightarrow> \<lambda> OclDeepEmbed disable_thy_output file_out_path_dep oid_start output_position design_analysis () \<Rightarrow>
      (\<lambda>(l, _). (List_map Thy_definition_hol l, OclDeepEmbed disable_thy_output file_out_path_dep oid_start output_position design_analysis ()))
  (let oid_start = oidReinitInh oid_start
     ; b = \<lambda>s. Expr_basic [s]
     ; (expr_app, cpt) = fold_list (\<lambda> ocore cpt.
         let f = \<lambda>ty exp. [Expr_binop (Expr_oid var_oid_uniq (oidGetInh cpt)) unicode_mapsto (Expr_apply (datatype_in @@ isub_of_str ty) [exp])] in
         ( case ocore of OclDefCoreSkip \<Rightarrow> []
                       | OclDefCoreBinding name ty \<Rightarrow>
                           let isub_name = \<lambda>s. s @@ isub_of_str ty in
                           f ty (b (print_examp_instance_tmp_name isub_name name))
                       | OclDefCoreAdd (OclInst n0 ty l_inh l_attr) \<Rightarrow>
                           let isub_name = \<lambda>s. s @@ isub_of_str ty in
                           f ty (print_examp_instance_app_constr2 oid_start b (List_map (\<lambda> OclDefCoreAdd x \<Rightarrow> x
                                                                               | _ \<Rightarrow> OclInst [] [] (OclNoInh []) []) l) ty l_inh l_attr isub_name cpt)
         , oidSucInh cpt)) l oid_start in
   ([ Definition (Expr_rewrite (b name) ''='' (Expr_apply ''state.make'' [Expr_apply ''empty''
       (flatten expr_app), b ''empty'', b ''empty''])) ], cpt)))"

definition "print_examp_def_st_defs = (\<lambda> _ \<Rightarrow> start_map Thy_lemmas_simp
  ([ Lemmas_simp '''' [Thm_strs ''state.defs'' 0] ]))"

subsection{* Conclusion *}

definition "section_aux n s = start_map' (\<lambda>_. [ Thy_section_title (Section_title n s) ])"
definition "section = section_aux 0"
definition "subsection = section_aux 1"
definition "subsubsection = section_aux 2"

definition "thy_object =
  (let subsection_def = subsection ''Definition''
     ; subsection_cp = subsection ''Context Passing''
     ; subsection_exec = subsection ''Execution with Invalid or Null as Argument''
     ; subsection_up = subsection ''Up Down Casting''
     ; subsection_defined = subsection ''Validity and Definedness Properties'' in
  flatten
          [ [ section ''Introduction''
            , subsection ''Outlining the Example''

            , section ''Example Data-Universe and its Infrastructure''
            , print_infra_datatype_class
            , print_infra_datatype_universe
            , print_infra_type_synonym_class
            , print_infra_instantiation_class
            , print_infra_instantiation_universe

            , section ''Instantiation of the Generic Strict Equality''
            , print_instantia_def_strictrefeq
            , print_instantia_lemmas_strictrefeq ]

          , flatten (map (\<lambda>(title, body_def, body_cp, body_exec, body_defined, body_up).
              section title # flatten [ subsection_def # body_def
                                      , subsection_cp # body_cp
                                      , subsection_exec # body_exec
                                      , subsection_defined # body_defined
                                      , subsection_up # body_up ])
          [ (''OclAsType'',
            [ print_astype_consts
            , print_astype_class
            (*, print_astype_from_universe*), print_astype_from_universe'
            , print_astype_lemmas_id ]
            , [ print_astype_lemma_cp
            , print_astype_lemmas_cp ]
            , [ print_astype_lemma_strict
            , print_astype_lemmas_strict ]
            , [ print_astype_defined ]
            , [ print_astype_up_d_cast0
            , print_astype_up_d_cast ])

          , (''OclIsTypeOf'',
            [ print_istypeof_consts
            , print_istypeof_class
            , print_istypeof_from_universe(*, print_istypeof_from_universe'*)
            , print_istypeof_lemmas_id ]
            , [ print_istypeof_lemma_cp
            , print_istypeof_lemmas_cp ]
            , [ print_istypeof_lemma_strict
            , print_istypeof_lemmas_strict ]
            , [ print_istypeof_defined
            , print_istypeof_defined' ]
            , [ print_istypeof_up_larger
            , print_istypeof_up_d_cast ])

          , (''OclIsKindOf'',
            [ print_iskindof_consts
            , print_iskindof_class
            , print_iskindof_from_universe(*, print_iskindof_from_universe'*)
            , print_iskindof_lemmas_id ]
            , [ print_iskindof_lemma_cp
            , print_iskindof_lemmas_cp ]
            , [ print_iskindof_lemma_strict
            , print_iskindof_lemmas_strict ]
            , [ print_iskindof_defined
            , print_iskindof_defined' ]
            , [ print_iskindof_up_eq_asty
            , print_iskindof_up_larger
            , print_iskindof_up_istypeof
            , print_iskindof_up_d_cast ]) ])

          , [ section ''OclAllInstances''
            , print_allinst_def_id
            , print_allinst_lemmas_id
            , subsection ''OclIsTypeOf''
            , subsection ''OclIsKindOf''

            , section ''The Accessors''
            , subsection_def
            , print_access_oid_uniq
            , print_access_eval_extract
            , print_access_choose
            , print_access_deref_oid
            , print_access_deref_assocs
            , print_access_select_object
            , print_access_select
            , print_access_select_obj
            , print_access_dot_consts
            , print_access_dot
            , print_access_dot_lemmas_id
            , subsection_cp
            , print_access_dot_cp_lemmas
            , print_access_dot_lemma_cp
            , print_access_dot_lemmas_cp
            , subsection_exec
            , print_access_lemma_strict

            , section ''A Little Infra-structure on Example States''
            , print_examp_def_st_defs ] ])"

definition "thy_object' = [ print_examp_oclint ]"
definition "thy_object'' = [ print_examp_instance_tmp ]"
definition "thy_object''' = [ print_examp_def_st_tmp ]"

definition "fold_thy0 univ thy_object0 f =
  fold (\<lambda>x (acc1, acc2).
    let (l, acc1) = x univ acc1 in
    (acc1, f l acc2)) thy_object0"
definition "fold_thy' f ast =
               (case ast of OclAstClass univ \<Rightarrow> fold_thy0 univ thy_object
                          | OclAstInstance univ \<Rightarrow> fold_thy0 univ thy_object''
                          | OclAstDefInt univ \<Rightarrow> fold_thy0 univ thy_object'
                          | OclAstDefState univ \<Rightarrow> fold_thy0 univ thy_object''') f"
definition "fold_thy = fold_thy' o fold"
definition "fold_thy_deep obj ocl =
  (case ocl of OclDeepEmbed _ _ _ output_position _ () \<Rightarrow>
   case fold_thy' (\<lambda>l (i, cpt). (Suc i, List.length l + cpt)) obj (ocl, output_position) of
    (OclDeepEmbed disable_thy_output file_out_path_dep oid_start _ design_analysis (), output_position) \<Rightarrow>
    OclDeepEmbed disable_thy_output file_out_path_dep oid_start output_position design_analysis ())"

definition "ocl_deep_embed_input_empty design_analysis = OclDeepEmbed True None (oidInit (Oid 0)) (0, 0) design_analysis ()"

section{* Generation to Deep Form: OCaml *}
subsection{* beginning *}

code_printing code_module "" \<rightharpoonup> (OCaml) {*

let (<<) f g x = f (g x)

module To = struct
  type nat = Zero_nat | Suc of nat

  type nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
    Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
    | NibbleE | NibbleF

  type char = Char of nibble * nibble

  module M = struct
    let to_nibble = function
      Nibble0 -> 0x0 | Nibble1 -> 0x1 | Nibble2 -> 0x2 | Nibble3 -> 0x3 | Nibble4 -> 0x4 | Nibble5 -> 0x5 |
       Nibble6 -> 0x6 | Nibble7 -> 0x7 | Nibble8 -> 0x8 | Nibble9 -> 0x9 | NibbleA -> 0xA | NibbleB -> 0xB | NibbleC -> 0xC | NibbleD -> 0xD
      | NibbleE -> 0xE | NibbleF -> 0xF

    let to_char = function Char (n1, n2) -> char_of_int (to_nibble n1 lsl 4 + to_nibble n2)

    let to_string l = (String.concat "" (List.map (fun c -> String.make 1 (to_char c)) l))
  (*
    let to_num =
      let rec aux mot n = function
        | Bit0 p -> aux mot (succ n) p
        | bit ->
          let mot = mot + (1 lsl n) in
          match bit with
          | Bit1 p -> aux mot (succ n) p
          | _ -> mot in
      aux 0 0

    let to_int = function
      | ZeroInt -> 0
      | Pos n -> to_num n
      | Neg n -> - (to_num n)
  *)
    let to_nat =
      let rec aux n = function Zero_nat -> n | Suc xs -> aux (succ n) xs in
      aux 0
  end

  let string nibble_rec char_rec =
    let ofN = nibble_rec
      Nibble0 Nibble1 Nibble2 Nibble3 Nibble4 Nibble5
      Nibble6 Nibble7 Nibble8 Nibble9 NibbleA NibbleB
      NibbleC NibbleD NibbleE NibbleF in
    M.to_string << List.map (char_rec (fun c1 c2 -> Char (ofN c1, ofN c2)))

  let nat nat_rec =
    M.to_nat << nat_rec Zero_nat (fun _ x -> Suc x)

  let oid oid_rec nat_rec oid =
    oid_rec (nat nat_rec) oid
end

module CodeType = struct
  module Cancel_rec = struct
    type i = int
  end
  type int = Cancel_rec.i
end

module CodeConst = struct
  (* here contain functions using characters
     not allowed in a Isabelle 'code_const' expr
     (e.g. '_', '"', ...) *)

  let outFile1 f file =
    let () = if Sys.file_exists file then Printf.eprintf "File exists %s\n" file else () in
    let oc = open_out file in
    let () = f (Printf.fprintf oc) in
    close_out oc

  let outStand1 f =
    f (Printf.fprintf stdout)

  module Sys = struct open Sys
    let isDirectory2 s = try is_directory s with _ -> false
    let argv = Array.to_list argv
  end

  module Printf = Printf
  module String = String
  module To = To
end

*}

subsection{* ML type *}

type_synonym ml_string = String.literal
datatype ml_nat = ML_nat
datatype ml_nibble = ML_nibble
datatype ml_char = ML_char
datatype ml_int = ML_int
datatype ml_oid = ML_oid

code_printing type_constructor ml_int \<rightharpoonup> (OCaml) "CodeType.int"

subsection{* ML code const *}

text{* ... *}

consts out_file0 :: "((ml_string \<Rightarrow> unit) (* fprintf *) \<Rightarrow> unit) \<Rightarrow> ml_string \<Rightarrow> unit"
consts out_file1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit) (* fprintf *) \<Rightarrow> unit) \<Rightarrow> ml_string \<Rightarrow> unit"
code_printing constant out_file1 \<rightharpoonup> (OCaml) "CodeConst.outFile1"

consts out_stand1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit) (* fprintf *) \<Rightarrow> unit) \<Rightarrow> unit"
code_printing constant out_stand1 \<rightharpoonup> (OCaml) "CodeConst.outStand1"

text{* module To *}

consts ToString :: "(ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> ml_nibble \<Rightarrow> nibble \<Rightarrow> ml_nibble) \<Rightarrow>
                    ((nibble \<Rightarrow> nibble \<Rightarrow> ml_char) \<Rightarrow> char \<Rightarrow> ml_char) \<Rightarrow>
                    string \<Rightarrow> ml_string"
code_printing constant ToString \<rightharpoonup> (OCaml) "CodeConst.To.string"
definition "To_string = ToString nibble_rec char_rec"

consts ToNat :: "(ml_nat \<Rightarrow> (nat \<Rightarrow> ml_nat \<Rightarrow> ml_nat) \<Rightarrow> nat \<Rightarrow> ml_nat) \<Rightarrow>
                 nat \<Rightarrow> ml_int"
code_printing constant ToNat \<rightharpoonup> (OCaml) "CodeConst.To.nat"
definition "To_nat = ToNat nat_rec"

consts ToOid :: "((nat \<Rightarrow> ml_oid) \<Rightarrow> internal_oid \<Rightarrow> ml_oid) \<Rightarrow>
                  (ml_nat \<Rightarrow> (nat \<Rightarrow> ml_nat \<Rightarrow> ml_nat) \<Rightarrow> nat \<Rightarrow> ml_nat) \<Rightarrow>
                 internal_oid \<Rightarrow> ml_int"
code_printing constant ToOid \<rightharpoonup> (OCaml) "CodeConst.To.oid"
definition "To_oid = ToOid internal_oid_rec nat_rec"

text{* module Printf *}

consts sprintf0 :: "ml_string \<Rightarrow> ml_string"
consts sprintf1 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> ml_string"
consts sprintf2 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> ml_string"
consts sprintf3 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> ml_string"
consts sprintf4 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> ml_string"
consts sprintf5 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> '\<alpha>5 \<Rightarrow> ml_string"
consts sprintf6 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> '\<alpha>5 \<Rightarrow> '\<alpha>6 \<Rightarrow> ml_string"

code_printing constant sprintf0 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
code_printing constant sprintf1 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
code_printing constant sprintf2 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
code_printing constant sprintf3 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
code_printing constant sprintf4 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
code_printing constant sprintf5 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
code_printing constant sprintf6 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"

consts eprintf0 :: "ml_string \<Rightarrow> unit"
code_printing constant eprintf0 \<rightharpoonup> (OCaml) "CodeConst.Printf.eprintf"

(* Monomorph *)

consts sprintf1s :: "ml_string \<Rightarrow> ml_string \<Rightarrow> ml_string"
code_printing constant sprintf1s \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"
consts sprintf2ss :: "ml_string \<Rightarrow> ml_string \<Rightarrow> ml_string \<Rightarrow> ml_string"
code_printing constant sprintf2ss \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf"

text{* module String *}

consts String_concat :: "ml_string \<Rightarrow> ml_string list \<Rightarrow> ml_string"
code_printing constant String_concat \<rightharpoonup> (OCaml) "CodeConst.String.concat"

text{* module List *}

definition "List_iter f = foldl (\<lambda>_. f) ()"
definition "List_mapi f l = (let (l, _) = foldl (\<lambda>(acc, n) x. (f n x # acc, Suc n)) ([], 0) l in rev l)"

text{* module Sys *}

consts Sys_is_directory2 :: "ml_string \<Rightarrow> bool"
code_printing constant Sys_is_directory2 \<rightharpoonup> (OCaml) "CodeConst.Sys.isDirectory2"

consts Sys_argv :: "ml_string list"
code_printing constant Sys_argv \<rightharpoonup> (OCaml) "CodeConst.Sys.argv"

text{* module Unicode *}

definition "Unicode_mk_u = sprintf1s (STR (Char Nibble5 NibbleC # ''<%s>''))"
definition "Unicode_u_Rightarrow = Unicode_mk_u (STR ''Rightarrow'')"
definition "Unicode_u_alpha = Unicode_mk_u (STR ''alpha'')"
definition "Unicode_u_lambda = Unicode_mk_u (STR ''lambda'')"
definition "Unicode_u_lfloor = Unicode_mk_u (STR ''lfloor'')"
definition "Unicode_u_rfloor = Unicode_mk_u (STR ''rfloor'')"
definition "Unicode_u_Longrightarrow = Unicode_mk_u (STR ''Longrightarrow'')"

subsection{* s of ... *} (* s_of *)

definition "s_of_dataty = (\<lambda> Datatype n l \<Rightarrow>
  sprintf2 (STR ''datatype %s = %s'')
    (To_string n)
    (String_concat (STR ''
                        | '')
      (List_map
        (\<lambda>(n,l).
         sprintf2 (STR ''%s %s'')
           (To_string n)
           (String_concat (STR '' '')
            (List_map
              (\<lambda> Opt o_ \<Rightarrow> sprintf1 (STR ''\"%s option\"'') (To_string o_)
               | Raw o_ \<Rightarrow> sprintf1 (STR ''%s'') (To_string o_))
              l))) l) ))"

fun s_of_rawty where "s_of_rawty rawty = (case rawty of
    Ty_base s \<Rightarrow> To_string s
  | Ty_apply name l \<Rightarrow> sprintf2 (STR ''%s %s'') (let s = String_concat (STR '', '') (map s_of_rawty l) in
                                                 case l of [_] \<Rightarrow> s | _ \<Rightarrow> sprintf1 (STR ''(%s)'') s)
                                                (s_of_rawty name))"

definition "s_of_ty_synonym = (\<lambda> Type_synonym n l \<Rightarrow>
    sprintf2 (STR ''type_synonym %s = \"%s\"'') (To_string n) (s_of_rawty l))"

fun s_of_expr where "s_of_expr expr = (
  case expr of
    Expr_case e l \<Rightarrow> sprintf2 (STR ''(case %s of %s)'') (s_of_expr e) (String_concat (STR ''
    | '') (map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) Unicode_u_Rightarrow (s_of_expr s2)) l))
  | Expr_rewrite e1 symb e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (To_string symb) (s_of_expr e2)
  | Expr_basic l \<Rightarrow> sprintf1 (STR ''%s'') (String_concat (STR '' '') (List_map To_string l))
  | Expr_oid tit s \<Rightarrow> sprintf2 (STR ''%s%d'') (To_string tit) (To_oid s)
  | Expr_binop e1 s e2 \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr e1) (s_of_expr (Expr_basic [s])) (s_of_expr e2)
  | Expr_annot e s \<Rightarrow> sprintf2 (STR ''(%s::%s)'') (s_of_expr e) (To_string s)
  | Expr_lambda s e \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') Unicode_u_lambda (To_string s) (s_of_expr e)
  | Expr_lambdas l e \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') Unicode_u_lambda (String_concat (STR '' '') (List_map To_string l)) (s_of_expr e)
  | Expr_lambdas0 e1 e2 \<Rightarrow> sprintf3 (STR ''(%s%s. %s)'') Unicode_u_lambda (s_of_expr e1) (s_of_expr e2)
  | Expr_function l \<Rightarrow> sprintf2 (STR ''(%s %s)'') Unicode_u_lambda (String_concat (STR ''
    | '') (map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) Unicode_u_Rightarrow (s_of_expr s2)) l))
  (*| Expr_apply s [e] \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (s_of_expr e)*)
  | Expr_apply s l \<Rightarrow> sprintf2 (STR ''(%s %s)'') (To_string s) (String_concat (STR '' '') (map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)) l))
  | Expr_applys e l \<Rightarrow> sprintf2 (STR ''((%s) %s)'') (s_of_expr e) (String_concat (STR '' '') (map (\<lambda> e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)) l))
  | Expr_some (Expr_function l) \<Rightarrow> sprintf4 (STR ''%s%s %s%s'') Unicode_u_lfloor Unicode_u_lambda (String_concat (STR ''
    | '') (map (\<lambda> (s1, s2) \<Rightarrow> sprintf3 (STR ''%s %s %s'') (s_of_expr s1) Unicode_u_Rightarrow (s_of_expr s2)) l)) Unicode_u_rfloor
  | Expr_some e \<Rightarrow> sprintf3 (STR ''%s%s%s'') Unicode_u_lfloor (s_of_expr e) Unicode_u_rfloor
  | Expr_postunary e1 e2 \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e1) (s_of_expr e2)
  | Expr_preunary e1 e2 \<Rightarrow> sprintf2 (STR ''%s %s'') (s_of_expr e1) (s_of_expr e2)
  | Expr_warning_parenthesis e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e)
  | Expr_parenthesis e \<Rightarrow> sprintf1 (STR ''(%s)'') (s_of_expr e))"

definition "s_of_instantiation_class = (\<lambda> Instantiation n n_def expr \<Rightarrow>
    let name = To_string n in
    sprintf4 (STR ''instantiation %s :: object
begin
  definition %s_%s_def : \"%s\"
  instance ..
end'')
      name
      (To_string n_def)
      name
      (s_of_expr expr))"

definition "s_of_defs_overloaded = (\<lambda> Defs_overloaded n e \<Rightarrow>
    sprintf2 (STR ''defs(overloaded) %s : \"%s\"'') (To_string n) (s_of_expr e))"

definition "s_of_consts_class = (\<lambda> Consts_raw n ty_out1 ty_out2 symb \<Rightarrow>
    sprintf5 (STR ''consts %s :: \"%s %s %s\" (\"(_) %s\")'') (To_string n) (s_of_rawty ty_out1) Unicode_u_Rightarrow (s_of_rawty ty_out2) (To_string symb))"

definition "s_of_definition_hol = (\<lambda>
    Definition e \<Rightarrow> sprintf1 (STR ''definition \"%s\"'') (s_of_expr e)
  | Definition_abbrev name (abbrev, prio) e \<Rightarrow> sprintf4 (STR ''definition %s (\"(1%s)\" %d)
  where \"%s\"'') (To_string name) (s_of_expr abbrev) (To_nat prio) (s_of_expr e)
  | Definition_abbrev0 name abbrev e \<Rightarrow> sprintf3 (STR ''definition %s (\"%s\")
  where \"%s\"'') (To_string name) (s_of_expr abbrev) (s_of_expr e))"

fun s_of_ntheorem_aux where "s_of_ntheorem_aux lacc expr =
  (let f_where = (\<lambda>l. (STR ''where'', String_concat (STR '' and '')
                                        (List_map (\<lambda>(var, expr). sprintf2 (STR ''%s = \"%s\"'')
                                                        (To_string var)
                                                        (s_of_expr expr)) l)))
     ; f_of = (\<lambda>l. (STR ''of'', String_concat (STR '' '')
                                  (List_map (\<lambda>expr. sprintf1 (STR ''\"%s\"'')
                                                        (s_of_expr expr)) l)))
     ; f_symmetric = (STR ''symmetric'', STR '''')
     ; s_base = (\<lambda>s lacc. sprintf2 (STR ''%s[%s]'') (To_string s) (String_concat (STR '', '') (List_map (\<lambda>(s, x). sprintf2 (STR ''%s %s'') s x) lacc))) in
  (\<lambda> Thm_str s \<Rightarrow> To_string s
   | Thm_strs s _ \<Rightarrow> To_string s
   | Thm_THEN (Thm_str s) e2 \<Rightarrow> s_base s ((STR ''THEN'', s_of_ntheorem_aux [] e2) # lacc)
   | Thm_THEN e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''THEN'', s_of_ntheorem_aux [] e2) # lacc) e1
   | Thm_simplified (Thm_str s) e2 \<Rightarrow> s_base s ((STR ''simplified'', s_of_ntheorem_aux [] e2) # lacc)
   | Thm_simplified e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''simplified'', s_of_ntheorem_aux [] e2) # lacc) e1
   | Thm_symmetric (Thm_str s) \<Rightarrow> s_base s (f_symmetric # lacc)
   | Thm_symmetric e1 \<Rightarrow> s_of_ntheorem_aux (f_symmetric # lacc) e1
   | Thm_where (Thm_str s) l \<Rightarrow> s_base s (f_where l # lacc)
   | Thm_where e1 l \<Rightarrow> s_of_ntheorem_aux (f_where l # lacc) e1
   | Thm_of (Thm_str s) l \<Rightarrow> s_base s (f_of l # lacc)
   | Thm_of e1 l \<Rightarrow> s_of_ntheorem_aux (f_of l # lacc) e1
   | Thm_OF (Thm_str s) e2 \<Rightarrow> s_base s ((STR ''OF'', s_of_ntheorem_aux [] e2) # lacc)
   | Thm_OF e1 e2 \<Rightarrow> s_of_ntheorem_aux ((STR ''OF'', s_of_ntheorem_aux [] e2) # lacc) e1) expr)"

definition "s_of_ntheorem = s_of_ntheorem_aux []"

definition "s_of_lemmas_simp = (\<lambda> Lemmas_simp s l \<Rightarrow>
    sprintf2 (STR ''lemmas%s [simp,code_unfold] = %s'')
      (if s = [] then STR '''' else To_string ('' '' @@ s))
      (String_concat (STR ''
                            '') (List_map s_of_ntheorem l)))"

fun s_of_tactic where "s_of_tactic expr = (\<lambda>
    Tac_rule s \<Rightarrow> sprintf1 (STR ''rule %s'') (s_of_ntheorem s)
  | Tac_erule s \<Rightarrow> sprintf1 (STR ''erule %s'') (s_of_ntheorem s)
  | Tac_elim s \<Rightarrow> sprintf1 (STR ''elim %s'') (s_of_ntheorem s)
  | Tac_subst s => sprintf1 (STR ''subst %s'') (s_of_ntheorem s)
  | Tac_insert l => sprintf1 (STR ''insert %s'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | Tac_plus t \<Rightarrow> sprintf1 (STR ''(%s)+'') (String_concat (STR '', '') (map s_of_tactic t))
  | Tac_simp \<Rightarrow> sprintf0 (STR ''simp'')
  | Tac_simp_add l \<Rightarrow> sprintf1 (STR ''simp add: %s'') (String_concat (STR '' '') (List_map To_string l))
  | Tac_simp_only l \<Rightarrow> sprintf1 (STR ''simp only: %s'') (String_concat (STR '' '') (List_map s_of_ntheorem l))
  | Tac_simp_all \<Rightarrow> sprintf0 (STR ''simp_all'')
  | Tac_simp_all_add s \<Rightarrow> sprintf1 (STR ''simp_all add: %s'') (To_string s)
  | Tac_auto_simp_add l \<Rightarrow> sprintf1 (STR ''auto simp: %s'') (String_concat (STR '' '') (List_map To_string l))
  | Tac_auto_simp_add_split l_simp l_split \<Rightarrow>
      let f = String_concat (STR '' '') in
      sprintf2 (STR ''auto simp: %s split: %s'') (f (List_map s_of_ntheorem l_simp)) (f (List_map To_string l_split))
  | Tac_rename_tac l \<Rightarrow> sprintf1 (STR ''rename_tac %s'') (String_concat (STR '' '') (List_map To_string l))
  | Tac_case_tac e \<Rightarrow> sprintf1 (STR ''case_tac \"%s\"'') (s_of_expr e)) expr"

definition "s_of_tactic_last = (\<lambda> Tacl_done \<Rightarrow> STR ''done''
                                | Tacl_by l_apply \<Rightarrow> sprintf1 (STR ''by(%s)'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))
                                | Tacl_sorry \<Rightarrow> STR ''sorry'')"

definition "s_of_lemma_by =
 (\<lambda> Lemma_by n l_spec l_apply tactic_last \<Rightarrow>
    sprintf4 (STR ''lemma %s : \"%s\"
%s%s'')
      (To_string n)
      (String_concat (sprintf1 (STR '' %s '') Unicode_u_Longrightarrow) (List_map s_of_expr l_spec))
      (String_concat (STR '''') (List_map (\<lambda> [] \<Rightarrow> STR '''' | l_apply \<Rightarrow> sprintf1 (STR ''  apply(%s)
'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))) l_apply))
      (s_of_tactic_last tactic_last)
  | Lemma_by_assum n l_spec concl l_apply tactic_last \<Rightarrow>
    sprintf4 (STR ''lemma %s : %s
%s%s'')
      (To_string n)
      (String_concat (STR '''') (List_map (\<lambda>(n, e).
          sprintf2 (STR ''
assumes %s\"%s\"'')
            (if n = '''' then STR '''' else sprintf1 (STR ''%s: '') (To_string n))
            (s_of_expr e)) l_spec
       @@
       [sprintf1 (STR ''
shows \"%s\"'') (s_of_expr concl)]))
      (String_concat (STR '''') (List_map (\<lambda> App [] \<Rightarrow> STR '''' | App l_apply \<Rightarrow>
sprintf1 (STR ''  apply(%s)
'') (String_concat (STR '', '') (List_map s_of_tactic l_apply))
        | App_using l \<Rightarrow> sprintf1 (STR ''  using %s
'') (String_concat (STR '' '') (List_map s_of_ntheorem l))) l_apply))
      (s_of_tactic_last tactic_last))"

definition "s_of_section_title disable_thy_output = (\<lambda> Section_title n section_title \<Rightarrow>
  if disable_thy_output then
    STR ''''
  else
    sprintf2 (STR ''%s{* %s *}'')
      (To_string ((case n of 0 \<Rightarrow> ''''
                     | Suc 0 \<Rightarrow> ''sub''
                     | Suc (Suc _) \<Rightarrow> ''subsub'') @@ ''section''))
      (To_string section_title))"

definition "s_of_thy disable_thy_output =
            (\<lambda> Thy_dataty dataty \<Rightarrow> s_of_dataty dataty
             | Thy_ty_synonym ty_synonym \<Rightarrow> s_of_ty_synonym ty_synonym
             | Thy_instantiation_class instantiation_class \<Rightarrow> s_of_instantiation_class instantiation_class
             | Thy_defs_overloaded defs_overloaded \<Rightarrow> s_of_defs_overloaded defs_overloaded
             | Thy_consts_class consts_class \<Rightarrow> s_of_consts_class consts_class
             | Thy_definition_hol definition_hol \<Rightarrow> s_of_definition_hol definition_hol
             | Thy_lemmas_simp lemmas_simp \<Rightarrow> s_of_lemmas_simp lemmas_simp
             | Thy_lemma_by lemma_by \<Rightarrow> s_of_lemma_by lemma_by
             | Thy_section_title section_title \<Rightarrow> s_of_section_title disable_thy_output section_title)"

definition "s_of_thy_list disable_thy_output name_fic_import output_position is_file l_thy =
  (let (th_beg, th_end) = case name_fic_import of None \<Rightarrow> ([], [])
   | Some (name, fic_import) \<Rightarrow>
       ( [ sprintf2 (STR ''theory %s imports \"%s\" begin'') (To_string name) (To_string fic_import) ]
       , [ STR '''', STR ''end'' ]) in
  flatten
        [ th_beg
        , flatten (fst (fold_list (\<lambda>l (i, cpt).
            let (l_thy, lg) = fold_list (\<lambda>l n. (s_of_thy disable_thy_output l, Suc n)) l 0 in
            (( STR ''''
             # sprintf4 (STR ''%s(* %d ************************************ %d + %d *)'')
                 (To_string (if is_file then '''' else [char_escape])) (To_nat (Suc i)) (To_nat cpt) (To_nat lg)
             # l_thy), Suc i, cpt + lg)) l_thy output_position))
        , th_end ])"

subsection{* conclusion *}

definition "write_file = (\<lambda> OclDeepEmbed disable_thy_output file_out_path_dep oid_start output_position design_analysis example \<Rightarrow>
  let (is_file, f_output) = case (file_out_path_dep, Sys_argv)
     of (Some (file_out, _), _ # dir # _) \<Rightarrow> (True, \<lambda>f. out_file1 f (if Sys_is_directory2 dir then sprintf2 (STR ''%s/%s.thy'') dir (To_string file_out) else dir))
      | _ \<Rightarrow> (False, out_stand1) in
  f_output
    (\<lambda>fprintf1.
      List_iter (fprintf1 (STR ''%s
''                                 ))
        (s_of_thy_list disable_thy_output file_out_path_dep output_position is_file
          ((rev o snd o fold_thy' Cons example)
             (OclDeepEmbed disable_thy_output file_out_path_dep oid_start output_position design_analysis (), [])))))"

subsection{* Deep (without reflection) *}

definition "Employee_DesignModel_UMLPart =
         OclClass ''OclAny'' []
  (Some (OclClass ''Galaxy'' [(''sound'', OclTy_base ''unit''), (''moving'', OclTy_base ''bool'')]
  (Some (OclClass ''Planet'' [(''weight'', OclTy_base ''nat'')]
  (Some (OclClass ''Person'' [(''salary'', OclTy_base ''int''), (''boss'', object)]
   None )) )) ))"

definition "main = write_file (OclDeepEmbed
                                 False
                                 (Some (''Employee_DesignModel_UMLPart_generated''
                                       ,''../src/OCL_main''))
                                 (oidInit (Oid 0))
                                 (0, 0)
                                 None
                                 (OclAstClass Employee_DesignModel_UMLPart))"
(*
export_code main
  in OCaml module_name M
  (no_signatures)
*)
section{* Generation to Shallow Form: SML *}

subsection{* i of ... *} (* i_of *)

definition "i_of_string b s = (let c = [Char Nibble2 Nibble7] in b (flatten [c,c, s, c,c]))"

(* *)

definition "K x _ = x"

definition "co1 = op o"
definition "co2 f g x1 x2 = f (g x1 x2)"
definition "co3 f g x1 x2 x3 = f (g x1 x2 x3)"
definition "co4 f g x1 x2 x3 x4 = f (g x1 x2 x3 x4)"
definition "co5 f g x1 x2 x3 x4 x5 = f (g x1 x2 x3 x4 x5)"
definition "co6 f g x1 x2 x3 x4 x5 x6 = f (g x1 x2 x3 x4 x5 x6)"

definition "ap1 a v0 f1 v1 = a v0 (f1 v1)"
definition "ap2 a v0 f1 f2 v1 v2 = a (a v0 (f1 v1)) (f2 v2)"
definition "ap3 a v0 f1 f2 f3 v1 v2 v3 = a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)"
definition "ap4 a v0 f1 f2 f3 f4 v1 v2 v3 v4 = a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)"
definition "ap5 a v0 f1 f2 f3 f4 f5 v1 v2 v3 v4 v5 = a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)"
definition "ap6 a v0 f1 f2 f3 f4 f5 f6 v1 v2 v3 v4 v5 v6 = a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5)) (f6 v6)"

definition "ar1 a v0 = a v0"
definition "ar2 a v0 f1 v1 = a (a v0 (f1 v1))"
definition "ar3 a v0 f1 f2 v1 v2 = a (a (a v0 (f1 v1)) (f2 v2))"
definition "ar4 a v0 f1 f2 f3 v1 v2 v3 = a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3))"
definition "ar5 a v0 f1 f2 f3 f4 v1 v2 v3 v4 = a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4))"
definition "ar6 a v0 f1 f2 f3 f4 f5 v1 v2 v3 v4 v5 = a (a (a (a (a (a v0 (f1 v1)) (f2 v2)) (f3 v3)) (f4 v4)) (f5 v5))"

(* *)

definition "i_of_bool b = bool_rec
  (b ''True'')
  (b ''False'')"

definition "i_of_pair a b f1 f2 = (\<lambda>f. \<lambda>(c, d) \<Rightarrow> f c d)
  (ap2 a (b ''Pair'') f1 f2)"

definition "i_of_list a b f = (\<lambda>f0. list_rec f0 o co1 K)
  (b ''Nil'')
  (ar2 a (b ''Cons'') f)"

definition "i_of_option a b f = option_rec
  (b ''None'')
  (ap1 a (b ''Some'') f)"

definition "i_of_nat a b = (\<lambda>f0. nat_rec f0 o K)
  (b ''0'')
  (ar1 a (b ''Suc''))"

(* *)

definition "i_of_internal_oid a b = internal_oid_rec
  (ap1 a (b ''Oid'') (i_of_nat a b))"

definition "i_of_internal_oids a b = internal_oids_rec
  (ap3 a (b ''Oids'')
    (i_of_nat a b)
    (i_of_nat a b)
    (i_of_nat a b))"

definition "i_of_ocl_collection b = ocl_collection_rec
  (b ''Set'')
  (b ''Sequence'')"

definition "i_of_ocl_ty a b = (\<lambda>f1 f2. ocl_ty_rec f1 f2 o co1 K)
  (ap1 a (b ''OclTy_base'') (i_of_string b))
  (ap1 a (b ''OclTy_object'') (i_of_string b))
  (ar2 a (b ''OclTy_collection'') (i_of_ocl_collection b))
  (ap1 a (b ''OclTy_base_raw'') (i_of_string b))"

definition "i_of_ocl_class a b = (\<lambda>f0 f1 f2 f3. ocl_class_rec_1 (co2 K (ar3 a f0 f1 f2)) (f3 None) (K (f3 o Some)))
  (b ''OclClass'')
    (i_of_string b)
    (i_of_list a b (i_of_pair a b (i_of_string b) (i_of_ocl_ty a b)))
    (i_of_option a b id)"

definition "i_of_ocl_data_shallow a b = ocl_data_shallow_rec
  (ap1 a (b ''Shall_str'') (i_of_string b))
  (ap1 a (b ''Shall_binding'') (i_of_string b))
  (ap1 a (b ''Shall_self'') (i_of_internal_oid a b))
  (b ''Shall_tmp'')"

definition "i_of_ocl_list_inh a b = (\<lambda>f0. co4 (ocl_list_inh_rec f0) (ap3 a))
  (ap1 a (b ''OclNoInh'') (i_of_list a b (i_of_pair a b (i_of_string b) (i_of_ocl_data_shallow a b))))
  (b ''OclInh'')
    (i_of_list a b (i_of_pair a b (i_of_string b) (i_of_ocl_data_shallow a b)))
    (i_of_list a b (i_of_pair a b (i_of_string b) (i_of_ocl_data_shallow a b)))
    (i_of_string b)"

definition "i_of_ocl_instance_single a b = ocl_instance_single_rec
  (ap4 a (b ''OclInst'')
    (i_of_string b)
    (i_of_string b)
    (i_of_ocl_list_inh a b)
    (i_of_list a b (i_of_pair a b (i_of_string b) (i_of_ocl_data_shallow a b))))"

definition "i_of_ocl_instance a b = ocl_instance_rec
  (ap1 a (b ''OclInstance'') (i_of_list a b (i_of_ocl_instance_single a b)))"

definition "i_of_ocl_def_int a b = ocl_def_int_rec
  (ap1 a (b ''OclDefI'') (i_of_list a b (i_of_string b)))"

definition "i_of_ocl_def_state_core a b = ocl_def_state_core_rec
  (ap1 a (b ''OclDefCoreAdd'') (i_of_ocl_instance_single a b))
  (b ''OclDefCoreSkip'')
  (ap2 a (b ''OclDefCoreBinding'') (i_of_string b) (i_of_string b))"

definition "i_of_ocl_def_state a b = ocl_def_state_rec
  (ap2 a (b ''OclDefSt'') (i_of_string b) (i_of_list a b (i_of_ocl_def_state_core a b)))"

definition "i_of_ocl_deep_embed_ast a b = ocl_deep_embed_ast_rec
  (ap1 a (b ''OclAstClass'') (i_of_ocl_class a b))
  (ap1 a (b ''OclAstInstance'') (i_of_ocl_instance a b))
  (ap1 a (b ''OclAstDefInt'') (i_of_ocl_def_int a b))
  (ap1 a (b ''OclAstDefState'') (i_of_ocl_def_state a b))"

definition "i_of_ocl_deep_embed_input a b f = ocl_deep_embed_input_rec
  (ap6 a (b ''OclDeepEmbed'')
    (i_of_bool b)
    (i_of_option a b (i_of_pair a b (i_of_string b) (i_of_string b)))
    (i_of_internal_oids a b)
    (i_of_pair a b (i_of_nat a b) (i_of_nat a b))
    (i_of_option a b (i_of_nat a b))
    (f a b))"

(* *)

definition "i_apply l1 l2 = flatten [l1, '' ('', l2, '')'']"

subsection{* global *}

code_reflect OCL
   functions nibble_rec char_rec
             char_escape
             fold_thy fold_thy_deep ocl_deep_embed_input_empty
             i_apply i_of_ocl_deep_embed_input i_of_ocl_deep_embed_ast

ML{*
structure To = struct
  datatype nat = Zero_nat | Suc of nat

  datatype nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
    Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
    | NibbleE | NibbleF

  datatype char = Char of nibble * nibble

  structure M = struct
    val to_nibble = fn
      Nibble0 => 0x0 | Nibble1 => 0x1 | Nibble2 => 0x2 | Nibble3 => 0x3 | Nibble4 => 0x4 | Nibble5 => 0x5 |
       Nibble6 => 0x6 | Nibble7 => 0x7 | Nibble8 => 0x8 | Nibble9 => 0x9 | NibbleA => 0xA | NibbleB => 0xB | NibbleC => 0xC | NibbleD => 0xD
      | NibbleE => 0xE | NibbleF => 0xF

    val to_char = fn Char (n1, n2) => Char.chr ((to_nibble n1) * 16 + to_nibble n2)

    fun to_string l = (String.concat (map (fn c => str (to_char c)) l))

    val to_nat =
      let fun aux n = fn Zero_nat => n | Suc xs => aux (n + 1) xs in
      aux 0
      end
  end

  fun string nibble_rec char_rec =
    let val ofN = nibble_rec
      Nibble0 Nibble1 Nibble2 Nibble3 Nibble4 Nibble5
      Nibble6 Nibble7 Nibble8 Nibble9 NibbleA NibbleB
      NibbleC NibbleD NibbleE NibbleF in
    M.to_string o List.map (char_rec (fn c1 => fn c2 => Char (ofN c1, ofN c2)))
    end

  fun nat nat_rec =
    M.to_nat o nat_rec Zero_nat (fn _ => Suc)
end

 val To_string = To.string OCL.nibble_rec OCL.char_rec
 val To_nat = To.nat OCL.nat_rec
*}

ML{*
type class_inline = { attr_base : (binding * binding) list
                    , attr_object : binding list
                    , child : binding list
                    , ocl_class : OCL.ocl_class option }

structure Data = Theory_Data
  (type T = class_inline Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

structure From = struct
 open OCL
 val from_nibble = fn
       0x0 => Nibble0 | 0x1 => Nibble1 | 0x2 => Nibble2 | 0x3 => Nibble3 | 0x4 => Nibble4 | 0x5 => Nibble5 |
        0x6 => Nibble6 | 0x7 => Nibble7 | 0x8 => Nibble8 | 0x9 => Nibble9 | 0xA => NibbleA | 0xB => NibbleB | 0xC => NibbleC | 0xD => NibbleD
       | 0xE => NibbleE | 0xF => NibbleF
 fun from_char c = let val c = Char.ord c in OCL.Char (from_nibble (c div 16), from_nibble (c mod 16)) end
 fun from_string n = map from_char (String.explode n)
 val from_binding = from_string o Binding.name_of
 fun from_term ctxt s = from_string (XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt s)))
 val from_nat =
   let fun from_nat accu = fn 0 => accu | x => from_nat (Suc accu) (x - 1) in
   from_nat Zero_nat
   end
 val from_internal_oid = Oid
 val from_bool = I
 val from_option = Option.map
 fun from_pair f1 f2 (x, y) = (f1 x, f2 y)

 fun mk_univ (n, ({attr_base = attr_base, attr_object = attr_object, child = child, ...}:class_inline)) t =
   OclClass ( from_string n
           , List.concat [ map (fn (b, ty) => (from_binding b, OclTy_base (from_binding ty))) attr_base
                         , map (fn b => (from_binding b, object)) attr_object]
           , case child of [] => NONE | [x] => SOME (mk_univ (let val x = Binding.name_of x in (x, let val SOME v = Symtab.lookup t x in v end) end) t))
end

val () =
  Outer_Syntax.command @{command_spec "Class"} "Class definition"
    ((Parse.binding --| Parse.$$$ "=") --
      Scan.repeat (@{keyword "attr_base"} |-- Parse.!!! (Parse.binding -- (Parse.$$$ "::" |-- Parse.!!! Parse.binding))) --
      Scan.repeat (@{keyword "attr_object"} |-- Parse.!!! Parse.binding) --
      Scan.repeat (@{keyword "child"} |-- Parse.!!! Parse.binding)
        >> (fn (((binding, attr_base), attr_object), child) => fn x =>
              x |> Toplevel.theory (fn thy => thy |> Data.map (fn t =>
                                                     let val name = Binding.name_of binding
                                                     fun mk ocl_class = { attr_base = attr_base
                                                                        , attr_object = attr_object
                                                                        , child = child
                                                                        , ocl_class = ocl_class } in
                                                     Symtab.insert (op =) (name, mk (SOME (From.mk_univ (name, mk NONE) t))) t
                                                     end))))
*}

ML{*
fun in_local decl thy =
  thy
  |> Named_Target.init I ""
  |> decl
  |> Local_Theory.exit_global
*}

subsection{* ... *}

ML{*
datatype generation_mode = Gen_deep of unit OCL.ocl_deep_embed_input
                                     * (((bstring * bstring) * bstring) * Token.T list) list (* seri_args *)
                                     * bstring option (* filename_thy *)
                         | Gen_shallow of unit OCL.ocl_deep_embed_input

structure Data_gen = Theory_Data
  (type T = generation_mode list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true))

val code_expr_argsP = Scan.optional (@{keyword "("} |-- Args.parse --| @{keyword ")"}) []

val parse_deep =
  Scan.optional (((@{keyword "THEORY"} |-- Parse.name) -- (@{keyword "IMPORTS"} |-- Parse.name)) >> SOME) NONE
      -- Scan.optional (@{keyword "SECTION"} >> K true) false
      -- (* code_expr_inP *) Scan.repeat (@{keyword "in"} |-- Parse.!!! (Parse.name
        -- Scan.optional (@{keyword "module_name"} |-- Parse.name) ""
        -- Scan.optional (@{keyword "file"} |-- Parse.name) ""
        -- code_expr_argsP))
      -- Scan.optional (@{keyword "oid_start"} |-- Parse.nat) 0
      -- Scan.optional (@{keyword "thy_dir"} |-- Parse.name >> SOME) NONE

val parse_scheme = @{keyword "design"} >> K NONE || @{keyword "analysis"} >> K (SOME 1)

val mode = 
     @{keyword "deep"} |-- parse_scheme -- parse_deep >> (fn (design_analysis, ((((file_out_path_dep, disable_thy_output), seri_args), oid_start), filename_thy)) =>
                 let val _ = case (seri_args, filename_thy, file_out_path_dep) of
                      ([_], _, NONE) => warning ("Unknown filename, generating to stdout and ignoring " ^ (@{make_string} seri_args))
                    | (_, SOME t, NONE) => warning ("Unknown filename, generating to stdout and ignoring " ^ (@{make_string} t))
                    | _ => () in
                                            Gen_deep (OCL.OclDeepEmbed
                                                       ( From.from_bool (not disable_thy_output)
                                                       , From.from_option (From.from_pair From.from_string From.from_string) file_out_path_dep
                                                       , OCL.oidInit (From.from_internal_oid (From.from_nat oid_start))
                                                       , From.from_pair From.from_nat From.from_nat (0, 0)
                                                       , From.from_option From.from_nat design_analysis
                                                       , () ), seri_args, filename_thy) end)
  || @{keyword "shallow"} |-- parse_scheme >> (fn design_analysis => Gen_shallow (OCL.ocl_deep_embed_input_empty (From.from_option From.from_nat design_analysis)))

val gen_empty = ""

val () =
  Outer_Syntax.command @{command_spec "generation_mode"} "set the generating list"
    (Parse.$$$ "[" |-- Parse.list mode --| Parse.$$$ "]" >> (fn n =>
      Toplevel.theory (Data_gen.map (Symtab.map_default (gen_empty, n) (fn _ => n)))))
*}

subsection{* Deep (with reflection) *}

ML{*
structure Deep = struct

fun prep_destination "" = NONE
  | prep_destination "-" = (legacy_feature "drop \"file\" argument entirely instead of \"-\""; NONE)
  | prep_destination s = SOME (Path.explode s)

fun produce_code thy cs seris =
  let
    val (names_cs, (naming, program)) = Code_Thingol.consts_program thy false cs in
    map (fn (((target, module_name), some_path), args) =>
      (some_path, Code_Target.produce_code_for thy (*some_path*) target NONE module_name args naming program names_cs)) seris
  end

fun export_code_cmd raw_cs seris filename_thy thy =
  let
    fun absolute_path filename = Path.implode (Path.append (Thy_Load.master_directory thy) (Path.explode filename))
    val with_tmp_file =
      case seris of
        [] =>
        (fn f =>
          Isabelle_System.with_tmp_file "OCL_class_diagram_generator" "ml" (fn filename =>
          let val filename = Path.implode filename in
          (* export_code
               in OCaml module_name M (* file "" *) *)
          f [(((("OCaml", "M"), filename), []), filename)]
          end))
      | _ =>
        (fn f => f (map (fn x => (x, case x of (((_, _), filename), _) => absolute_path filename)) seris))
  in

  with_tmp_file (fn seris =>
    let val _ = Code_Target.export_code
        thy
        (Code_Target.read_const_exprs thy raw_cs)
        ((map o apfst o apsnd) prep_destination (map fst seris))
        val (out, _) = Isabelle_System.bash_output ("ocaml -w '-8' " ^ snd (hd seris)
                                                       ^ (case filename_thy of NONE => ""
                                                                             | SOME filename_thy => " " ^ absolute_path filename_thy)) in
    out end)

  end


fun mk_term ctxt s = fst (Scan.pass (Context.Proof ctxt) Args.term (Outer_Syntax.scan Position.none s))

fun mk_free ctxt s l =
  let val t_s = mk_term ctxt s in
  if Term.is_Free t_s then s else
    let val l = (s, "") :: l in
    mk_free ctxt (fst (hd (Term.variant_frees t_s l))) l
    end
  end

end
*}

subsection{* Shallow *}

ML{*
structure Shallow_conv = struct
 fun To_binding s = Binding.make (s, Position.none)
 val To_sbinding = To_binding o To_string
 fun s_of_rawty rawty = case rawty of
    OCL.Ty_base s => To_string s
  | OCL.Ty_apply (name, l) => (let val s = String.concatWith ", " (map s_of_rawty l) in
                                                 case l of [_] => s | _ => "(" ^ s ^ ")" end)
                              ^ " " ^
                              (s_of_rawty name)

val STR = I

val Unicode_mk_u = fn s => (STR ("\\" ^ "<" ^ s ^ ">"))
val Unicode_u_Rightarrow = Unicode_mk_u (STR "Rightarrow")
val Unicode_u_alpha = Unicode_mk_u (STR "alpha")
val Unicode_u_lambda = Unicode_mk_u (STR "lambda")
val Unicode_u_lfloor = Unicode_mk_u (STR "lfloor")
val Unicode_u_rfloor = Unicode_mk_u (STR "rfloor")
val Unicode_u_Longrightarrow = Unicode_mk_u (STR "Longrightarrow")

fun s_of_expr expr = let open OCL in
  case expr of
    Expr_case (e, l) => let val s1 =
 (s_of_expr e)
val s2 = (String.concatWith (STR "\n    | ") (map (fn (s1, s2) => String.concatWith (STR " ")
 [(s_of_expr s1), Unicode_u_Rightarrow, (s_of_expr s2)]) l)) in
(STR "(case " ^ s1 ^ " of " ^ s2 ^ ")") end
  | Expr_rewrite (e1, symb, e2) => String.concatWith (STR " ") [(s_of_expr e1), (To_string symb), (s_of_expr e2)]
  | Expr_basic l =>  (String.concatWith (STR " ") (map To_string l))
  | Expr_oid (tit, s) => To_string tit ^ Int.toString (case s of Oid s => To_nat s)
  | Expr_binop (e1, s, e2) => String.concatWith (STR " ") [(s_of_expr e1), (s_of_expr (Expr_basic [s])), (s_of_expr e2)]
  | Expr_annot (e, s) => (STR "(" ^ (s_of_expr e)  ^ "::" ^ (To_string s) ^ ")")
  | Expr_lambda (s, e) =>  (STR "(" ^ Unicode_u_lambda  ^ "" ^ (To_string s)  ^ ". " ^ (s_of_expr e) ^ ")")
  | Expr_lambdas (l, e) => (STR "(" ^ Unicode_u_lambda ^ "" ^ (String.concatWith (STR " ") (map To_string l)) ^ ". " ^ (s_of_expr e) ^ ")")
  | Expr_lambdas0 (e1, e2) => (STR "(" ^ Unicode_u_lambda ^ "" ^ (s_of_expr e1) ^ ". " ^ (s_of_expr e2) ^ ")")
  | Expr_function l =>  (STR "(" ^ Unicode_u_lambda  ^ " " ^ (String.concatWith (STR "\n    | ") (map (fn (s1, s2) => String.concatWith (STR " ") [ (s_of_expr s1),Unicode_u_Rightarrow, (s_of_expr s2)]) l)) ^ ")")
  (*| Expr_apply s [e] => sprintf2 (STR "(" ^ s ^ " " ^ s ^ ")") (To_string s) (s_of_expr e)*)
  | Expr_apply (s, l) =>  let val s1 = (To_string s) val s2 = (String.concatWith (STR " ") (map (fn e => (STR "(" ^ (s_of_expr e) ^ ")") ) l)) in
(STR "(" ^ s1 ^ " " ^ s2 ^ ")") end
  | Expr_applys (e, l) => let val s1 = (s_of_expr e) val s2 = (String.concatWith (STR " ") (map (fn e => (STR "(" ^ (s_of_expr e) ^ ")") ) l)) in
 (STR "((" ^ s1 ^ ") " ^ s2 ^ ")") end
  | Expr_some (Expr_function l) => let val s1 = Unicode_u_lfloor val s2 = Unicode_u_lambda val s3 = (String.concatWith (STR "\n    | ") (map (fn (s1, s2) => String.concatWith (STR " ") [ (s_of_expr s1), Unicode_u_Rightarrow, (s_of_expr s2)]) l)) val s4 = Unicode_u_rfloor in
(STR "" ^ s1 ^ "" ^ s2 ^ " " ^ s3 ^ "" ^ s4 ^ "") end
  | Expr_some e => String.concatWith (STR "") [Unicode_u_lfloor, (s_of_expr e), Unicode_u_rfloor]
  | Expr_postunary (e1, e2) =>  (s_of_expr e1) ^ " " ^ (s_of_expr e2)
  | Expr_preunary (e1, e2) =>  (s_of_expr e1) ^ " " ^ (s_of_expr e2)
  | Expr_warning_parenthesis e =>  (STR "(" ^ (s_of_expr e) ^ ")")
  | Expr_parenthesis e => (STR "(" ^ (s_of_expr e) ^ ")")
end

fun simp_tac f = Method.Basic (fn ctxt => SIMPLE_METHOD (asm_full_simp_tac (f ctxt) 1))

fun m_of_ntheorem ctxt s = let open OCL in case s of
    Thm_str s => Proof_Context.get_thm ctxt (To_string s)
  | Thm_strs (s, n) => List.nth (Proof_Context.get_thms ctxt (To_string s), To_nat n)
  | Thm_THEN (e1, e2) => m_of_ntheorem ctxt e1 RSN (1, m_of_ntheorem ctxt e2)
  | Thm_simplified (e1, e2) => asm_full_simplify (clear_simpset ctxt addsimps [m_of_ntheorem ctxt e2]) (m_of_ntheorem ctxt e1)
  | Thm_OF (e1, e2) => [m_of_ntheorem ctxt e2] MRS m_of_ntheorem ctxt e1
  | Thm_where (nth, l) => read_instantiate ctxt (map (fn (var, expr) => ((To_string var, 0), s_of_expr expr)) l) (m_of_ntheorem ctxt nth)
  | Thm_symmetric s => m_of_ntheorem ctxt (Thm_THEN (s, Thm_str (From.from_string "sym")))
  | Thm_of (nth, l) =>
      let val thm = m_of_ntheorem ctxt nth
          fun zip_vars _ [] = []
            | zip_vars (_ :: xs) (NONE :: rest) = zip_vars xs rest
            | zip_vars ((x, _) :: xs) (SOME t :: rest) = (x, t) :: zip_vars xs rest
            | zip_vars [] _ = error "More instantiations than variables in theorem" in
      read_instantiate ctxt (map (fn (v, expr) => (v, s_of_expr expr))
                                 (zip_vars (rev (Term.add_vars (Thm.full_prop_of thm) []))
                                           (map SOME l))) thm
      end
end

fun m_of_tactic expr = let open OCL val f_fold = fold open Method in case expr of
    Tac_rule s => Basic (fn ctxt => rule [m_of_ntheorem ctxt s])
  | Tac_erule s => Basic (fn ctxt => erule 0 [m_of_ntheorem ctxt s])
  | Tac_elim s => Basic (fn ctxt => elim [m_of_ntheorem ctxt s])
  | Tac_subst s => Basic (fn ctxt => SIMPLE_METHOD' (EqSubst.eqsubst_tac ctxt [0] [m_of_ntheorem ctxt s]))
  | Tac_insert l => Basic (fn ctxt => insert (map (m_of_ntheorem ctxt) l))
  | Tac_plus t => Repeat1 (Then (map m_of_tactic t))
  | Tac_simp => simp_tac I
  | Tac_simp_add l => simp_tac (fn ctxt => ctxt addsimps (map (Proof_Context.get_thm ctxt o To_string) l))
  | Tac_simp_only l => simp_tac (fn ctxt => clear_simpset ctxt addsimps (map (m_of_ntheorem ctxt) l))
  | Tac_simp_all => m_of_tactic (Tac_plus [Tac_simp])
  | Tac_simp_all_add s => m_of_tactic (Tac_plus [Tac_simp_add [s]])
  | Tac_auto_simp_add l => Basic (fn ctxt => SIMPLE_METHOD (auto_tac (ctxt addsimps (map (Proof_Context.get_thm ctxt o To_string) l))))
  | Tac_auto_simp_add_split (l_simp, l_split) =>
      Basic (fn ctxt => SIMPLE_METHOD (auto_tac (f_fold (fn (f, l) => f_fold f l)
              [(Simplifier.add_simp, map (m_of_ntheorem ctxt) l_simp)
              ,(Splitter.add_split, map (Proof_Context.get_thm ctxt o To_string) l_split)]
              ctxt)))
  | Tac_rename_tac l => Basic (K (SIMPLE_METHOD' (rename_tac (map To_string l))))
  | Tac_case_tac e => Basic (fn ctxt => SIMPLE_METHOD' (Induct_Tacs.case_tac ctxt (s_of_expr e)))
end

end

structure Shallow_ml = struct open Shallow_conv
fun perform_instantiation thy tycos vs f_eq add_def tac (*add_eq_thms*) =
    thy
    |> Class.instantiation (tycos, vs, f_eq)
    |> fold_map add_def tycos
    |-> Class.prove_instantiation_exit_result (map o Morphism.thm) (fn _ => tac)
(*    |-> fold Code.del_eqn
    |> fold add_eq_thms tycos*)
    |-> K I
local
fun read_abbrev b ctxt raw_rhs =
  let
    val rhs = Proof_Context.read_typ_syntax (ctxt |> Proof_Context.set_defsort []) raw_rhs;
    val ignored = Term.fold_atyps_sorts (fn (_, []) => I | (T, _) => insert (op =) T) rhs [];
    val _ =
      if null ignored then ()
      else Context_Position.if_visible ctxt warning
        ("Ignoring sort constraints in type variables(s): " ^
          commas_quote (map (Syntax.string_of_typ ctxt) (rev ignored)) ^
          "\nin type abbreviation " ^ (case b of NONE => "" | SOME b => Binding.print b));
  in rhs end
in
fun read_typ_syntax b = read_abbrev b
                      o Proof_Context.init_global
end

fun s_of_tactic l = (Method.Then (map m_of_tactic l), (Position.none, Position.none))

val apply_results = fn OCL.App l => (fn st => st |> (Proof.apply_results (s_of_tactic l)) |> Seq.the_result "")
                     | OCL.App_using l => fn st =>
                         let val ctxt = Proof.context_of st in
                         Proof.using [map (fn s => ([m_of_ntheorem ctxt s], [])) l] st
                         end

fun global_terminal_proof o_by = let open OCL in case o_by of
   Tacl_done => Proof.global_done_proof
 | Tacl_sorry => Proof.global_skip_proof true
 | Tacl_by l_apply => Proof.global_terminal_proof (s_of_tactic l_apply, NONE)
end
end

structure Shallow_main = struct open Shallow_conv open Shallow_ml
val OCL_main = let open OCL in (*let val f = *)fn
  Thy_dataty (Datatype (n, l)) =>
    (snd oo Datatype.add_datatype_cmd Datatype_Aux.default_config)
      [((To_sbinding n, [], NoSyn),
       map (fn (n, l) => (To_sbinding n, map (fn OCL.Opt o_ => To_string o_ ^ " option"
                                             |   Raw o_ => To_string o_) l, NoSyn)) l)]
| Thy_ty_synonym (Type_synonym (n, l)) =>
    (fn thy =>
     let val s_bind = To_sbinding n in
     (snd o Typedecl.abbrev_global (s_bind, [], NoSyn)
                                   (read_typ_syntax (SOME s_bind) thy (s_of_rawty l))) thy
     end)
| Thy_instantiation_class (Instantiation (n, n_def, expr)) =>
    (fn thy =>
     let val name = To_string n in
     perform_instantiation
       thy
       [ let val Type (s, _) = (read_typ_syntax NONE thy name) in s end ]
       []
       (Syntax.read_sort (Proof_Context.init_global thy) "object")
       (fn _ => fn thy =>
        let val ((_, (_, ty)), thy) = Specification.definition_cmd
           (NONE, ((To_binding (To_string n_def ^ "_" ^ name ^ "_def"), []), s_of_expr expr)) false thy in
         (ty, thy)
        end)
       (fn thms => Class.intro_classes_tac [] THEN ALLGOALS (Proof_Context.fact_tac thms))
     end)
| Thy_defs_overloaded (Defs_overloaded (n, e)) =>
    Isar_Cmd.add_defs ((false, true), [((To_sbinding n, s_of_expr e), [])])
| Thy_consts_class (Consts_raw (n, ty_out1, ty_out2, symb)) =>
    Sign.add_consts [( To_sbinding n
                     , String.concatWith " " [ (s_of_rawty ty_out1), Unicode_u_Rightarrow, (s_of_rawty ty_out2) ]
                     , Mixfix ("(_) " ^ To_string symb, [], 1000))]
| Thy_definition_hol def =>
    let val (def, e) = case def of
        Definition e => (NONE, e)
      | Definition_abbrev (name, (abbrev, prio), e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix ("(1" ^ s_of_expr abbrev ^ ")", [], To_nat prio)), e)
      | Definition_abbrev0 (name, abbrev, e) =>
          (SOME ( To_sbinding name
                , NONE
                , Mixfix ("(" ^ s_of_expr abbrev ^ ")", [], 1000)), e) in
    in_local (snd o Specification.definition_cmd (def, ((@{binding ""}, []), s_of_expr e)) false)
    end
| Thy_lemmas_simp (Lemmas_simp (s, l)) =>
    in_local (fn lthy => (snd o Specification.theorems Thm.lemmaK
      [((To_sbinding s, map (Attrib.intern_src (Proof_Context.theory_of lthy))
                          [Args.src (("simp", []), Position.none), Args.src (("code_unfold", []), Position.none)]),
        map (fn x => ([m_of_ntheorem lthy x], [])) l)]
      []
      false) lthy)
| Thy_lemma_by (Lemma_by (n, l_spec, l_apply, o_by)) =>
      in_local (fn lthy =>
           Specification.theorem_cmd Thm.lemmaK NONE (K I)
             (@{binding ""}, []) [] [] (Element.Shows [((To_sbinding n, [])
                                                       ,[((String.concatWith (STR " " ^ Unicode_u_Longrightarrow ^ " ")
                                                             (map s_of_expr l_spec)), [])])])
             false lthy
        |> fold (apply_results o OCL.App) l_apply
        |> global_terminal_proof o_by)
| Thy_lemma_by (Lemma_by_assum (n, l_spec, concl, l_apply, o_by)) =>
      in_local (fn lthy =>
           Specification.theorem_cmd Thm.lemmaK NONE (K I)
             (To_sbinding n, [])
             []
             (map (fn (n, e) => Element.Assumes [((To_sbinding n, []), [(s_of_expr e, [])])]) l_spec)
             (Element.Shows [((@{binding ""}, []),[(s_of_expr concl, [])])])
             false lthy
        |> fold apply_results l_apply
        |> global_terminal_proof o_by)
| Thy_section_title _ => I
(*in fn t => fn thy => f t thy handle ERROR s => (warning s; thy)
 end*)
end
end
(*val _ = print_depth 100*)
*}

subsection{* Outer Syntax: Class.end *}

ML{*

fun outer_syntax_command cmd_spec cmd_descr parser get_oclclass =
  let val i_of_write_file =
    let val a = OCL.i_apply
      ; val b = I in
    OCL.ap1 a (From.from_term @{context} @{term "write_file"})
      (OCL.i_of_ocl_deep_embed_input a b OCL.i_of_ocl_deep_embed_ast)
    end in
  Outer_Syntax.command cmd_spec cmd_descr
    (parser >> (fn name =>
      Toplevel.theory (fn thy =>
        let val (ocl, thy) =
        OCL.fold_list

          let val get_oclclass = get_oclclass name in
          fn Gen_deep (ocl, seri_args, filename_thy) =>
              let fun def s = in_local (snd o Specification.definition_cmd (NONE, ((@{binding ""}, []), s)) false) in
              fn thy0 =>
                let val name_main = Deep.mk_free (Proof_Context.init_global thy0) "main" []
                  ; val obj = get_oclclass thy0 in
                thy0 |> def (String.concatWith " " (  name_main
                                                  :: "="
                                                  :: (To_string (i_of_write_file
(case ocl of OCL.OclDeepEmbed (disable_thy_output, file_out_path_dep, oid_start, output_position, design_analysis, ()) =>
  OCL.OclDeepEmbed ( disable_thy_output, file_out_path_dep, oid_start, output_position, design_analysis, obj ))))
                                                  :: []))
                     |> Deep.export_code_cmd [name_main] seri_args filename_thy
                     |> (fn s =>
                          let val _ = writeln
                                (case seri_args of [] =>
                                  String.concat (map ((fn s => s ^ "\n") o Active.sendback_markup [Markup.padding_command] o trim_line)
                                    (String.tokens (fn c => From.from_char c = OCL.char_escape) s))
                                | _ => s) in
                          (Gen_deep (OCL.fold_thy_deep obj ocl, seri_args, filename_thy), thy0) end)
                end
              end
           | Gen_shallow ocl => fn thy =>
             let val (ocl, thy) = OCL.fold_thy Shallow_main.OCL_main (get_oclclass thy) (ocl, thy) in
             (Gen_shallow ocl, thy)
             end
          end

          let val SOME l = Symtab.lookup (Data_gen.get thy) gen_empty in l end
          thy
        in
        Data_gen.map (Symtab.update (gen_empty, ocl)) thy end)))
end

val () =
  outer_syntax_command @{command_spec "Class.end"} "Class generation"
    Parse.binding
    (fn name => fn thy =>
       let val SOME { attr_base = attr_base
                    , attr_object = attr_object
                    , child = child
                    , ocl_class = SOME ocl_class } = Symtab.lookup (Data.get thy) (Binding.name_of name) in
       OCL.OclAstClass ocl_class end)
*}

section{* Outer Syntax: Instance *}

ML{*

datatype ocl_term = OclTerm of binding
                  | OclOid of int
                  | OclTmp (* FIXME: to remove *)

datatype 'a ocl_l_attr = Ocl_l_attr of 'a
                    | Ocl_l_attr_cast of 'a ocl_prop * binding

and 'a ocl_prop = Ocl_prop of 'a ocl_l_attr (* l_inh *) * 'a (* l_attr *)

datatype ocl_prop_main = Ocl_prop_main of ((binding * ocl_term) list) ocl_prop

val list_attr0 = Parse.list (Parse.binding -- (Parse.$$$ "=" |--
  (Parse.binding >> OclTerm
  || (@{keyword "self"} |-- Parse.nat) >> OclOid)))
val list_attr = Parse.$$$ "[" |-- Parse.!!! (list_attr0
  -- (Parse.$$$ "]" >> (fn _ => (NONE : binding option))))
val list_attr_cast = (Parse.$$$ "(" -- Parse.$$$ "[") |-- Parse.!!! (list_attr0
  -- ((Parse.$$$ "]" -- Parse.$$$ "::") |-- (Parse.binding >> SOME) --| Parse.$$$ ")"))

fun annot_ty f = Parse.$$$ "(" |-- f --| Parse.$$$ "::" -- Parse.binding --| Parse.$$$ ")"
val list_attr0_tmp = Parse.$$$ "[" |-- Parse.list ( ((Parse.binding -- (Parse.$$$ "=" |--
  (Parse.binding >> OclTerm
  || (@{keyword "self"} |-- Parse.nat) >> OclOid))) || (Parse.underscore >> K (@{binding ""}, OclTmp)))) --| Parse.$$$ "]"
fun list_attr_tmp s = ((Parse.$$$ "(" |-- Parse.list
  (Parse.!!! ( list_attr0_tmp >> Ocl_l_attr
  || (annot_ty list_attr_tmp >> Ocl_l_attr_cast) ))
  --| Parse.$$$ ")" >> (fn (x1 :: Ocl_l_attr x2 :: _) => Ocl_prop (x1, x2)))) s

val () =
  outer_syntax_command @{command_spec "Define_int"} ""
    (Parse.$$$ "[" |-- Parse.list Parse.number --| Parse.$$$ "]")
    (fn l_int => fn _ =>
      OCL.OclAstDefInt (OCL.OclDefI (map From.from_string l_int)))

datatype state_content = ST_l_attr of (binding * ocl_term) list * binding option
                       | ST_skip
                       | ST_binding of binding

datatype state_content_tmp = STtmp_l_attr of (binding * ocl_term) list ocl_prop * binding (* ty *)
                       | STtmp_empty
                       | STtmp_binding of binding (* name *) * binding (* ty *)

val state_parse =
  (@{keyword "defines"} -- Parse.$$$ "[" |-- Parse.list
      (  (list_attr || list_attr_cast) >> ST_l_attr
      || Parse.binding >> ST_binding) --| Parse.$$$ "]")
  || @{keyword "skip"} >> K [ST_skip]

val state_parse_tmp =
  (@{keyword "defines"} -- Parse.$$$ "[" |-- Parse.list
      (  annot_ty list_attr_tmp >> STtmp_l_attr
      || annot_ty Parse.binding >> STtmp_binding) --| Parse.$$$ "]")
  || @{keyword "skip"} >> K [STtmp_empty]

val () =
  Outer_Syntax.command @{command_spec "Define_state"} ""
    ((Parse.binding --| @{keyword "="} -- Parse.$$$ "[" |-- (Parse.list state_parse >> List.concat) --| Parse.$$$ "]") >> (fn n =>
      let val _ = writeln (@{make_string} n) in
      Toplevel.theory (fn thy => thy)
      end))

val inst1 = Parse.binding --| @{keyword "::"} -- Parse.binding --| @{keyword "="} -- (list_attr || list_attr_cast)
val inst1_tmp = Parse.binding --| @{keyword "::"} -- Parse.binding --| @{keyword "="} -- list_attr_tmp

val () =
  Outer_Syntax.command @{command_spec "Instance"} ""
    ((inst1 -- Scan.repeat (@{keyword "and"} |-- inst1)) >> (fn n =>
      let val _ = writeln (@{make_string} n) in
      Toplevel.theory (fn thy => thy)
      end))

local
  fun get_oclinst l _ =
    OCL.OclInstance (map (fn ((name,typ), Ocl_prop (l_inh, l_attr)) =>
        let val f = map (fn (attr, ocl) => (From.from_binding attr,
                      case ocl of OclTerm s => OCL.Shall_str (From.from_binding s)
                                | OclOid n => OCL.Shall_self (From.from_internal_oid (From.from_nat n))
                                | OclTmp => OCL.Shall_tmp))
            val l_inh = case l_inh of Ocl_l_attr l => OCL.OclNoInh (f l)
                                    | Ocl_l_attr_cast (Ocl_prop (Ocl_l_attr l_inh, l_attr), b) => OCL.OclInh (f l_inh, f l_attr, From.from_binding b) in
        OCL.OclInst
          (From.from_binding name, From.from_binding typ, l_inh, f l_attr) end) l)
in

val () =
  outer_syntax_command @{command_spec "Instance_tmp"} ""
    (inst1_tmp -- Scan.repeat (@{keyword "and"} |-- inst1_tmp))
    (fn (x, xs) => fn thy =>
      OCL.OclAstInstance (get_oclinst (x :: xs) thy))

val () =
  outer_syntax_command @{command_spec "Define_state_tmp"} ""
    (Parse.binding --| (@{keyword "="} -- Parse.$$$ "[") -- (Parse.list state_parse_tmp >> List.concat) --| Parse.$$$ "]")
    (fn (name, l) => fn thy =>
      OCL.OclAstDefState (OCL.OclDefSt (From.from_binding name,
        map (fn STtmp_l_attr (l, ty) => OCL.OclDefCoreAdd (case get_oclinst [((ty, ty), l)] thy of OCL.OclInstance [x] => x)
              | STtmp_empty => OCL.OclDefCoreSkip
              | STtmp_binding (b1, b2) => OCL.OclDefCoreBinding (From.from_binding b1, From.from_binding b2)) l)))
end

(*val _ = print_depth 100*)
*}

Instance X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 :: Person = [ salary = 1300 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 :: Person = [ salary = 1800 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 :: Person = [ ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 :: Person = [ salary = 2900 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 :: Person = [ salary = 3500 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 :: Person = [ salary = 2500 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 :: OclAny = ([ salary = 3200 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 ] :: Person)
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 :: OclAny = [ ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 :: Person = [ salary = 0 ]

Define_state \<sigma>\<^sub>1 =
  [ defines [ [ salary = 1000 , boss = self 1 ]
            , [ salary = 1200 ] ]
  , skip
  , defines [ [ salary = 2600 , boss = self 4 ]
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5
            , [ salary = 2300 , boss = self 3 ] ]
  , skip
  , skip
  , defines [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 ] ]

Define_state \<sigma>\<^sub>1' =
  [ defines [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 ]
  , skip
  , defines [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8
            , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 ] ]

Define_state \<sigma>\<^sub>0 = []

end
