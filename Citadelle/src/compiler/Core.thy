(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Core.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Saclay, Univ. Paris-Sud, France
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

section\<open>General Environment for the Translation: Conclusion\<close>

theory  Core
imports "core/Floor1_enum"
        "core/Floor1_infra"
        "core/Floor1_astype"
        "core/Floor1_istypeof"
        "core/Floor1_iskindof"
        "core/Floor1_allinst"
        "core/Floor1_access"
        "core/Floor1_examp"
        "core/Floor2_examp"
        "core/Floor1_ctxt"
        "core/Floor2_ctxt"
begin

subsection\<open>Preliminaries\<close>

datatype ('a, 'b) embedding = Embed_theories "('a \<Rightarrow> 'b \<Rightarrow> all_meta list \<times> 'b) list"
                            | Embed_locale "'a \<Rightarrow> 'b \<Rightarrow> semi__locale \<times> 'b"
                                           "('a \<Rightarrow> 'b \<Rightarrow> semi__theory list \<times> 'b) list"
                                           "('a \<Rightarrow> 'b \<Rightarrow> all_meta list \<times> 'b) list"

type_synonym 'a embedding' = "('a, compiler_env_config) embedding" (* polymorphism weakening needed by code_reflect *)

definition "L_fold f =
 (let f_locale = \<lambda>loc_data l.
    f (\<lambda>a b.
          let (loc_data, b) = loc_data a b
            ; (l, b) = List.fold (\<lambda>f0. \<lambda>(l, b) \<Rightarrow> let (x, b) = f0 a b in (x # l, b)) l ([], b) in
          ([META_semi__theories (Theories_locale loc_data (rev l))], b)) in
  \<lambda> Embed_theories l \<Rightarrow> List.fold f l
  | Embed_locale loc_data l_loc l_th \<Rightarrow> List.fold f l_th o f_locale loc_data l_loc)"

subsection\<open>Assembling Translations\<close>

definition "section_aux n s = start_map' (\<lambda>_. [ O.section (Section n s) ])"
definition "section = section_aux 0"
definition "subsection = section_aux 1"
definition "subsubsection = section_aux 2"
definition "txt f = start_map'''' O.text o (\<lambda>_ design_analysis. [Text (f design_analysis)])"
definition "txt' s = txt (\<lambda>_. s)"
definition "txt'' = txt' o S.flatten"
definition "txt''d s = txt (\<lambda> Gen_only_design \<Rightarrow> S.flatten s | _ \<Rightarrow> \<open>\<close>)"
definition "txt''a s = txt (\<lambda> Gen_only_design \<Rightarrow> \<open>\<close> | _ \<Rightarrow> S.flatten s)"

definition' thy_class ::
  (* polymorphism weakening needed by code_reflect *)
  "_ embedding'" where \<open>thy_class =
  (let subsection_def = subsection \<open>Definition\<close>
     ; subsection_cp = subsection \<open>Context Passing\<close>
     ; subsection_exec = subsection \<open>Execution with Invalid or Null as Argument\<close>
     ; subsection_defined = subsection \<open>Validity and Definedness Properties\<close>
     ; subsection_up = subsection \<open>Up Down Casting\<close>
     ; subsection_const = subsection \<open>Const\<close> in
  (Embed_theories o L.flatten)
          [ [ print_infra_enum_synonym ]
            , [ txt''d [ \<open>
   \label{ex:employee-design:uml} \<close> ]
            , txt''a [ \<open>
   \label{ex:employee-analysis:uml} \<close> ]
            , section \<open>Introduction\<close>
            , txt'' [ \<open>

  For certain concepts like classes and class-types, only a generic
  definition for its resulting semantics can be given. Generic means,
  there is a function outside HOL that ``compiles'' a concrete,
  closed-world class diagram into a ``theory'' of this data model,
  consisting of a bunch of definitions for classes, accessors, method,
  casts, and tests for actual types, as well as proofs for the
  fundamental properties of these operations in this concrete data
  model. \<close> ]
            , txt'' [ \<open>
   Such generic function or ``compiler'' can be implemented in
  Isabelle on the ML level.  This has been done, for a semantics
  following the open-world assumption, for UML 2.0
  in~\cite{brucker.ea:extensible:2008-b, brucker:interactive:2007}. In
  this paper, we follow another approach for UML 2.4: we define the
  concepts of the compilation informally, and present a concrete
  example which is verified in Isabelle/HOL. \<close> ]
            , subsection \<open>Outlining the Example\<close>
            , txt''d [ \<open>
   We are presenting here a ``design-model'' of the (slightly
modified) example Figure 7.3, page 20 of
the OCL standard~\cite{omg:ocl:2012}. To be precise, this theory contains the formalization of
the data-part covered by the UML class model (see \autoref{fig:person}):\<close> ]
            , txt''a [ \<open>
   We are presenting here an ``analysis-model'' of the (slightly
modified) example Figure 7.3, page 20 of
the OCL standard~\cite{omg:ocl:2012}.
Here, analysis model means that associations
were really represented as relation on objects on the state---as is
intended by the standard---rather by pointers between objects as is
done in our ``design model'' (see \autoref{ex:employee-design:uml}).
To be precise, this theory contains the formalization of the data-part
covered by the UML class model (see \autoref{fig:person-ana}):\<close> ]
            , txt''d [ \<open>

\begin{figure}
  \centering\scalebox{.3}{\includegraphics{figures/person.png}}%
  \caption{A simple UML class model drawn from Figure 7.3,
  page 20 of~\cite{omg:ocl:2012}. \label{fig:person}}
\end{figure}
\<close> ]
            , txt''a [ \<open>

\begin{figure}
  \centering\scalebox{.3}{\includegraphics{figures/person.png}}%
  \caption{A simple UML class model drawn from Figure 7.3,
  page 20 of~\cite{omg:ocl:2012}. \label{fig:person-ana}}
\end{figure}
\<close> ]
            , txt'' [ \<open>
   This means that the association (attached to the association class
\inlineocl{EmployeeRanking}) with the association ends \inlineocl+boss+ and \inlineocl+employees+ is implemented
by the attribute  \inlineocl+boss+ and the operation \inlineocl+employees+ (to be discussed in the OCL part
captured by the subsequent theory).
\<close> ]
            , section \<open>Example Data-Universe and its Infrastructure\<close>
            (*, txt'' [ \<open>
   Ideally, the following is generated automatically from a UML class model.  \<close> ]
            *), txt'' [ \<open>
   Our data universe  consists in the concrete class diagram just of node's,
and implicitly of the class object. Each class implies the existence of a class
type defined for the corresponding object representations as follows: \<close> ]
            (*, print_latex_infra_datatype_class*)
            , print_infra_datatype_class
            , txt'' [ \<open>
   Now, we construct a concrete ``universe of OclAny types'' by injection into a
sum type containing the class types. This type of OclAny will be used as instance
for all respective type-variables. \<close> ]
            , print_infra_datatype_universe
            , txt'' [ \<open>
   Having fixed the object universe, we can introduce type synonyms that exactly correspond
to OCL types. Again, we exploit that our representation of OCL is a ``shallow embedding'' with a
one-to-one correspondance of OCL-types to types of the meta-language HOL. \<close> ]
            , print_infra_type_synonym_class
            , print_infra_type_synonym_class_higher
            , print_infra_type_synonym_class_rec
            , print_infra_enum_syn
            (*, txt'' [ \<open>
   Just a little check: \<close> ]
            *), txt'' [ \<open>
   To reuse key-elements of the library like referential equality, we have
to show that the object universe belongs to the type class ``oclany,'' \ie,
 each class type has to provide a function @{term oid_of} yielding the object id (oid) of the object. \<close> ]
            , print_infra_instantiation_class
            , print_infra_instantiation_universe

            , section \<open>Instantiation of the Generic Strict Equality\<close>
            , txt'' [ \<open>
   We instantiate the referential equality
on @{text "Person"} and @{text "OclAny"} \<close> ]
            , print_instantia_def_strictrefeq
            , print_instantia_lemmas_strictrefeq
            , txt'' [ \<open>
   For each Class \emph{C}, we will have a casting operation \inlineocl{.oclAsType($C$)},
   a test on the actual type \inlineocl{.oclIsTypeOf($C$)} as well as its relaxed form
   \inlineocl{.oclIsKindOf($C$)} (corresponding exactly to Java's \verb+instanceof+-operator.
\<close> ]
            , txt'' [ \<open>
   Thus, since we have two class-types in our concrete class hierarchy, we have
two operations to declare and to provide two overloading definitions for the two static types.
\<close> ] ]

          , L.flatten (L.map (\<lambda>(title, body_def, body_cp, body_exec, body_defined, body_up, body_const).
              section title # L.flatten [ subsection_def # body_def
                                      , subsection_cp # body_cp
                                      , subsection_exec # body_exec
                                      , subsection_defined # body_defined
                                      , subsection_up # body_up
                                      , subsection_const # body_const ])
          [ (\<open>OclAsType\<close>,
            [ print_astype_consts
            , print_astype_class
            , print_astype_from_universe
            , print_astype_lemmas_id ]
            , [ print_astype_lemma_cp
            , print_astype_lemmas_cp ]
            , [ print_astype_lemma_strict
            , print_astype_lemmas_strict ]
            , [ print_astype_defined ]
            , [ print_astype_up_d_cast0
            , print_astype_up_d_cast
            , print_astype_d_up_cast ]
            , [ print_astype_lemma_const
              , print_astype_lemmas_const ])

          , (\<open>OclIsTypeOf\<close>,
            [ print_istypeof_consts
            , print_istypeof_class
            , print_istypeof_from_universe
            , print_istypeof_lemmas_id ]
            , [ print_istypeof_lemma_cp
            , print_istypeof_lemmas_cp ]
            , [ print_istypeof_lemma_strict
            , print_istypeof_lemmas_strict ]
            , [ print_istypeof_defined
            , print_istypeof_defined' ]
            , [ print_istypeof_up_larger
            , print_istypeof_up_d_cast ]
            , [])

          , (\<open>OclIsKindOf\<close>,
            [ print_iskindof_consts
            , print_iskindof_class
            , print_iskindof_from_universe
            , print_iskindof_lemmas_id ]
            , [ print_iskindof_lemma_cp
            , print_iskindof_lemmas_cp ]
            , [ print_iskindof_lemma_strict
            , print_iskindof_lemmas_strict ]
            , [ print_iskindof_defined
            , print_iskindof_defined' ]
            , [ print_iskindof_up_eq_asty
            , print_iskindof_up_larger
            , print_iskindof_up_istypeof_unfold
            , print_iskindof_up_istypeof
            , print_iskindof_up_d_cast ]
            , []) ])

          , [ section \<open>OclAllInstances\<close>
            , txt'' [ \<open>
   To denote OCL-types occuring in OCL expressions syntactically---as, for example,  as
``argument'' of \inlineisar{oclAllInstances()}---we use the inverses of the injection
functions into the object universes; we show that this is sufficient ``characterization.'' \<close> ]
            , print_allinst_def_id
            , print_allinst_lemmas_id
            , print_allinst_astype
            , print_allinst_exec
            , subsection \<open>OclIsTypeOf\<close>
            , print_allinst_istypeof_pre
            , print_allinst_istypeof
            , subsection \<open>OclIsKindOf\<close>
            , print_allinst_iskindof_eq
            , print_allinst_iskindof_larger

            , section \<open>The Accessors\<close>
            , txt''d [ \<open>
  \label{sec:edm-accessors}\<close> ]
            , txt''a [ \<open>
  \label{sec:eam-accessors}\<close> ]
            (*, txt'' [ \<open>
   Should be generated entirely from a class-diagram. \<close> ]
            *), subsection_def
            , txt''a [ \<open>
   We start with a oid for the association; this oid can be used
in presence of association classes to represent the association inside an object,
pretty much similar to the \inlineisar+Employee_DesignModel_UMLPart+, where we stored
an \verb+oid+ inside the class as ``pointer.'' \<close> ]
            , print_access_oid_uniq_ml
            , print_access_oid_uniq
            , txt''a [ \<open>
   From there on, we can already define an empty state which must contain
for $\mathit{oid}_{Person}\mathcal{BOSS}$ the empty relation (encoded as association list, since there are
associations with a Sequence-like structure).\<close> ]
            , print_access_eval_extract
            , txt''a [ \<open>
   The @{text pre_post}-parameter is configured with @{text fst} or
@{text snd}, the @{text to_from}-parameter either with the identity @{term id} or
the following combinator @{text switch}: \<close> ]
            , print_access_choose_ml
            , print_access_choose
            , print_access_deref_oid
            , print_access_deref_assocs
            , txt'' [ \<open>
   pointer undefined in state or not referencing a type conform object representation \<close> ]
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
            , subsection \<open>Representation in States\<close>
            , print_access_def_mono
            , print_access_is_repr
            , print_access_repr_allinst

            , section \<open>A Little Infra-structure on Example States\<close>
            , txt''d [ \<open>

The example we are defining in this section comes from the figure~\ref{fig:edm1_system-states}.
\begin{figure}
\includegraphics[width=\textwidth]{figures/pre-post.pdf}
\caption{(a) pre-state $\sigma_1$ and
  (b) post-state $\sigma_1'$.}
\label{fig:edm1_system-states}
\end{figure}
\<close> ]
            , txt''a [ \<open>

The example we are defining in this section comes from the figure~\ref{fig:eam1_system-states}.
\begin{figure}
\includegraphics[width=\textwidth]{figures/pre-post.pdf}
\caption{(a) pre-state $\sigma_1$ and
  (b) post-state $\sigma_1'$.}
\label{fig:eam1_system-states}
\end{figure}
\<close> ]
            , print_examp_def_st_defs
            , print_astype_lemmas_id2 ] ])\<close>

definition "thy_enum_flat = Embed_theories []"
definition "thy_enum = Embed_theories [ print_enum ]"
definition "thy_class_synonym = Embed_theories []"
definition "thy_class_flat = Embed_theories []"
definition "thy_association = Embed_theories []"
definition "thy_instance = Embed_theories 
                             [ print_examp_instance_defassoc_typecheck_var
                             , print_examp_instance_defassoc
                             , print_examp_instance
                             , print_examp_instance_defassoc_typecheck ]"
definition "thy_def_base_l = Embed_theories [ print_examp_oclbase ]"
definition "thy_def_state = (\<lambda> Floor1 \<Rightarrow> Embed_theories 
                                           [ Floor1_examp.print_examp_def_st_typecheck_var
                                           , Floor1_examp.print_examp_def_st1 ]
                             | Floor2 \<Rightarrow> Embed_locale
                                           Floor2_examp.print_examp_def_st_locale
                                           [ Floor2_examp.print_examp_def_st2
                                           , Floor2_examp.print_examp_def_st_dom
                                           , Floor2_examp.print_examp_def_st_dom_lemmas
                                           , Floor2_examp.print_examp_def_st_perm
                                           , Floor2_examp.print_examp_def_st_allinst
                                           , Floor2_examp.print_examp_def_st_defassoc_typecheck ]
                                           [ Floor2_examp.print_examp_def_st_def_interp ])"
definition "thy_def_transition = (\<lambda> Floor1 \<Rightarrow> Embed_theories 
                                              [ Floor1_examp.print_transition ]
                                | Floor2 \<Rightarrow> Embed_locale
                                              Floor2_examp.print_transition_locale
                                              [ Floor2_examp.print_transition_interp
                                              , Floor2_examp.print_transition_def_state
                                              , Floor2_examp.print_transition_wff
                                              , Floor2_examp.print_transition_where ]
                                              [ Floor2_examp.print_transition_def_interp
                                              , Floor2_examp.print_transition_lemmas_oid ])"
definition "thy_ctxt = (\<lambda> Floor1 \<Rightarrow> Embed_theories 
                                      [ Floor1_ctxt.print_ctxt ]
                        | Floor2 \<Rightarrow> Embed_theories 
                                      [ Floor2_ctxt.print_ctxt_pre_post
                                      , Floor2_ctxt.print_ctxt_inv
                                      , Floor2_ctxt.print_ctxt_thm ])"
definition "thy_flush_all = Embed_theories []"
(* NOTE typechecking functions can be put at the end, however checking already defined constants can be done earlier *)

subsection\<open>Combinators Folding the Compiling Environment\<close>

definition "compiler_env_config_reset_all env =
  (let env = compiler_env_config_reset_no_env env in
   ( env \<lparr> D_input_meta := [] \<rparr>
   , let (l_class, l_env) = find_class_ass env in
     L.flatten
       [ l_class
       , List.filter (\<lambda> META_flush_all _ \<Rightarrow> False | _ \<Rightarrow> True) l_env
       , [META_flush_all OclFlushAll] ] ))"

definition "fold_thy0 meta thy_object0 f =
  L_fold (\<lambda>x (acc1, acc2).
    let (sorry, dirty) = D_output_sorry_dirty acc1
      ; (l, acc1) = x meta acc1 in
    (f (if sorry = Some Gen_sorry | sorry = None & dirty then
          L.map (map_semi__theory (map_lemma (\<lambda> Lemma n spec _ _ \<Rightarrow> Lemma n spec [] C.sorry
                                                | Lemma_assumes n spec1 spec2 _ _ \<Rightarrow> Lemma_assumes n spec1 spec2 [] C.sorry))) l
        else
          l) acc1 acc2)) thy_object0"

definition "comp_env_input_class_rm f_fold f env_accu =
  (let (env, accu) = f_fold f env_accu in
   (env \<lparr> D_input_class := None \<rparr>, accu))"

definition "comp_env_save ast f_fold f env_accu =
  (let (env, accu) = f_fold f env_accu in
   (env \<lparr> D_input_meta := ast # D_input_meta env \<rparr>, accu))"

definition "comp_env_save_deep ast f_fold =
  comp_env_save ast (\<lambda>f. map_prod
    (case ast of META_def_state Floor1 meta \<Rightarrow> Floor1_examp.print_meta_setup_def_state meta
               | META_def_transition Floor1 meta \<Rightarrow> Floor1_examp.print_meta_setup_def_transition meta
               | _ \<Rightarrow> id)
    id o
    f_fold f)"

definition "comp_env_input_class_mk f_try f_accu_reset f_fold f =
  (\<lambda> (env, accu).
    f_fold f
      (case D_input_class env of Some _ \<Rightarrow> (env, accu) | None \<Rightarrow>
       let (l_class, l_env) = find_class_ass env
         ; (l_enum, l_env) = partition (\<lambda>META_enum _ \<Rightarrow> True | _ \<Rightarrow> False) l_env in
       (f_try (\<lambda> () \<Rightarrow>
         let D_input_meta0 = D_input_meta env
           ; (env, accu) =
               let meta = class_unflat' (arrange_ass True (D_ocl_semantics env \<noteq> Gen_default) l_class (L.map (\<lambda> META_enum e \<Rightarrow> e) l_enum))
                 ; (env, accu) = List.fold (\<lambda> ast. comp_env_save ast (case ast of META_enum meta \<Rightarrow> fold_thy0 meta thy_enum) f)
                                           l_enum
                                           (let env = compiler_env_config_reset_no_env env in
                                            (env \<lparr> D_input_meta := List.filter (\<lambda> META_enum _ \<Rightarrow> False | _ \<Rightarrow> True) (D_input_meta env) \<rparr>, f_accu_reset env accu))
                 ; (env, accu) = fold_thy0 meta thy_class f (env, accu) in
               (env \<lparr> D_input_class := Some meta \<rparr>, accu)
           ; (env, accu) =
               List.fold
                 (\<lambda>ast. comp_env_save ast (case ast of
                     META_instance meta \<Rightarrow> fold_thy0 meta thy_instance
                   | META_def_base_l meta \<Rightarrow> fold_thy0 meta thy_def_base_l
                   | META_def_state floor meta \<Rightarrow> fold_thy0 meta (thy_def_state floor)
                   | META_def_transition floor meta \<Rightarrow> fold_thy0 meta (thy_def_transition floor)
                   | META_ctxt floor meta \<Rightarrow> fold_thy0 meta (thy_ctxt floor)
                   | META_flush_all meta \<Rightarrow> fold_thy0 meta thy_flush_all)
                        f)
                 l_env
                 (env \<lparr> D_input_meta := L.flatten [l_class, l_enum] \<rparr>, accu) in
          (env \<lparr> D_input_meta := D_input_meta0 \<rparr>, accu)))))"

definition "comp_env_input_class_bind l f =
  List.fold (\<lambda>x. x f) l"

definition "fold_thy' f_env_save f_try f_accu_reset f =
 (let comp_env_input_class_mk = comp_env_input_class_mk f_try f_accu_reset in
  List.fold (\<lambda> ast.
    f_env_save ast (case ast of
     META_enum meta \<Rightarrow> comp_env_input_class_rm (fold_thy0 meta thy_enum_flat)
   | META_class_raw Floor1 meta \<Rightarrow> comp_env_input_class_rm (fold_thy0 meta thy_class_flat)
   | META_association meta \<Rightarrow> comp_env_input_class_rm (fold_thy0 meta thy_association)
   | META_ass_class Floor1 (OclAssClass meta_ass meta_class) \<Rightarrow>
       comp_env_input_class_rm (comp_env_input_class_bind [ fold_thy0 meta_ass thy_association
                                                      , fold_thy0 meta_class thy_class_flat ])
   | META_class_synonym meta \<Rightarrow> comp_env_input_class_rm (fold_thy0 meta thy_class_synonym)
   | META_instance meta \<Rightarrow> comp_env_input_class_mk (fold_thy0 meta thy_instance)
   | META_def_base_l meta \<Rightarrow> fold_thy0 meta thy_def_base_l
   | META_def_state floor meta \<Rightarrow> comp_env_input_class_mk (fold_thy0 meta (thy_def_state floor))
   | META_def_transition floor meta \<Rightarrow> fold_thy0 meta (thy_def_transition floor)
   | META_ctxt floor meta \<Rightarrow> comp_env_input_class_mk (fold_thy0 meta (thy_ctxt floor))
   | META_flush_all meta \<Rightarrow> comp_env_input_class_mk (fold_thy0 meta thy_flush_all)) f))"

definition "compiler_env_config_update f env =
  (* WARNING The semantics of the meta-embedded language is not intended to be reset here (like oid_start), only syntactic configurations of the compiler (path, etc...) *)
 (let env' = f env in
  if D_input_meta env = [] then
    env'
      \<lparr> D_output_disable_thy := D_output_disable_thy env
      , D_output_header_thy := D_output_header_thy env
      (*D_ocl_oid_start*)
      (*D_output_position*)
      , D_ocl_semantics := D_ocl_semantics env
      (*D_input_class*)
      (*D_input_meta*)
      (*D_input_instance*)
      (*D_input_state*)
      (*D_output_header_force*)
      (*D_output_auto_bootstrap*)
      (*D_ocl_accessor*)
      (*D_ocl_HO_type*)
      , D_output_sorry_dirty := D_output_sorry_dirty env \<rparr>
  else
    fst (fold_thy'
           comp_env_save_deep
           (\<lambda>f. f ())
           (\<lambda>_. id)
           (\<lambda>_. Pair)
           (D_input_meta env')
           (env, ())))"

definition "fold_thy_shallow f_try f_accu_reset x = 
  fold_thy'
    comp_env_save
    f_try
    f_accu_reset
    (\<lambda>l acc1.
      map_prod (\<lambda> env. env \<lparr> D_input_meta := D_input_meta acc1 \<rparr>) id
      o List.fold x l
      o Pair acc1)"

definition "fold_thy_deep obj env =
  (case fold_thy'
          comp_env_save_deep
          (\<lambda>f. f ())
          (\<lambda>env _. D_output_position env)
          (\<lambda>l acc1 (i, cpt). (acc1, (Succ i, natural_of_nat (List.length l) + cpt)))
          obj
          (env, D_output_position env) of
    (env, output_position) \<Rightarrow> env \<lparr> D_output_position := output_position \<rparr>)"

end
