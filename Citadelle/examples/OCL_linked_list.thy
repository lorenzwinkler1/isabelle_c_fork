theory 
  OCL_linked_list
imports
  OCL_main (* Testing *)
begin

section{* Example Data-Universe *}
text{* Should be generated entirely from a class-diagram. *}

datatype node = Node oid int oid

instantiation node :: object
begin

definition oid_of_def:
   "oid_of x = (case x of Node oid _ _ \<Rightarrow> oid)"

instance ..

end

section{* Instantiation of the generic strict equality *}
text{* Should be generated entirely from a class-diagram. *}

defs   StrictRefEq_node : 
       "(x::(node,node)val) \<doteq> y \<equiv> gen_ref_eq x y"

lemmas strict_eq_node =
    cp_gen_ref_eq_object[of "x::(node,node)val" 
                            "y::(node,node)val" 
                            \<tau>, 
                         simplified StrictRefEq_node[symmetric]]

    cp_intro(9)         [of "P::(node,node)val \<Rightarrow>(node,node)val"
                            "Q::(node,node)val \<Rightarrow>(node,node)val",
                         simplified StrictRefEq_node[symmetric] ]
(*    gen_ref_eq_def      [of "x::(node,node)val" 
                            "y::(node,node)val", 
                         simplified StrictRefEq_node[symmetric]]
    gen_ref_eq_defargs  [of _
                            "x::(node,node)val" 
                            "y::(node,node)val", 
                         simplified StrictRefEq_node[symmetric]]
    gen_ref_eq_object_strict1 
                        [of "x::(node,node)val",
                         simplified StrictRefEq_node[symmetric]]
    gen_ref_eq_object_strict2 
                        [of "x::(node,node)val",
                         simplified StrictRefEq_node[symmetric]]
    gen_ref_eq_object_strict3 
                        [of "x::(node,node)val",
                         simplified StrictRefEq_node[symmetric]]
    gen_ref_eq_object_strict4 
                        [of "x::(node,node)val",
                         simplified StrictRefEq_node[symmetric]]
*)

section{* Selector Definition *}
text{* Should be generated entirely from a class-diagram. *}

fun dot_next:: "(node,node)val \<Rightarrow> (node,node)val"  ("(1(_).next)" 50)
  where "(X).next = (\<lambda> \<tau>. case X \<tau> of
               None \<Rightarrow> None
          | \<lfloor> None \<rfloor> \<Rightarrow> None
          | \<lfloor>\<lfloor> Node oid i next \<rfloor>\<rfloor> \<Rightarrow> if next \<in> dom (snd \<tau>)
                                         then \<lfloor> (snd \<tau>) next \<rfloor>
                                         else None)"

fun dot_i:: "(node,node)val \<Rightarrow> (node)Integer"  ("(1(_).i)" 50)
  where "(X).i = (\<lambda> \<tau>. case X \<tau> of
               None \<Rightarrow> None
          | \<lfloor> None \<rfloor> \<Rightarrow> None
          | \<lfloor>\<lfloor> Node oid i next \<rfloor>\<rfloor> \<Rightarrow> 
                      if oid \<in> dom (snd \<tau>)
                      then (case (snd \<tau>) oid of
                                 None \<Rightarrow> None
                            | \<lfloor> Node oid i next \<rfloor> \<Rightarrow> \<lfloor>\<lfloor> i \<rfloor>\<rfloor>)
                      else None)"

fun dot_next_at_pre:: "(node,node)val \<Rightarrow> (node,node)val"  ("(1(_).next@pre)" 50)
  where "(X).next@pre = (\<lambda> \<tau>. case X \<tau> of
                        None \<Rightarrow> None
                      | \<lfloor> None \<rfloor> \<Rightarrow> None
                      | \<lfloor>\<lfloor> Node oid i next  \<rfloor>\<rfloor> \<Rightarrow> if next \<in> dom (fst \<tau>)
                                                       then \<lfloor> (fst \<tau>) next \<rfloor>
                                                       else None)"


fun dot_i_at_pre:: "(node,node)val \<Rightarrow> (node)Integer"  ("(1(_).i@pre)" 50)
where "(X).i@pre = (\<lambda> \<tau>. case X \<tau> of
               None \<Rightarrow> None
          | \<lfloor> None \<rfloor> \<Rightarrow> None
          | \<lfloor>\<lfloor> Node oid i next \<rfloor>\<rfloor> \<Rightarrow> 
                      if oid \<in> dom (fst \<tau>)
                      then (case (fst \<tau>) oid of
                                None \<Rightarrow> None
                            | \<lfloor> Node oid i next \<rfloor> \<Rightarrow> \<lfloor>\<lfloor> i \<rfloor>\<rfloor>)
                      else None)"

lemma cp_dot_next:
"((X).next) \<tau> = ((\<lambda>_. X \<tau>).next) \<tau>" by(simp)

lemma cp_dot_i:
"((X).i) \<tau> = ((\<lambda>_. X \<tau>).i) \<tau>" by(simp)

lemma cp_dot_next_at_pre:
"((X).next@pre) \<tau> = ((\<lambda>_. X \<tau>).next@pre) \<tau>" by(simp)

lemma cp_dot_i_pre:
"((X).i@pre) \<tau> = ((\<lambda>_. X \<tau>).i@pre) \<tau>" by(simp)

lemmas cp_dot_nextI [simp, intro!]= 
       cp_dot_next[THEN allI[THEN allI], of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]

lemmas cp_dot_nextI_at_pre [simp, intro!]= 
       cp_dot_next_at_pre[THEN allI[THEN allI], 
                          of "\<lambda> X _. X" "\<lambda> _ \<tau>. \<tau>", THEN cpI1]

lemma dot_next_nullstrict [simp]: "(null).next = invalid"
by(rule ext, simp add: null_def invalid_def)

lemma dot_next_at_pre_nullstrict [simp] : "(null).next@pre = invalid"
by(rule ext, simp add: null_def invalid_def)

lemma dot_next_strict[simp] : "(invalid).next = invalid"
by(rule ext, simp add: null_def invalid_def)

lemma dot_nextATpre_strict[simp] : "(invalid).next@pre = invalid"
by(rule ext, simp add: null_def invalid_def)

section{* Invariant *}

axiomatization inv_Node :: "(node,node)val \<Rightarrow> (node)Boolean"
where A : "(\<tau> \<Turnstile> (\<delta> self)) \<longrightarrow> 
               (\<tau> \<Turnstile> inv_Node(self)) =
                   ((\<tau> \<Turnstile> (self .next \<doteq> null)) \<or> 
                    ( \<tau> \<Turnstile> (self .next <> null) \<and> (\<tau> \<Turnstile> (self .next .i \<prec> self .i))  \<and> 
                     (\<tau> \<Turnstile> (inv_Node(self .next))))) "

thm A

axiomatization inv_Node_at_pre :: "(node,node)val \<Rightarrow> (node)Boolean"
where B : "(\<tau> \<Turnstile> (\<delta> self)) \<longrightarrow> 
               (\<tau> \<Turnstile> inv_Node_at_pre(self)) =
                   ((\<tau> \<Turnstile> (self .next@pre \<doteq> null)) \<or> 
                    ( \<tau> \<Turnstile> (self .next@pre <> null) \<and> (\<tau> \<Turnstile> (self .next@pre .i@pre \<prec> self .i@pre))  \<and> 
                     (\<tau> \<Turnstile> (inv_Node_at_pre(self .next@pre))))) "

text{* A very first attempt to characterize the axiomatization by an inductive
definition - this can not be the last word since too weak (should be equality!) *}
coinductive inv :: " (node,node)val \<Rightarrow> (node)st \<Rightarrow> bool" where
 "(\<tau> \<Turnstile> (\<delta> self)) \<Longrightarrow> inv st x"  |
 "(\<tau> \<Turnstile> (\<delta> self)) \<Longrightarrow> ((\<tau> \<Turnstile> (self .next \<doteq> null)) \<or> 
                      (\<tau> \<Turnstile> (self .next <> null) \<and> (\<tau> \<Turnstile> (self .next .i \<prec> self .i))  \<and> 
                     ( (inv(self .next))\<tau> )))
                     \<Longrightarrow> ( inv st \<tau>)"

find_theorems "inv"

fun contents_contract :: "('a state \<Rightarrow> ('a oid option) \<Rightarrow> int set) \<Rightarrow> 'a state \<Rightarrow> ('a oid option) \<Rightarrow> bool" where
"contents_contract f st None = True" |
"contents_contract f st (Some s) = (case st s of None \<Rightarrow> True 
  | Some (Node i next) \<Rightarrow> f st (Some s) = (case next of None \<Rightarrow> {i} | Some n \<Rightarrow> f st (Some n) \<union> {i}))"

definition contents :: "'a state \<Rightarrow> ('a oid option) \<Rightarrow> int set" where
contents_post: "contents = (SOME f . \<forall> st s . contents_contract f st s)"

definition contents_at_pre :: "'a state \<Rightarrow> ('a oid option) \<Rightarrow> int set" where
contents_post2: "contents_at_pre = (SOME f . \<forall> st s . contents_contract f st s)"

lemma contents_def: "contents_at_pre st (Some s) = (case st s of None \<Rightarrow> undefined
  | Some (Node i next) \<Rightarrow> (case next of None \<Rightarrow> {i} | Some n \<Rightarrow> contents_at_pre st (Some n) \<union> {i}))"
apply(auto simp: contents_post2)
apply(case_tac "st s", simp_all)
prefer 2
apply(case_tac "a", simp_all)
apply(case_tac "option", simp_all)
sorry

declare OO_List.inv.simps [testgen_OO_eqs]
declare contents_def [testgen_OO_eqs]

test_spec "inv pre_state s \<longrightarrow> contents (post_state pre_state x) (Some s) = contents_at_pre pre_state (Some s) \<union> {x}"
apply(gen_test_cases "post_state" simp del: contents_post contents_post2)
store_test_thm "oo_test"

gen_test_data "oo_test"

thm oo_test.test_data

ML {*

val test_tac = alias_closure_tac @{context} @{typ "'a option"}

*}

lemma "(at_next st y) = (at_next st (at_next st y))" 
apply(tactic "test_tac 1")
apply(simp_all)
oops

lemma rewr: "id (x::int) = id x + id x - id x"
apply(simp)
done

lemma "(x::int) = id x"
(* apply(tactic "EqSubst.eqsubst_tac @{context} [1] [@{thm rewr}] 1") *)
apply(tactic "bounded_unfold_tac @{context} 3 @{thm rewr} 1")
oops

end