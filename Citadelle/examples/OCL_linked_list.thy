theory 
  OCL_linked_list
imports
  "../OCL_main" (* Testing *)
begin

section{* Example Data-Universe *}
text{* Should be generated entirely from a class-diagram. *}

text{* Our data universe @{text "'\<AA>"} consists in the 
       concrete class diagram just of node's. *}

datatype node = Node oid (* the oid to the node itself *)
                     int (* the attribute i *) 
                     oid (* the attribute "next" *)

type_synonym Boolean     = "(node)Boolean"
type_synonym Integer     = "(node)Integer"
type_synonym Void        = "(node)Void"
type_synonym Node        = "(node,node option option)val"
type_synonym Set_Integer = "(node,int option option)Set"

instantiation node :: object
begin
   definition oid_of_def: "oid_of x = (case x of Node oid _ _ \<Rightarrow> oid)"
   instance ..
end


instantiation   option  :: (object)object
begin 
   definition oid_of_option_def: "oid_of x = oid_of (the x)"
   instance ..
end


section{* Instantiation of the generic strict equality *}
text{* Should be generated entirely from a class-diagram. *}

defs   StrictRefEq_node : "(x::Node) \<doteq> y \<equiv> gen_ref_eq x y"

lemmas strict_eq_node =
    cp_gen_ref_eq_object[of "x::Node" "y::Node" "\<tau>", 
                         simplified StrictRefEq_node[symmetric]]
    cp_intro(9)         [of "P::Node \<Rightarrow>Node""Q::Node \<Rightarrow>Node",
                         simplified StrictRefEq_node[symmetric] ]
    gen_ref_eq_def      [of "x::Node" "y::Node", 
                         simplified StrictRefEq_node[symmetric]]
    gen_ref_eq_defargs  [of _ "x::Node" "y::Node", 
                         simplified StrictRefEq_node[symmetric]]
    gen_ref_eq_object_strict1 
                        [of "x::Node",
                         simplified StrictRefEq_node[symmetric]]
    gen_ref_eq_object_strict2 
                        [of "x::Node",
                         simplified StrictRefEq_node[symmetric]]
    gen_ref_eq_object_strict3 
                        [of "x::Node",
                         simplified StrictRefEq_node[symmetric]]
    gen_ref_eq_object_strict3 
                        [of "x::Node",
                         simplified StrictRefEq_node[symmetric]]
    gen_ref_eq_object_strict4 
                        [of "x::Node",
                         simplified StrictRefEq_node[symmetric]]


section{* Selector Definition *}
text{* Should be generated entirely from a class-diagram. *}

fun dot_next:: "Node \<Rightarrow> Node"  ("(1(_).next)" 50)
  where "(X).next = (\<lambda> \<tau>. case X \<tau> of
               None \<Rightarrow> None
          | \<lfloor>  None \<rfloor> \<Rightarrow> None
          | \<lfloor>\<lfloor> Node oid i next \<rfloor>\<rfloor> \<Rightarrow> if next \<in> dom (snd \<tau>)
                                         then \<lfloor> (snd \<tau>) next \<rfloor>
                                         else None)"

fun dot_i:: "Node \<Rightarrow> Integer"  ("(1(_).i)" 50)
  where "(X).i = (\<lambda> \<tau>. case X \<tau> of
               None \<Rightarrow> None
          | \<lfloor>  None \<rfloor> \<Rightarrow> None
          | \<lfloor>\<lfloor> Node oid i next \<rfloor>\<rfloor> \<Rightarrow> 
                      if oid \<in> dom (snd \<tau>)
                      then (case (snd \<tau>) oid of
                                 None \<Rightarrow> None
                            | \<lfloor> Node oid i next \<rfloor> \<Rightarrow> \<lfloor>\<lfloor> i \<rfloor>\<rfloor>)
                      else None)"

fun dot_next_at_pre:: "Node \<Rightarrow> Node"  ("(1(_).next@pre)" 50)
  where "(X).next@pre = (\<lambda> \<tau>. case X \<tau> of
                          None \<Rightarrow> None
                      | \<lfloor> None \<rfloor> \<Rightarrow> None
                      | \<lfloor>\<lfloor>Node oid i next\<rfloor>\<rfloor> \<Rightarrow> if next \<in> dom (fst \<tau>)
                                              then \<lfloor> (fst \<tau>) next \<rfloor>
                                              else None)"

fun dot_i_at_pre:: "Node \<Rightarrow> Integer"  ("(1(_).i@pre)" 50)
where "(X).i@pre = (\<lambda> \<tau>. case X \<tau> of
              None \<Rightarrow> None
          | \<lfloor>  None \<rfloor> \<Rightarrow> None
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
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)

lemma dot_next_at_pre_nullstrict [simp] : "(null).next@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)

lemma dot_next_strict[simp] : "(invalid).next = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)

lemma dot_nextATpre_strict[simp] : "(invalid).next@pre = invalid"
by(rule ext, simp add: null_fun_def null_option_def bot_option_def null_def invalid_def)

section{* Standard State Infrastructure *}
text{* These definitions should be generated --- again --- from the class
diagram. *}

section{* Invariant *}
text{* These recursive predicates can be defined conservatively 
by greatest fix-point constructions - automatically. See HOL-OCL Book
for details. For the purpose of this example, we state them as axioms
here.*}
axiomatization inv_Node :: "Node \<Rightarrow> Boolean"
where A : "(\<tau> \<Turnstile> (\<delta> self)) \<longrightarrow> 
               (\<tau> \<Turnstile> inv_Node(self)) =
                   ((\<tau> \<Turnstile> (self .next \<doteq> null)) \<or> 
                    ( \<tau> \<Turnstile> (self .next <> null) \<and> (\<tau> \<Turnstile> (self .next .i \<prec> self .i))  \<and> 
                     (\<tau> \<Turnstile> (inv_Node(self .next))))) "


axiomatization inv_Node_at_pre :: "Node \<Rightarrow> Boolean"
where B : "(\<tau> \<Turnstile> (\<delta> self)) \<longrightarrow> 
               (\<tau> \<Turnstile> inv_Node_at_pre(self)) =
                   ((\<tau> \<Turnstile> (self .next@pre \<doteq> null)) \<or> 
                    ( \<tau> \<Turnstile> (self .next@pre <> null) \<and> (\<tau> \<Turnstile> (self .next@pre .i@pre \<prec> self .i@pre))  \<and> 
                     (\<tau> \<Turnstile> (inv_Node_at_pre(self .next@pre))))) "

text{* A very first attempt to characterize the axiomatization by an inductive
definition - this can not be the last word since too weak (should be equality!) *}
coinductive inv :: " Node \<Rightarrow> (node)st \<Rightarrow> bool" where 
 "(\<tau> \<Turnstile> (\<delta> self)) \<Longrightarrow> ((\<tau> \<Turnstile> (self .next \<doteq> null)) \<or> 
                      (\<tau> \<Turnstile> (self .next <> null) \<and> (\<tau> \<Turnstile> (self .next .i \<prec> self .i))  \<and> 
                     ( (inv(self .next))\<tau> )))
                     \<Longrightarrow> ( inv self \<tau>)"


section{* The contract of a recursive query : *}
text{* The original specification of a recursive query :
\begin{verbatim}
context Node::contents():Set(Integer)
post:  result = if self.next = null 
                then Set{i}
                else self.next.contents()->including(i)
                endif
\end{verbatim} *}


consts dot_contents :: "Node \<Rightarrow> Set_Integer"  ("(1(_).contents'('))" 50)
 
axiomatization dot_contents_def where
"(\<tau> \<Turnstile> ((self).contents() \<triangleq> result)) =
 (if (\<delta> self) \<tau> = true \<tau> 
  then ((\<tau> \<Turnstile> true) \<and>  
        (\<tau> \<Turnstile> (result \<triangleq> if (self .next \<doteq> null) 
                        then (Set{self .i}) 
                        else (self .next .contents()->including(self .i))
                        endif)))
  else \<tau> \<Turnstile> result \<triangleq> invalid)"


consts dot_contents_AT_pre :: "Node \<Rightarrow> Set_Integer"  ("(1(_).contents@pre'('))" 50)
 
axiomatization where dot_contents_AT_pre_def:
"(\<tau> \<Turnstile> (self).contents@pre() \<triangleq> result) =
 (if (\<delta> self) \<tau> = true \<tau> 
  then \<tau> \<Turnstile> true \<and>                                (* pre *)
        \<tau> \<Turnstile> (result \<triangleq> if (self).next@pre \<doteq> null  (* post *)
                        then Set{(self).i@pre}
                        else (self).next@pre .contents@pre()->including(self .i@pre)
                        endif)
  else \<tau> \<Turnstile> result \<triangleq> invalid)"

text{* Note that these @pre variants on methods are only available on queries, i.e.
operations without side-effect. *}
(* TODO: Should be rephased by conservative means... *)

section{* The contract of a method. *}
text{*
The specification in high-level OCL input syntax reads as follows:
\begin{verbatim}
context Node::insert(x:Integer) 
post: contents():Set(Integer)
contents() = contents@pre()->including(x)
\end{verbatim}
*}

consts dot_insert :: "Node \<Rightarrow> Integer \<Rightarrow> Void"  ("(1(_).insert'(_'))" 50)

axiomatization where dot_insert_def:
"(\<tau> \<Turnstile> (self).insert(x) \<triangleq> result) =
 (if (\<delta> self) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>  
  then \<tau> \<Turnstile> true \<and>  
       \<tau> \<Turnstile> (self).contents() \<triangleq> (self).contents@pre()->including(x)
  else \<tau> \<Turnstile> (self).insert(x) \<triangleq> invalid)"

lemma H : "(\<tau> \<Turnstile> (self).insert(x) \<triangleq> result)"
 nitpick
thm dot_insert_def

(* Old stuff by Matthias Diss - will not really work any longer in this context: 

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
*)

end