header{* Part III: OCL Contracts and an Example *}

(* This example is not yet balanced. Some parts of should go to 
   Part II : State and Objects. *)

theory 
  Employee_DesignModel_OCLPart
imports
  Employee_DesignModel_UMLPart (* Testing *)
begin

section{* Standard State Infrastructure *}
text{* These definitions should be generated --- again --- from the class diagram. *}

section{* Invariant *}
text{* These recursive predicates can be defined conservatively 
by greatest fix-point constructions - automatically. See HOL-OCL Book
for details. For the purpose of this example, we state them as axioms
here.*}
axiomatization inv_Person :: "Person \<Rightarrow> Boolean"
where A : "(\<tau> \<Turnstile> (\<delta> self)) \<longrightarrow> 
               (\<tau> \<Turnstile> inv_Person(self)) =
                   ((\<tau> \<Turnstile> (self .boss \<doteq> null)) \<or> 
                    ( \<tau> \<Turnstile> (self .boss <> null) \<and> (\<tau> \<Turnstile> (self .boss .age \<prec> self .age))  \<and> 
                     (\<tau> \<Turnstile> (inv_Person(self .boss))))) "


axiomatization inv_Person_at_pre :: "Person \<Rightarrow> Boolean"
where B : "(\<tau> \<Turnstile> (\<delta> self)) \<longrightarrow> 
               (\<tau> \<Turnstile> inv_Person_at_pre(self)) =
                   ((\<tau> \<Turnstile> (self .boss@pre \<doteq> null)) \<or> 
                    ( \<tau> \<Turnstile> (self .boss@pre <> null) \<and> (\<tau> \<Turnstile> (self .boss@pre .age@pre \<prec> self .age@pre))  \<and> 
                     (\<tau> \<Turnstile> (inv_Person_at_pre(self .boss@pre))))) "

text{* A very first attempt to characterize the axiomatization by an inductive
definition - this can not be the last word since too weak (should be equality!) *}
coinductive inv :: "Person \<Rightarrow> (\<AA>)st \<Rightarrow> bool" where 
 "(\<tau> \<Turnstile> (\<delta> self)) \<Longrightarrow> ((\<tau> \<Turnstile> (self .boss \<doteq> null)) \<or> 
                      (\<tau> \<Turnstile> (self .boss <> null) \<and> (\<tau> \<Turnstile> (self .boss .age \<prec> self .age))  \<and> 
                     ( (inv(self .boss))\<tau> )))
                     \<Longrightarrow> ( inv self \<tau>)"


section{* The contract of a recursive query : *}
text{* The original specification of a recursive query :
\begin{verbatim}
context Person::contents():Set(Integer)
post:  result = if self.boss = null 
                then Set{i}
                else self.boss.contents()->including(i)
                endif
\end{verbatim} *}


consts dot_contents :: "Person \<Rightarrow> Set_Integer"  ("(1(_).contents'('))" 50)
 
axiomatization dot_contents_def where
"(\<tau> \<Turnstile> ((self).contents() \<triangleq> result)) =
 (if (\<delta> self) \<tau> = true \<tau> 
  then ((\<tau> \<Turnstile> true) \<and>  
        (\<tau> \<Turnstile> (result \<triangleq> if (self .boss \<doteq> null) 
                        then (Set{self .age}) 
                        else (self .boss .contents()->including(self .age))
                        endif)))
  else \<tau> \<Turnstile> result \<triangleq> invalid)"


consts dot_contents_AT_pre :: "Person \<Rightarrow> Set_Integer"  ("(1(_).contents@pre'('))" 50)
 
axiomatization where dot_contents_AT_pre_def:
"(\<tau> \<Turnstile> (self).contents@pre() \<triangleq> result) =
 (if (\<delta> self) \<tau> = true \<tau> 
  then \<tau> \<Turnstile> true \<and>                                (* pre *)
        \<tau> \<Turnstile> (result \<triangleq> if (self).boss@pre \<doteq> null  (* post *)
                        then Set{(self).age@pre}
                        else (self).boss@pre .contents@pre()->including(self .age@pre)
                        endif)
  else \<tau> \<Turnstile> result \<triangleq> invalid)"

text{* Note that these @pre variants on methods are only available on queries, i.e.
operations without side-effect. *}
(* TODO: Should be rephased by conservative means... *)

(* Missing: Properties on Casts, type-tests, and equality vs. projections. *)

section{* The contract of a method. *}
text{*
The specification in high-level OCL input syntax reads as follows:
\begin{verbatim}
context Person::insert(x:Integer) 
post: contents():Set(Integer)
contents() = contents@pre()->including(x)
\end{verbatim}
*}

consts dot_insert :: "Person \<Rightarrow> Integer \<Rightarrow> Void"  ("(1(_).insert'(_'))" 50)

axiomatization where dot_insert_def:
"(\<tau> \<Turnstile> ((self).insert(x) \<triangleq> result)) =
 (if (\<delta> self) \<tau> = true \<tau> \<and> (\<upsilon> x) \<tau> = true \<tau>  
  then \<tau> \<Turnstile> true \<and>  
       \<tau> \<Turnstile> ((self).contents() \<triangleq> (self).contents@pre()->including(x))
  else \<tau> \<Turnstile> ((self).insert(x) \<triangleq> invalid))"

(*
lemma H : "(\<tau> \<Turnstile> (self).insert(x) \<triangleq> result)"
 nitpick
thm dot_insert_def
oops
takes too long...
*) 
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
