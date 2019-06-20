theory Seq_MonadSE
  imports MonadSE
begin
  
subsection{* Chaining Executions : Definitions of Multi-bind Operators *}

text{*  In order to express execution sequences inside \HOL --- rather
than arguing over a certain pattern of terms on the meta-level --- and
in order to make our theory amenable to formal reasoning over execution sequences, 
we represent them as lists of input and generalize the bind-operator
of the state-exception monad accordingly. The approach is straightforward,
but comes with a price: we have to encapsulate all input and output data
into one type, and restrict ourselves to  a uniform step function.
Assume that we have a typed interface to a module with
the operations $op_1$, $op_2$, \ldots, $op_n$ with the inputs 
$\iota_1$, $\iota_2$, \ldots, $\iota_n$ (outputs are treated analogously).
Then we can encode for this interface the general input - type:
\begin{displaymath}
\texttt{datatype}\ \texttt{in}\ =\ op_1\ ::\ \iota_1\ |\ ...\ |\ \iota_n
\end{displaymath}
Obviously, we loose some type-safety in this approach; we have to express
that in traces only \emph{corresponding} input and output belonging to the 
same operation will occur; this form of side-conditions have to be expressed
inside \HOL. From the user perspective, this will not make much difference,
since junk-data resulting from too weak typing can be ruled out by adopted
front-ends. 
*}

text{* Note that the subsequent notion of a test-sequence allows the io stepping 
function (and the special case of a program under test) to stop execution 
\emph{within} the sequence; such premature terminations are characterized by an 
output list which is shorter than the input list. 

Intuitively, @{text mbind} corresponds to a sequence of operation calls, separated by
";", in Java. The operation calls may fail (raising an exception), which means that
the state is maintained and the exception can still be caught at the end of the 
execution sequence.

*}

fun    mbind :: "'\<iota> list  \<Rightarrow>  ('\<iota> \<Rightarrow> ('o,'\<sigma>) MON\<^sub>S\<^sub>E) \<Rightarrow> ('o list,'\<sigma>) MON\<^sub>S\<^sub>E"  
where "mbind [] iostep \<sigma> = Some([], \<sigma>)"
    | "mbind (a#S) iostep \<sigma> = 
                (case iostep a \<sigma> of 
                     None   \<Rightarrow> Some([], \<sigma>)
                  |  Some (out, \<sigma>') \<Rightarrow> (case mbind S iostep \<sigma>' of 
                                          None    \<Rightarrow> Some([out],\<sigma>') 
                                        | Some(outs,\<sigma>'') \<Rightarrow> Some(out#outs,\<sigma>'')))"

notation mbind ("mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e") (* future name: mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e *)

text{* This definition is fail-safe; in case of an exception, the current state is maintained,
       the computation as a whole is marked as success.
       Compare to the fail-strict variant @{text "mbind'"}: *}

lemma mbind_unit [simp]: 
     "mbind [] f = (result [])"
      by(rule ext, simp add: unit_SE_def)

text{* The characteristic property of @{term mbind} --- which distinguishes it from 
       @{text mbind} defined in the sequel --- is that it never fails; it ``swallows'' internal
       errors occuring during the computation. *}    
lemma mbind_nofailure [simp]:
     "mbind S f \<sigma> \<noteq> None"
      apply(rule_tac x=\<sigma> in spec)
      apply(induct S, auto simp:unit_SE_def)
      apply(case_tac "f a x", auto)
      apply(erule_tac x="b" in allE) 
      apply(erule exE, erule exE, simp)
      done

text{* In contrast, we define a fail-strict sequential execution operator.
He has more the characteristic to fail globally whenever one of its operation
steps fails.

Intuitively speaking, @{text mbind'} corresponds to an execution of operations 
where a results in a System-Halt. Another interpretation of @{text mbind'} is to
view it as a kind of @{term foldl} foldl over lists via @{term bind\<^sub>S\<^sub>E}.*} 
 
fun    mbind' :: "'\<iota> list  \<Rightarrow>  ('\<iota> \<Rightarrow> ('o,'\<sigma>) MON\<^sub>S\<^sub>E) \<Rightarrow> ('o list,'\<sigma>) MON\<^sub>S\<^sub>E"
where "mbind' [] iostep \<sigma> = Some([], \<sigma>)" |
      "mbind' (a#S) iostep \<sigma> = 
                (case iostep a \<sigma> of 
                     None   \<Rightarrow> None
                  |  Some (out, \<sigma>') \<Rightarrow> (case mbind' S iostep \<sigma>' of 
                                          None    \<Rightarrow> None   (*  fail-strict *) 
                                        | Some(outs,\<sigma>'') \<Rightarrow> Some(out#outs,\<sigma>'')))"
notation mbind' ("mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p") (* future name: mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p *)

lemma mbind'_unit [simp]: 
     "mbind' [] f = (result [])"
      by(rule ext, simp add: unit_SE_def)

lemma mbind'_bind [simp]: 
     "(x \<leftarrow> mbind' (a#S) F; M x) = (a \<leftarrow> (F a); (x \<leftarrow> mbind' S F; M (a # x)))"
      by(rule ext, rename_tac "z",simp add: bind_SE_def split: option.split)

declare mbind'.simps[simp del] (* use only more abstract definitions *)

text{* The next @{text mbind} sequential execution operator is called 
Fail-Purge. He has more the characteristic to never fail, just "stuttering" 
above operation steps that fail. Another alternative in modeling. *} 

fun    mbind'' :: "'\<iota> list  \<Rightarrow>  ('\<iota> \<Rightarrow> ('o,'\<sigma>) MON\<^sub>S\<^sub>E) \<Rightarrow> ('o list,'\<sigma>) MON\<^sub>S\<^sub>E"
where "mbind'' [] iostep \<sigma> = Some([], \<sigma>)" |
      "mbind'' (a#S) iostep \<sigma> = 
                (case iostep a \<sigma> of 
                     None           \<Rightarrow> mbind'' S iostep \<sigma>
                  |  Some (out, \<sigma>') \<Rightarrow> (case mbind'' S iostep \<sigma>' of 
                                          None    \<Rightarrow> None   (*  does not occur *) 
                                        | Some(outs,\<sigma>'') \<Rightarrow> Some(out#outs,\<sigma>'')))"

notation mbind'' ("mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e") (* future name: mbind\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e\<^sub>F\<^sub>a\<^sub>i\<^sub>l *)
declare  mbind''.simps[simp del] (* use only more abstract definitions *)


text{* mbind' as failure strict operator can be seen as a foldr on bind -
       if the types would match \ldots *}

subsubsection{* Definition : Miscellaneous Operators and their Properties *}

lemma mbind_try: 
  "(x \<leftarrow> mbind (a#S) F; M x) = 
   (a' \<leftarrow> try\<^sub>S\<^sub>E(F a); 
      if a' = None 
      then (M [])
      else (x \<leftarrow> mbind S F; M (the a' # x)))"
apply(rule ext)
apply(simp add: bind_SE_def try_SE_def)
apply(case_tac "F a x", auto)
apply(simp add: bind_SE_def try_SE_def)
apply(case_tac "mbind S F b", auto)
done



  
end
  