(***************************************************************************************
 * Clean.thy --- a basic abstract ("shallow") programming language for test and proof.
 * Burkhart Wolff, Frederic Tuong and Chantal Keller, LRI, Univ. Paris-Saclay, France
 ***************************************************************************************)

section \<open>The Clean Language\<close>

text\<open>\<^verbatim>\<open>Clean\<close> (pronounce : "C lean") is a minimalistic imperative language with C-like control-flow operators based on a 
shallow embedding into the SE exception Monad theory formalized in \<^verbatim>\<open>Clean.MonadSE\<close>. It comprises:
\begin{itemize}
\item C-like control flow with \verb+break+ and \verb+return+.
\item global variables.
\item function calls (seen as Monad-executions) with side-effects, recursion
      and local variables.
\item parameters are modeled via functional abstractions 
      (functions are Monads ...); a passing of parameters to local variables
      might be added later.
\item direct recursive function calls
\item cartouche syntax for \<open>\<lambda>\<close>-lifted update operations supporting global and local variables.
\end{itemize}

Note that \<^verbatim>\<open>Clean\<close> in its current version is restricted to \<^emph>\<open>monomorphic\<close> global and local variables
as well as function parameters. This limitation will be overcome at a later stage. The construction
in itself, however, is deeply based on parametric polymorphism (enabling structured proofs over
extensible records as used in languages of the ML family
\<^url>\<open>http://www.cs.ioc.ee/tfp-icfp-gpce05/tfp-proc/21num.pdf\<close>
and Haskell \<^url>\<open>https://www.schoolofhaskell.com/user/fumieval/extensible-records\<close>).
\<close>


theory Clean
  imports Symbex_MonadSE
  keywords "global_vars" "local_vars_test" :: thy_decl 
     and "returns" "pre" "post" "local_vars" "variant" 
     and "function_spec" :: thy_decl
     and "rec_function_spec"   :: thy_decl

begin


section\<open>A High-level Description of the Clean Memory Model\<close>

subsection\<open>A Simple Typed Memory Model: Clean \<close>
text\<open> Clean is based on a ``no-frills'' state-exception monad 
\<^theory_text>\<open>type_synonym ('o, '\<sigma>) MON\<^sub>S\<^sub>E = \<open>'\<sigma> \<rightharpoonup> ('o \<times> '\<sigma>)\<close>\<close> with the 
usual definitions of \<^term>\<open>bind\<close> and \<^term>\<open>unit\<close>.
In this language, sequence operators, 
conditionals and loops can be integrated. From a concrete program, the underlying state
\<^theory_text>\<open>'\<sigma>\<close> is incrementally constructed by a sequence of extensible record definitions:
\<^enum> initially, an internal control state is defined to give semantics to \<^term>\<open>break\<close> and
 \<^term>\<open>return\<close> statements:
  \begin{isar}
        record control_state =  break_val  :: bool   return_val :: bool
  \end{isar}
  \<^theory_text>\<open>control_state\<close> represents the $\sigma_0$ state.
\<^enum> Any global variable definition block with definitions $a_1 : \tau_1$ $\dots$ $a_n : \tau_n$  
  is translated into a record extension:
  \begin{isar}
        record \<sigma>$_{n+1}$ = \<sigma>$_n$    +    a$_1$ :: $\tau_1$; ...; $a_n$ :: $\tau_n$
  \end{isar}
\<^enum> Any local variable definition block (as part of a procedure declaration) 
  with definitions $a_1 : \tau_1$ $\dots$ $a_n : \tau_n$ is translated into the record extension:
  \begin{isar}
        record \<sigma>$_{n+1}$ = \<sigma>$_n$    +    a$_1$ :: $\tau_1$ list; ...; $a_n$ :: $\tau_n$ list; result :: $\tau_{result-type}$ list; 
  \end{isar}
  where the \<^theory_text>\<open>list\<close>-lifting is used to model a \<^emph>\<open>stack\<close> of local variable instances
  in case of direct recursions and the \<^term>\<open>result_value\<close> used for the value of the \<^term>\<open>return\<close>
  statement.\<close>

text \<open> The \<^theory_text>\<open>record\<close> package creates an
\<^theory_text>\<open>'\<sigma>\<close> extensible record type
\<^theory_text>\<open>'\<sigma> control_state_ext\<close> where the
\<^theory_text>\<open>'\<sigma>\<close> stands for extensions that were subsequently ``stuffed'' in
them. Furthermore, it generates definitions for the constructor, accessor and update functions and
automatically derives a number of theorems over them (e.g., ``updates on different fields commute'',
``accessors on a record are surjective'', ``accessors yield the value of the last update''). The
collection of these theorems constitutes the \<^emph>\<open>memory model\<close> of Clean. This
model might be wrong in the sense that it does not reflect the operational behaviour of a particular
compiler, however, it is by construction \<^emph>\<open>logically consistent\<close> since it is
impossible to derive falsity from the entire set of rules. \<close>

text\<open>
On this basis, assignments, conditionals and loops are reformulated into
\<^term>\<open>break\<close>-aware and \<^term>\<open>return\<close>-aware versions as shown in the definitions of \<^term>\<open>assign\<close> and \<^term>\<open>if_C\<close> (in this theory file, see below). The Clean
theory contains about 600 derived theorems containing symbolic evaluation and Hoare-style
verification rules.
\<close>

text\<open>IS THIS SUBSEQUENT PARAGRAPH USEFUL HERE ? \<close>
text\<open>For example, a global variable \<^verbatim>\<open>A\<close> representing an array of integer could be represented
by
\<^theory_text>\<open>record state0 = control_state + A :: "int list"\<close>
which could be later extended by another global variable, say, \<^verbatim>\<open>B\<close> representing a real represented
by --- why not ? --- Cauchy Sequence @{typ "nat \<Rightarrow> (int \<times> int)"} as follows:
\<^theory_text>\<open>record state1 = state0 + B :: "nat \<Rightarrow> (int \<times> int)"\<close>.
A further extension would be needed if a (potentially recursive) function \<^verbatim>\<open>f\<close> with some local
variable  \<^verbatim>\<open>tmp\<close> is defined:
\<^theory_text>\<open>record state2 = state1 + tmp :: "nat stack" result_value :: "nat stack" \<close> where the "stack" 
needed for modeling recursive instances is just a synonym for lists.
\<close>

text\<open>IS THIS SUBSEQUENT PARAGRAPH SUFFICIENTLY PREPARED ? EXAMPLE IS PRIME ? ? \<close>

text\<open> 
Importing Clean into a theory with its activated back-end proceeds as in \autoref{fig:clean}.
Clean generates for the C program a common type for the state, based on two generated
extensible records --- in the figure: just a global variable \<^term>\<open>k\<close> and a local variable 
with a stack of result values for \<open>is_prime\<close>. Clean maps machine integers simply 
and naively on the HOL type \<^theory_text>\<open>int\<close>. The core of this program is represented by two 
generated definitions available subsequently in the logical context, where they are ready to be
used in symbolic executions or proofs.

Generated definitions include push and pop operations for local variable
blocks, for the entire variable space of procedures. Additionally, a specific syntax is introduced to represent assignments on global and local variables. For example,
\<open>i := 2\<close> internally rewrites to
@{term [source = true] \<open>assign (\<lambda>\<sigma>. ((i_upd o map_hd) (\<lambda>_. 2)) \<sigma>)\<close>}.
The \<open>return\<close> operation is syntactically equivalent to the assignment of the result variable 
in the local state (stack) and sets the \<^term>\<open>return_val\<close> flag.
On this representation of the C program, the term \<open>is_prime n\<close> can be decomposed into  
program test-cases according to a well-established coverage criterion.
Technically, this is done by a variant of the program-based testing method
\begin{isar}
  apply (branch_and_loop_coverage "Suc (Suc (Suc 0))")
\end{isar}
developed in @{cite "DBLP:conf/tap/Keller18"}, which also uses Clean as semantic basis.
Note that the testing approach does not need the formulation of an invariant,
which is already non-trivial in the given example. 
\<close>

section\<open> Control-States  \<close>

text\<open>The control state is the "root" of all extensions for local and global variable
spaces in \<^verbatim>\<open>Clean\<close>. It contains just the information of the current control-flow: a break occurred
(meaning all commands till the end of the control block will be skipped) or a return occurred
(meaning all commands till the end of the current function body will be skipped).\<close>
  
record  control_state = 
            break_status  :: bool
            return_status :: bool

(* break quites innermost while or for, return quits an entire execution sequence. *)  
definition break :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"
  where   "break \<equiv> (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> break_status := True \<rparr>))"
  
definition unset_break_status :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"
  where   "unset_break_status \<equiv> (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> break_status := False \<rparr>))"

definition set_return_status :: " (unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"    
  where   "set_return_status = (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> return_status := True \<rparr>))"
    
definition unset_return_status :: "(unit, ('\<sigma>_ext) control_state_ext) MON\<^sub>S\<^sub>E"    
  where   "unset_return_status  = (\<lambda> \<sigma>. Some((), \<sigma> \<lparr> return_status := False \<rparr>))"


definition exec_stop :: "('\<sigma>_ext) control_state_ext \<Rightarrow> bool"
  where   "exec_stop = (\<lambda> \<sigma>. break_status \<sigma> \<or> return_status \<sigma> )"


section\<open> Global and Local State Management based on Extensible Records (CORE) \<close>

text\<open>Declarations of global and local variable blocks were constructed by subsequent extensions
of the @{typ "control_state"}, the entire construction of a common state space is realized on top
of a management of extensible records. 
\<close>
ML\<open>

structure StateMgt_core = 
struct

val control_stateT = Syntax.parse_typ @{context} "control_state"
val control_stateS = @{typ "('a)control_state_scheme"};

fun optionT t = Type(@{type_name "Option.option"},[t]);
fun MON_SE_T res state = state --> optionT(HOLogic.mk_prodT(res,state));

fun merge_control_stateS (@{typ "('a)control_state_scheme"},t) = t
   |merge_control_stateS (t, @{typ "('a)control_state_scheme"}) = t
   |merge_control_stateS (t, t') = if (t = t') then t else error"can not merge Clean state"

datatype var_kind = global_var of typ | local_var of typ

fun type_of(global_var t) = t | type_of(local_var t) = t

type state_field_tab = var_kind Symtab.table

structure Data = Generic_Data
(
  type T                      = (state_field_tab * typ (* current extensible record *)) 
  val  empty                  = (Symtab.empty,control_stateS)
  val  extend                 = I
  fun  merge((s1,t1),(s2,t2)) = (Symtab.merge (op =)(s1,s2),merge_control_stateS(t1,t2))
);


val get_data                   = Data.get o Context.Proof;
val map_data                   = Data.map;
val get_data_global            = Data.get o Context.Theory;
val map_data_global            = Context.theory_map o map_data;

val get_state_type             = snd o get_data
val get_state_type_global      = snd o get_data_global
val get_state_field_tab        = fst o get_data
val get_state_field_tab_global = fst o get_data_global
fun upd_state_type f           = map_data (fn (tab,t) => (tab, f t))
fun upd_state_type_global f    = map_data_global (fn (tab,t) => (tab, f t))

fun fetch_state_field (ln,X)   = let val a::b:: _  = rev (Long_Name.explode ln) in ((b,a),X) end;

fun filter_name name ln        = let val ((a,b),X) = fetch_state_field ln
                                 in  if a = name then SOME((a,b),X) else NONE end;

fun filter_attr_of name thy    = let val tabs = get_state_field_tab_global thy
                                 in  map_filter (filter_name name) (Symtab.dest tabs) end;

fun is_program_variable name thy = Symtab.defined((fst o get_data_global) thy) name

fun is_global_program_variable name thy = case Symtab.lookup((fst o get_data_global) thy) name of
                                             SOME(global_var _) => true
                                           | _ => false

fun is_local_program_variable name thy = case Symtab.lookup((fst o get_data_global) thy) name of
                                             SOME(local_var _) => true
                                           | _ => false

fun declare_state_variable_global f field thy  =  
             let val Const(name,ty) = Syntax.read_term_global thy field
             in  (map_data_global (apfst (Symtab.update_new(name,f ty))) (thy)
                 handle Symtab.DUP _ => error("multiple declaration of global var"))
             end;

fun declare_state_variable_local f field ctxt  = 
             let val Const(name,ty) = Syntax.read_term_global  (Context.theory_of ctxt) field
             in  (map_data (apfst (Symtab.update_new(name,f ty)))(ctxt)
                 handle Symtab.DUP _ => error("multiple declaration of global var"))
             end;

end\<close>

section\<open> The Core Clean Operations (embedded in the State-Exception Monad) \<close>

consts syntax_assign :: "('\<alpha>  \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> term" (infix ":=" 60)

definition assign :: "(('\<sigma>_ext) control_state_scheme  \<Rightarrow> 
                       ('\<sigma>_ext) control_state_scheme) \<Rightarrow> 
                       (unit,('\<sigma>_ext) control_state_scheme)MON\<^sub>S\<^sub>E"
  where   "assign f = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some((), \<sigma>) else Some((), f \<sigma>))"

(* todo: rename assign to trans2mon combinator; since it will be used for calls as well *)

definition  assign_global :: "(('a  \<Rightarrow> 'a ) \<Rightarrow> '\<sigma>_ext control_state_scheme \<Rightarrow> '\<sigma>_ext control_state_scheme)
                      \<Rightarrow> ('\<sigma>_ext control_state_scheme \<Rightarrow>  'a)
                      \<Rightarrow> (unit,'\<sigma>_ext control_state_scheme) MON\<^sub>S\<^sub>E"
  where    "assign_global upd rhs = assign(\<lambda>\<sigma>. ((upd) (%_. rhs \<sigma>)) \<sigma>)"


fun      map_hd :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list" 
  where "map_hd f [] = []"
      | "map_hd f (a#S) = f a # S"

lemma tl_map_hd [simp] :"tl (map_hd f S) = tl S"  by (metis list.sel(3) map_hd.elims) 

definition "map_nth = (\<lambda>i f l. list_update l i (f (l ! i)))"

definition  assign_local :: "(('a list \<Rightarrow> 'a list) \<Rightarrow> '\<sigma>_ext control_state_scheme \<Rightarrow> '\<sigma>_ext control_state_scheme)
                      \<Rightarrow> ('\<sigma>_ext control_state_scheme \<Rightarrow>  'a)
                      \<Rightarrow> (unit,'\<sigma>_ext control_state_scheme) MON\<^sub>S\<^sub>E"
  where    "assign_local upd rhs = assign(\<lambda>\<sigma>. ((upd o map_hd) (%_. rhs \<sigma>)) \<sigma>)"


text\<open>Semantically, the difference between \<^emph>\<open>global\<close> and \<^emph>\<open>local\<close> is rather unimpressive as the 
     following lemma shows. However, the distinction matters for the pretty-printing setup of Clean.\<close>
lemma "assign_local upd rhs = assign_global (upd o map_hd) rhs "
      unfolding assign_local_def assign_global_def by simp

text\<open>The return command in C-like languages is represented basically by an assignment to a local
variable \<^verbatim>\<open>result_value\<close> (see below in the Clean-package generation). Plus a setting of the 
\<^term>\<open>return_status\<close> ... Note that a return may appear after a break and should have no effect
in this case ...\<close>

definition return\<^sub>C :: "(('a list \<Rightarrow> 'a list) \<Rightarrow> '\<sigma>_ext control_state_scheme \<Rightarrow> '\<sigma>_ext control_state_scheme)
                      \<Rightarrow> ('\<sigma>_ext control_state_scheme \<Rightarrow>  'a)
                      \<Rightarrow> (unit,'\<sigma>_ext control_state_scheme) MON\<^sub>S\<^sub>E"
  where   "return\<^sub>C upd rhs = assign_local upd rhs ;- 
                            (\<lambda>\<sigma>. if exec_stop \<sigma> then Some((), \<sigma>) 
                                                else set_return_status \<sigma>)" 

definition block\<^sub>C :: "  (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E
                     \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E  
                     \<Rightarrow> ('\<alpha>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E
                     \<Rightarrow> ('\<alpha>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "block\<^sub>C push core pop \<equiv> (          \<comment> \<open>assumes break and return unset \<close> 
                                   push ;-   \<comment> \<open>create new instances of local variables \<close> 
                                   core ;-   \<comment> \<open>execute the body \<close>
                                   unset_break_status ;-    \<comment> \<open>unset a potential break \<close>
                                   unset_return_status;-    \<comment> \<open>unset a potential return break \<close>
                                   (x \<leftarrow> pop;           \<comment> \<open>restore previous local var instances \<close>
                                    unit\<^sub>S\<^sub>E(x)))"        \<comment> \<open>yield the return value \<close>
    

(* Is this the right approach to handle calls of ops with multiple arguments ? Or better
   some appropriate currying principle ? *) 
definition call\<^sub>C :: "( '\<alpha> \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E) \<Rightarrow>
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<alpha>) \<Rightarrow>                        
                      ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "call\<^sub>C M A\<^sub>1 = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some(undefined, \<sigma>) else M (A\<^sub>1 \<sigma>) \<sigma>)"



(* some more experimental variants for curried operations ... *)
definition call_0\<^sub>C :: "('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "call_0\<^sub>C M = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some(undefined, \<sigma>) else M \<sigma>)"

text\<open>The generic version using tupling is identical with @{term \<open>call_1\<^sub>C\<close>}.\<close>
definition call_1\<^sub>C :: "( '\<alpha> \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E) \<Rightarrow>
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<alpha>) \<Rightarrow>                        
                      ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"                                                      
  where   "call_1\<^sub>C  = call\<^sub>C"

definition call_2\<^sub>C :: "( '\<alpha> \<Rightarrow> '\<beta> \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E) \<Rightarrow>
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<alpha>) \<Rightarrow>                        
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<beta>) \<Rightarrow>      
                      ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "call_2\<^sub>C M A\<^sub>1 A\<^sub>2 = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some(undefined, \<sigma>) else M (A\<^sub>1 \<sigma>) (A\<^sub>2 \<sigma>) \<sigma>)"

definition call_3\<^sub>C :: "( '\<alpha> \<Rightarrow> '\<beta> \<Rightarrow>  '\<gamma> \<Rightarrow> ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E) \<Rightarrow>
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<alpha>) \<Rightarrow>                        
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<beta>) \<Rightarrow>      
                       ((('\<sigma>_ext) control_state_ext) \<Rightarrow> '\<gamma>) \<Rightarrow>      
                      ('\<rho>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "call_3\<^sub>C M A\<^sub>1 A\<^sub>2 A\<^sub>3 = (\<lambda>\<sigma>. if exec_stop \<sigma> then Some(undefined, \<sigma>) 
                                                   else M (A\<^sub>1 \<sigma>) (A\<^sub>2 \<sigma>) (A\<^sub>3 \<sigma>) \<sigma>)"

(* and 4 and 5 and ... *)                        

definition if_C :: "[('\<sigma>_ext) control_state_ext \<Rightarrow> bool, 
                      ('\<beta>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E, 
                      ('\<beta>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E] \<Rightarrow> ('\<beta>, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "if_C c E F = (\<lambda>\<sigma>. if exec_stop \<sigma> 
                              then Some(undefined, \<sigma>)  \<comment> \<open>state unchanged, return arbitrary\<close>
                              else if c \<sigma> then E \<sigma> else F \<sigma>)"     

syntax    (xsymbols)
          "_if_SECLEAN" :: "['\<sigma> \<Rightarrow> bool,('o,'\<sigma>)MON\<^sub>S\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(if\<^sub>C _ then _ else _fi)" [5,8,8]8)
translations 
          "(if\<^sub>C cond then T1 else T2 fi)" == "CONST Clean.if_C cond T1 T2"

          
          
definition while_C :: "(('\<sigma>_ext) control_state_ext \<Rightarrow> bool) 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
  where   "while_C c B \<equiv> (\<lambda>\<sigma>. if exec_stop \<sigma> then Some((), \<sigma>)
                               else ((MonadSE.while_SE (\<lambda> \<sigma>. \<not>exec_stop \<sigma> \<and> c \<sigma>) B) ;- 
                                     unset_break_status) \<sigma>)"
  
syntax    (xsymbols)
          "_while_C" :: "['\<sigma> \<Rightarrow> bool, (unit, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(while\<^sub>C _ do _ od)" [8,8]8)
translations 
          "while\<^sub>C c do b od" == "CONST Clean.while_C c b"

    

section\<open> Global and Local State Management based on Extensible Records \<close>

text\<open>In the following, we add a number of advanced HOL-term constructors in the style of 
@{ML_structure "HOLogic"} from the Isabelle/HOL libraries. They incorporate the construction
of types during term construction in in a bottom-up manner. Consequently, the leafs of such
terms should always be typed and anonymous loose-@{ML "Bound"} variables avoided.\<close>

ML\<open>
(* HOLogic extended *)

fun mk_None ty = let val none = \<^const_name>\<open>Option.option.None\<close>
                     val none_ty = ty --> Type(\<^type_name>\<open>option\<close>,[ty])
                in  Const(none, none_ty)
                end;

fun mk_Some t = let val some = \<^const_name>\<open>Option.option.Some\<close> 
                    val ty = fastype_of t
                    val some_ty = ty --> Type(\<^type_name>\<open>option\<close>,[ty])
                in  Const(some, some_ty) $ t
                end;

fun dest_listTy (Type(\<^type_name>\<open>List.list\<close>, [T])) = T;

fun mk_hdT t = let val ty = fastype_of t 
               in  Const(\<^const_name>\<open>List.hd\<close>, ty --> (dest_listTy ty)) $ t end

fun mk_tlT t = let val ty = fastype_of t 
               in  Const(\<^const_name>\<open>List.tl\<close>, ty --> ty) $ t end


fun  mk_undefined (@{typ "unit"}) = Const (\<^const_name>\<open>Product_Type.Unity\<close>, \<^typ>\<open>unit\<close>)
    |mk_undefined t               = Const (\<^const_name>\<open>HOL.undefined\<close>, t)

fun meta_eq_const T = Const (\<^const_name>\<open>Pure.eq\<close>, T --> T --> propT);

fun mk_meta_eq (t, u) = meta_eq_const (fastype_of t) $ t $ u;

fun   mk_pat_tupleabs [] t = t
    | mk_pat_tupleabs [(s,ty)] t = absfree(s,ty)(t)
    | mk_pat_tupleabs ((s,ty)::R) t = HOLogic.mk_case_prod(absfree(s,ty)(mk_pat_tupleabs R t));

fun read_constname ctxt n = fst(dest_Const(Syntax.read_term ctxt n))

\<close>

text\<open>And here comes the core of the \<^theory_text>\<open>Clean\<close>-State-Management: the module that provides the 
functionality for the commands keywords \<^theory_text>\<open>global_vars\<close>, \<^theory_text>\<open>local_vars\<close>  and \<^theory_text>\<open>local_vars_test\<close>.
Note that the difference between \<^theory_text>\<open>local_vars\<close> and \<^theory_text>\<open>local_vars_test\<close> is just a technical one:
\<^theory_text>\<open>local_vars\<close> can only be used inside a Clean function specification, the \<^theory_text>\<open>function_spec\<close>
command defined below, while \<^theory_text>\<open>local_vars_test\<close> is defined as global Isar command for test purposes. 

A particular feature of the local-variable management is the provision of definitions for \<^term>\<open>push\<close>
and \<^term>\<open>pop\<close> operations --- encoded as \<^theory_text>\<open>('o, '\<sigma>) MON\<^sub>S\<^sub>E\<close> operations --- which are vital for
the function specifications defined below.
\<close>

ML\<open>
structure StateMgt = 
struct

open StateMgt_core

val result_name = "result_value"
fun mk_result_name x = result_name

fun get_result_value_conf name thy = 
        let val  S = filter_attr_of name thy
        in  hd(filter (fn ((_,b),_) => b = result_name) S) 
            handle Empty => error "internal error: get_result_value_conf " end; 


fun mk_lookup_result_value_term name sty thy =
    let val ((prefix,name),local_var(Type("fun", [_,ty]))) = get_result_value_conf name thy;
        val long_name = Sign.intern_const thy (prefix^"."^name)
        val term = Const(long_name, sty --> ty)
    in  mk_hdT (term $ Free("\<sigma>",sty)) end


fun  map_to_update sty is_pop thy ((struct_name, attr_name), local_var (Type("fun",[_,ty]))) term = 
       let val tlT = if is_pop then Const(\<^const_name>\<open>List.tl\<close>, ty --> ty)
                     else Const(\<^const_name>\<open>List.Cons\<close>, dest_listTy ty --> ty --> ty)
                          $ mk_undefined (dest_listTy ty)
           val update_name = Sign.intern_const  thy (struct_name^"."^attr_name^"_update")
       in (Const(update_name, (ty --> ty) --> sty --> sty) $ tlT) $ term end
   | map_to_update _ _ _ ((_, _),_) _ = error("internal error map_to_update")     

fun mk_local_state_name binding = 
       Binding.prefix_name "local_" (Binding.suffix_name "_state" binding)  
fun mk_global_state_name binding = 
       Binding.prefix_name "global_" (Binding.suffix_name "_state" binding)  

fun construct_update is_pop binding sty thy = 
       let val long_name = Binding.name_of( binding)
           val attrS = StateMgt_core.filter_attr_of long_name thy
       in  fold (map_to_update sty is_pop thy) (attrS) (Free("\<sigma>",sty)) end

fun cmd (decl, spec, prems, params) = #2 oo Specification.definition' decl params prems spec


val SPY  = Unsynchronized.ref (Bound 0)
val SPY1 = Unsynchronized.ref (Binding.empty)
val SPY2 =  Unsynchronized.ref (@{typ "unit"})
val SPY3 =  Unsynchronized.ref (@{typ "unit"})


fun mk_push_name binding = Binding.prefix_name "push_" binding

fun push_eq binding  name_op rty sty lthy = 
         let val mty = MON_SE_T rty sty 
             val thy = Proof_Context.theory_of lthy
             val term = construct_update false binding sty thy
         in  mk_meta_eq((Free(name_op, mty) $ Free("\<sigma>",sty)), 
                         mk_Some ( HOLogic.mk_prod (mk_undefined rty,term)))
                          
         end;

fun mk_push_def binding sty lthy =
    let val name_pushop =  mk_push_name binding
        val rty = \<^typ>\<open>unit\<close>
        val eq = push_eq binding  (Binding.name_of name_pushop) rty sty lthy
        (* val mty = StateMgt_core.MON_SE_T rty sty *)
        val args = (SOME(name_pushop,NONE (* SOME mty *),NoSyn), (Binding.empty_atts,eq),[],[])
    in cmd args true lthy  end;

fun mk_pop_name binding = Binding.prefix_name "pop_"  binding

fun pop_eq  binding name_op rty sty lthy = 
         let val mty = MON_SE_T rty sty 
             val thy = Proof_Context.theory_of lthy
             val res_access = mk_lookup_result_value_term (Binding.name_of binding) sty thy
             val term = construct_update true binding  sty thy                 
         in  mk_meta_eq((Free(name_op, mty) $ Free("\<sigma>",sty)), 
                         mk_Some ( HOLogic.mk_prod (res_access,term)))                          
         end;


fun mk_pop_def binding rty sty lthy = 
    let val mty = StateMgt_core.MON_SE_T rty sty 
        val name_op =  mk_pop_name binding
        val eq = pop_eq binding (Binding.name_of name_op) rty sty lthy
        val args = (SOME(name_op,NONE(* SOME mty *),NoSyn),(Binding.empty_atts,eq),[],[])
    in cmd args true lthy
    end;


fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
       (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));


fun read_fields raw_fields ctxt =
  let
    val Ts = Syntax.read_typs ctxt (map (fn (_, raw_T, _) => raw_T) raw_fields);
    val fields = map2 (fn (x, _, mx) => fn T => (x, T, mx)) raw_fields Ts;
    val ctxt' = fold Variable.declare_typ Ts ctxt;
  in (fields, ctxt') end;

fun add_record_cmd0 read_fields overloaded is_global_kind raw_params binding raw_parent raw_fields thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
    val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
    val (parent, ctxt2) = read_parent raw_parent ctxt1;
    val (fields, ctxt3) = read_fields raw_fields ctxt2;
    fun lift (a,b,c) =  (a, HOLogic.listT b, c)
    val fields' = if is_global_kind then fields else map lift fields
    val params' = map (Proof_Context.check_tfree ctxt3) params;
    val declare = StateMgt_core.declare_state_variable_global
    fun upd_state_typ thy = let val ctxt = Proof_Context.init_global thy
                                val ty = Syntax.parse_typ ctxt (Binding.name_of binding)
                            in  StateMgt_core.upd_state_type_global(K ty)(thy) end
    fun insert_var ((f,_,_), thy) =           
            if is_global_kind   
            then declare StateMgt_core.global_var (Binding.name_of f) thy
            else declare StateMgt_core.local_var  (Binding.name_of f) thy
    fun define_push_pop thy = 
            if not is_global_kind 
            then let val ctxt = Proof_Context.init_global thy;
                     val ty_bind =  Binding.prefix_name "'a " (Binding.suffix_name "_scheme" binding)
                     val sty = Syntax.parse_typ ctxt (Binding.name_of ty_bind)
                     val rty = dest_listTy (#2(hd(rev fields')))
                 in thy

                    |> Named_Target.theory_map (mk_push_def binding sty) 
                    |> Named_Target.theory_map (mk_pop_def  binding rty sty) 
                                                            
                 end
            else thy
  in thy |> Record.add_record overloaded (params', binding) parent fields' 
         |> (fn thy =>  List.foldr insert_var (thy) (fields'))
         |> upd_state_typ
         |> define_push_pop 
  end;



fun typ_2_string_raw (Type(s,[TFree _])) = if String.isSuffix "_scheme" s
                                            then Long_Name.base_name(unsuffix "_scheme" s)
                                            else Long_Name.base_name(unsuffix "_ext" s)
                                          
   |typ_2_string_raw (Type(s,_)) = 
                         error ("Illegal parameterized state type - not allowed in Clean:"  ^ s) 
   |typ_2_string_raw _ = error  "Illegal state type - not allowed in Clean." 
                                  
             
fun new_state_record0 add_record_cmd is_global_kind (((raw_params, binding), res_ty), raw_fields) thy =
    let val binding = if is_global_kind 
                      then mk_global_state_name binding
                      else mk_local_state_name binding
        val raw_parent = SOME(typ_2_string_raw (StateMgt_core.get_state_type_global thy))
        val pos = Binding.pos_of binding
        fun upd_state_typ thy = let val ctxt = Proof_Context.init_global thy
                                    val ty_bind =  Binding.prefix_name "'a " 
                                                        (Binding.suffix_name "_scheme" binding)
                                    val ty = Syntax.parse_typ ctxt (Binding.name_of ty_bind)
                                in  StateMgt_core.upd_state_type_global(K ty)(thy) end
        val result_binding = Binding.make(result_name,pos)
        val raw_fields' = case res_ty of 
                            NONE => raw_fields
                          | SOME res_ty => raw_fields @ [(result_binding,res_ty, NoSyn)]
    in  thy |> add_record_cmd {overloaded = false} is_global_kind 
                              raw_params binding raw_parent raw_fields' 
            |> upd_state_typ 

    end

val add_record_cmd    = add_record_cmd0 read_fields;
val add_record_cmd'   = add_record_cmd0 pair;

val new_state_record  = new_state_record0 add_record_cmd
val new_state_record' = new_state_record0 add_record_cmd'

val _ =
  Outer_Syntax.command 
      \<^command_keyword>\<open>global_vars\<close>   
      "define global state record"
      ((Parse.type_args_constrained -- Parse.binding)
    -- Scan.succeed NONE
    -- Scan.repeat1 Parse.const_binding
    >> (Toplevel.theory o new_state_record true));
;

val _ =
  Outer_Syntax.command 
      \<^command_keyword>\<open>local_vars_test\<close>  
      "define local state record"
      ((Parse.type_args_constrained -- Parse.binding) 
    -- (Parse.typ >> SOME)
    -- Scan.repeat1 Parse.const_binding
    >> (Toplevel.theory o new_state_record false))
;
end
\<close>

section\<open>Syntactic Sugar supporting \<open>\<lambda>\<close>-lifting for Global and Local Variables \<close>

ML \<open>
structure Clean_Syntax_Lift =
struct
val SPY4 = Unsynchronized.ref (@{typ "unit"});
val SPY5 = Unsynchronized.ref (Bound 0);
val SPY6 = Unsynchronized.ref (Bound 0);
val SPY7 = Unsynchronized.ref (Bound 0);

  local
    fun mk_local_access X = Const (@{const_name "Fun.comp"}, dummyT) 
                            $ Const (@{const_name "List.list.hd"}, dummyT) $ X
  in
    fun app_sigma db tm ctxt = case tm of
        Const(name, _) => if StateMgt_core.is_global_program_variable name (Proof_Context.theory_of ctxt) 
                          then tm $ (Bound db) (* lambda lifting *)
                          else if StateMgt_core.is_local_program_variable name (Proof_Context.theory_of ctxt) 
                               then (mk_local_access tm) $ (Bound db) (* lambda lifting local *)
                               else tm              (* no lifting *)
      | Free _ => tm
      | Var _ => tm
      | Bound n => if n > db then Bound(n + 1) else Bound n 
      | Abs (x, ty, tm') => Abs(x, ty, app_sigma (db+1) tm' ctxt)
      | t1 $ t2 => (app_sigma db t1 ctxt) $ (app_sigma db t2 ctxt)

    fun scope_var name =
      Proof_Context.theory_of
      #> (fn thy =>
            if StateMgt_core.is_global_program_variable name thy then SOME true
            else if StateMgt_core.is_local_program_variable name thy then SOME false
            else NONE)

    fun assign_update var = var ^ Record.updateN

    fun transform_term0 abs scope_var tm =
      case tm of
         Const (@{const_name "Clean.syntax_assign"}, _)
         $ (t1 as Const ("_type_constraint_", _) $ Const (name, ty))
         $ t2 =>
            Const ( case scope_var name of
                      SOME true => @{const_name "assign_global"}
                    | SOME false => @{const_name "assign_local"}
                    | NONE => raise TERM ("mk_assign", [t1])
                  , dummyT)
            $ Const(assign_update name, ty)
            $ abs t2
       | _ => abs tm

    fun transform_term ctxt sty =
      transform_term0
        (fn tm => Abs ("\<sigma>", sty, app_sigma 0 tm ctxt))
        (fn name => scope_var name ctxt)

    fun transform_term' ctxt = transform_term ctxt dummyT

    fun string_tr ctxt content args =
      let fun err () = raise TERM ("string_tr", args)
      in
        (case args of
          [(Const (@{syntax_const "_constrain"}, _)) $ (Free (s, _)) $ p] =>
            (case Term_Position.decode_position p of
              SOME (pos, _) =>
              let val txt = Symbol_Pos.implode(content (s,pos))
                  val tm = Syntax.parse_term ctxt txt
                  val sty = StateMgt_core.get_state_type ctxt
val _ = (SPY4:=sty) val _ = (SPY5:=tm)
                  val tr = transform_term ctxt sty tm
val _ = (SPY6:=tr)
                  val ct = Syntax.check_term ctxt tr
val _ = (SPY7:=ct)
              in
                ct
              end
            | NONE => err ())
        | _ => err ())
      end
  end
end
\<close>

syntax "_cartouche_string" :: "cartouche_position \<Rightarrow> string"  ("_")

parse_translation \<open>
  [(@{syntax_const "_cartouche_string"},
    (fn ctxt => Clean_Syntax_Lift.string_tr ctxt (Symbol_Pos.cartouche_content o Symbol_Pos.explode)))]
\<close>

section\<open>Support for (direct recursive) Clean Function Specifications \<close>

text\<open>Based on the machinery for the State-Management and  implicitly cooperating with the 
cartouches for assignment syntax, the function specification packages coordinates:
\<^enum> parsing and type-checking of parameters
\<^enum> parsing and type-checking of of pre- and post conditions in MOAL notation
  (using \<open>\<lambda>\<close>-lifting cartouches and implicit reference to parameters, pre- and psot states) 
\<^enum> parsing local variable section and effectuating the local-variable space generation
\<^enum> parsing of the body in this extended variable space
\<^enum> optionally parsing measures and treating recursion.

The reader interested in details is referred to the \<open>Quicksort_concept.thy\<close>-example in this 
distribution.
\<close>

definition old :: "'a \<Rightarrow> 'a" where "old x = x"


ML\<open> 
\<close>

ML \<open> 
structure Function_Specification_Parser  = 
  struct

val SPY = Unsynchronized.ref(Bound 0)

    type funct_spec_src = {    
        binding:  binding,                         (* name *)
        params: (binding*string) list,             (* parameters and their type*)
        ret_type: string,                          (* return type; default unit *)
        locals: (binding*string*mixfix)list,       (* local variables *)
        pre_src: string,                           (* precondition src *)
        post_src: string,                          (* postcondition src *)
        variant_src: string option,                       (* variant src *)
        body_src: string * Position.T              (* body src *)
      }

    type funct_spec_sem = {    
        params: (binding*typ) list,                (* parameters and their type*)
        ret_ty: typ,                               (* return type *)
        pre: term,                                 (* precondition  *)
        post: term,                                (* postcondition  *)
        variant: term option                       (* variant  *)
      }


    val parse_arg_decl = Parse.binding -- (Parse.$$$ "::" |-- Parse.typ)

    val parse_param_decls = Args.parens (Parse.enum "," parse_arg_decl)
      
    val parse_returns_clause = Scan.optional (\<^keyword>\<open>returns\<close> |--  Parse.typ) "unit"
    
    val parse_proc_spec = (
          Parse.binding 
       -- parse_param_decls
       -- parse_returns_clause
      --| \<^keyword>\<open>pre\<close>             -- Parse.term 
      --| \<^keyword>\<open>post\<close>            -- Parse.term 
      --  Scan.option( \<^keyword>\<open>variant\<close> --| Parse.term)
      --| \<^keyword>\<open>local_vars\<close> -- (Scan.repeat1 Parse.const_binding)
   (* --| \<^keyword>\<open>defines\<close>         -- (Parse.position (Parse.cartouche>>cartouche)) *)
      --| \<^keyword>\<open>defines\<close>         -- (Parse.position (Parse.term)) 
      ) >> (fn (((((((binding,params),ret_ty),pre_src),post_src),variant_src),locals),body_src) => 
        {
          binding = binding, 
          params=params, 
          ret_type=ret_ty, 
          pre_src=pre_src, 
          post_src=post_src, 
          variant_src=variant_src,
          locals=locals,
          body_src=body_src} : funct_spec_src
        )

   fun read_params params ctxt =
     let
       val Ts = Syntax.read_typs ctxt (map snd params);
       val params' = map2 (fn (x, _) => fn T => (x, T)) params Ts;
       val ctxt' = fold Variable.declare_typ Ts ctxt;
     in (params', ctxt') end;
   
   fun read_result ret_ty ctxt = 
          let val [ty] = Syntax.read_typs ctxt [ret_ty]
              val ctxt' = Variable.declare_typ ty ctxt           
          in  (ty, ctxt') end

   fun read_function_spec ({ binding ,  params,  ret_type,  pre_src,  post_src, 
                                  variant_src, ...} : funct_spec_src
                               ) ctxt =
       let val (params', ctxt') = read_params params ctxt
           val (rty, ctxt'') = read_result ret_type ctxt' 
           val pre_term = Syntax.read_term ctxt'' pre_src
           val post_term = Syntax.read_term ctxt'' post_src
           val variant = Option.map (Syntax.read_term ctxt'')  variant_src
       in ({params = params',ret_ty = rty,pre = pre_term,post = post_term,variant = variant},ctxt'') end 


   fun check_absence_old term = 
            let fun test (s,ty) = if s = @{const_name "old"} andalso fst (dest_Type ty) = "fun"
                                  then error("the old notation is not allowed here!")  
                                  else false
            in  exists_Const test term end
   
   fun transform_old sty term = 
       let fun  transform_old0 (Const(@{const_name "old"}, ty as Type("fun", [_,_])) $ term ) 
                              = (case term of
                                  (Const(s,ty) $ Bound x) =>  (Const(s,ty) $ Bound (x+1))
                                | _ => error("illegal application of the old notation."))
               |transform_old0 (t1 $ t2) = transform_old0 t1 $ transform_old0 t2
               |transform_old0 (Abs(s,ty,term)) = Abs(s,ty,transform_old0 term) 
               |transform_old0 term = term
       in  Abs("\<sigma>\<^sub>p\<^sub>r\<^sub>e", sty, transform_old0 term) end
   

   fun define_precond binding  sty params pre = 
       let val args_ty = HOLogic.mk_tupleT(map snd params) 
           val params = map (fn (b,r) => (Binding.name_of b,r)) params
           val pre' = case pre of 
                        Abs(nn, sty_pre, term) => mk_pat_tupleabs params (Abs(nn,sty_pre(* sty root ! !*),term))
                      | _ => error ("internal error in define_precond")  
           val bdg_pre = Binding.suffix_name "_pre" binding
           val _ = check_absence_old pre'
           val eq =  mk_meta_eq(Free(Binding.name_of bdg_pre, args_ty --> sty --> HOLogic.boolT),pre')
           val args = (SOME(bdg_pre,NONE,NoSyn), (Binding.empty_atts,eq),[],[]) 
       in  StateMgt.cmd args true end 

   fun define_postcond binding  rty sty params post = 
       let val args_ty = HOLogic.mk_tupleT(map snd params) 
           val params = map (fn (b,r) => (Binding.name_of b,r)) params
           val post = transform_old sty post 
           val post' = case post of 
                        Abs(nn, sty_pre, term) => mk_pat_tupleabs params (Abs(nn,sty_pre(* sty root ! !*),term))
                      | _ => error ("internal error in define_precond")  
           val bdg_post = Binding.suffix_name "_post" binding
           val eq =  mk_meta_eq(Free(Binding.name_of bdg_post, args_ty --> sty --> sty --> rty --> HOLogic.boolT),post')
           val args = (SOME(bdg_post,NONE,NoSyn), (Binding.empty_atts,eq),[],[]) 
       in  StateMgt.cmd args true end 

   fun define_body_core binding rty sty params body ctxt = 
       let val bdg_core = Binding.suffix_name "_core" binding
           val bdg_core_name = Binding.name_of bdg_core

           val args_ty = HOLogic.mk_tupleT(map snd params)
           val params' = map (fn (b,r) => (Binding.name_of b,r)) params
           val _ = writeln "define_body_core"
           val _ = (SPY:=body)
           val core =  mk_pat_tupleabs params'  body
           val rmty = StateMgt_core.MON_SE_T rty sty 
           val umty = StateMgt.MON_SE_T @{typ "unit"} sty

           val eq =  mk_meta_eq(Free(bdg_core_name, args_ty --> umty),core)
           val args_core = (SOME(bdg_core,NONE,NoSyn), (Binding.empty_atts,eq),[],[]) 

       in  ctxt |> StateMgt.cmd args_core true
       end 
 
   fun define_body_main binding rty sty params body ctxt = 
       let val push_name = StateMgt.mk_push_name (StateMgt.mk_local_state_name binding)
           val pop_name = StateMgt.mk_pop_name (StateMgt.mk_local_state_name binding)
           val bdg_core = Binding.suffix_name "_core" binding
           val bdg_core_name = Binding.name_of bdg_core

           val args_ty = HOLogic.mk_tupleT(map snd params)
           val params' = map (fn (b,r) => (Binding.name_of b,r)) params
           val _ = writeln "define_body_main"
           val _ = (SPY:=body)
           val rmty = StateMgt_core.MON_SE_T rty sty 

           val umty = StateMgt.MON_SE_T @{typ "unit"} sty
           val rhs_main = Const(@{const_name "Clean.block\<^sub>C"}, umty --> umty  --> rmty --> rmty)
                          $ Const(read_constname ctxt (Binding.name_of push_name),umty)
                          $ (Const(read_constname ctxt bdg_core_name,args_ty --> umty)  
                             $ HOLogic.mk_tuple (map Free params'))
                          $ Const(read_constname ctxt (Binding.name_of pop_name),rmty)
           val eq_main =  mk_meta_eq(Free(Binding.name_of binding, args_ty --> rmty),
                                     mk_pat_tupleabs params' rhs_main)
           val args_main = (SOME(binding,NONE,NoSyn), (Binding.empty_atts,eq_main),[],[]) 
       in  ctxt |> StateMgt.cmd args_main true 
       end 


   fun checkNsem_function_spec ({variant_src=SOME _, ...} : funct_spec_src) _ = 
                               error "No measure required in non-recursive call"
      |checkNsem_function_spec (args as {binding, ret_type, 
                                         variant_src=NONE, locals, body_src,...} : funct_spec_src) thy =
       let val sty_old = StateMgt_core.get_state_type_global thy
           val ({params,ret_ty,pre,post,...}, ctxt) = read_function_spec args (Proof_Context.init_global thy)
       in  thy  |> Named_Target.theory_map
                         (fn ctxt =>
                          let 
                          in (ctxt |> define_precond binding  sty_old params pre
                                   |> define_postcond binding  ret_ty sty_old params post)  end)
                |> StateMgt.new_state_record false ((([],binding), SOME ret_type),locals)
                |> Named_Target.theory_map
                         (fn ctxt => 
                          let val sty = StateMgt_core.get_state_type ctxt
                              val (_,ctxt') = Variable.add_fixes_binding (map fst params) ctxt (* has this any effect ? *)
                              val body = Syntax.read_term ctxt' (fst body_src)
                          in  ctxt' |> define_body_core binding ret_ty sty params body
                          end)
                |> Named_Target.theory_map
                         (fn ctxt => 
                          let val sty = StateMgt_core.get_state_type ctxt
                              val (_,ctxt') = Variable.add_fixes_binding (map fst params) ctxt (* has this any effect ? *)
                              val body = Syntax.read_term ctxt' (fst body_src)
                          in  ctxt' |> define_body_main binding ret_ty sty params body
                          end)
        end
   (* TODO : further simplify ... *)


   fun checkNsem_rec_function_spec ({ binding ,  params,  ret_type,  pre_src,  post_src,
                                  variant_src,  locals, body_src} : funct_spec_src
                               ) thy = 
        let val _ = case variant_src of 
                      NONE => warning ("no measure provided; measure parameterized")
                     |SOME _ => ()
        in   (warning "rec_function_spec not yet implemented; ignored";thy) end 
   
   val _ =
     Outer_Syntax.command 
         \<^command_keyword>\<open>function_spec\<close>   
         "define Clean function specification"
         (parse_proc_spec >> (Toplevel.theory o checkNsem_function_spec));
   
   val _ =
     Outer_Syntax.command 
         \<^command_keyword>\<open>rec_function_spec\<close>   
         "define recursive Clean function specification"
         (parse_proc_spec >> (Toplevel.theory o checkNsem_rec_function_spec));
       
  end
\<close>


section\<open>Symbolic Execution Rules \<close>


text\<open> ... and we provide syntactic sugar via cartouches \<close>
text\<open> Basic Symbolic execution rules. As they are equalities, they can also
be used as program optimization rules. \<close>

lemma non_exec_assign  : 
assumes "\<not> exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign f; M)) = ((f \<sigma>) \<Turnstile>  M)"
by (simp add: assign_def assms exec_bind_SE_success)

lemma non_exec_assign'  : 
assumes "\<not> exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> (assign f;- M)) = ((f \<sigma>) \<Turnstile>  M)"
by (simp add: assign_def assms exec_bind_SE_success bind_SE'_def)

lemma exec_assign  : 
assumes "exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign f; M)) = (\<sigma> \<Turnstile> M)"
by (simp add: assign_def assms exec_bind_SE_success)     

lemma exec_assign'  : 
assumes "exec_stop \<sigma>"
shows "(\<sigma> \<Turnstile> (assign f;- M)) = (\<sigma> \<Turnstile> M)"
by (simp add: assign_def assms exec_bind_SE_success bind_SE'_def)     

lemma non_exec_assign_global  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign_global upd rhs; M)) = ((upd (\<lambda>_. rhs \<sigma>) \<sigma>) \<Turnstile>  M)"
by(simp add: assign_global_def non_exec_assign assms)

lemma non_exec_assign_global'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (assign_global upd rhs;- M)) = ((upd (\<lambda>_. rhs \<sigma>) \<sigma>) \<Turnstile>  M)"
  by (metis (full_types) assms bind_SE'_def non_exec_assign_global)


lemma exec_assign_global  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign_global upd rhs; M)) = ( \<sigma> \<Turnstile>  M)"
  by (simp add: assign_global_def assign_def assms exec_bind_SE_success)

lemma exec_assign_global'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (assign_global upd rhs;- M)) = ( \<sigma> \<Turnstile>  M)"
  by (simp add: assign_global_def assign_def assms exec_bind_SE_success bind_SE'_def)

lemma non_exec_assign_local  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign_local upd rhs; M)) = ((upd (map_hd (\<lambda>_. rhs \<sigma>)) \<sigma>) \<Turnstile>  M)"
  by(simp add: assign_local_def non_exec_assign assms)

lemma non_exec_assign_local'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (assign_local upd rhs;- M)) = ((upd (map_hd (\<lambda>_. rhs \<sigma>)) \<sigma>) \<Turnstile>  M)"
  by (metis assms bind_SE'_def non_exec_assign_local)


lemma exec_assign_local  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> assign_local upd rhs; M)) = ( \<sigma> \<Turnstile>  M)"
  by (simp add: assign_local_def assign_def assms exec_bind_SE_success)

lemma exec_assign_local'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (assign_global upd rhs;- M)) = ( \<sigma> \<Turnstile>  M)"
  by (simp add: assign_global_def assign_def assms exec_bind_SE_success bind_SE'_def)


lemmas exec_assignD = exec_assign[THEN iffD1]
thm exec_assignD

lemmas exec_assignD' = exec_assign'[THEN iffD1]

lemma non_exec_call_0  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> call_0\<^sub>C M; M')) = (\<sigma> \<Turnstile> M;- M')"
  by (simp add: assms bind_SE'_def bind_SE_def call_0\<^sub>C_def valid_SE_def)

lemma non_exec_call_0'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> call_0\<^sub>C M;- M') = (\<sigma> \<Turnstile> M;- M')"
  by (simp add: assms bind_SE'_def non_exec_call_0)


lemma exec_call_0  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> call_0\<^sub>C M; M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms call_0\<^sub>C_def exec_bind_SE_success)

lemma exec_call_0'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (call_0\<^sub>C M;- M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms bind_SE'_def exec_call_0)




lemma non_exec_call_1  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( x \<leftarrow> (call_1\<^sub>C M A\<^sub>1); M' x)) = (\<sigma> \<Turnstile> (x \<leftarrow> M (A\<^sub>1 \<sigma>); M' x))"
  by (simp add: assms bind_SE'_def call\<^sub>C_def bind_SE_def call_1\<^sub>C_def valid_SE_def)

lemma non_exec_call_1'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> call_1\<^sub>C M A\<^sub>1;- M') = (\<sigma> \<Turnstile>  M (A\<^sub>1 \<sigma>);- M')"
  by (simp add: assms bind_SE'_def non_exec_call_1)


lemma exec_call_1  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( x \<leftarrow> call_1\<^sub>C M A\<^sub>1; M' x)) = (\<sigma> \<Turnstile>  M' undefined)"
  by (simp add: assms call_1\<^sub>C_def call\<^sub>C_def exec_bind_SE_success)

lemma exec_call_1'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (call_1\<^sub>C M A\<^sub>1;- M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms bind_SE'_def exec_call_1)


lemma non_exec_call  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( x \<leftarrow> (call\<^sub>C M A\<^sub>1); M' x)) = (\<sigma> \<Turnstile> (x \<leftarrow> M (A\<^sub>1 \<sigma>); M' x))"
  by (simp add: assms call\<^sub>C_def bind_SE'_def bind_SE_def call_1\<^sub>C_def valid_SE_def)

lemma non_exec_call'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> call\<^sub>C M A\<^sub>1;- M') = (\<sigma> \<Turnstile>  M (A\<^sub>1 \<sigma>);- M')"
  by (simp add: assms bind_SE'_def non_exec_call)


lemma exec_call  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( x \<leftarrow> call\<^sub>C M A\<^sub>1; M' x)) = (\<sigma> \<Turnstile>  M' undefined)"
  by (simp add: assms call\<^sub>C_def call_1\<^sub>C_def exec_bind_SE_success)

lemma exec_call'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (call\<^sub>C M A\<^sub>1;- M')) = (\<sigma> \<Turnstile>  M')"
  by (metis assms call_1\<^sub>C_def exec_call_1')


lemma non_exec_call_2  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> (call_2\<^sub>C M A\<^sub>1 A\<^sub>2); M')) = (\<sigma> \<Turnstile> M (A\<^sub>1 \<sigma>) (A\<^sub>2 \<sigma>);- M')"
  by (simp add: assms bind_SE'_def bind_SE_def call_2\<^sub>C_def valid_SE_def)

lemma non_exec_call_2'  : 
assumes "\<not> exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> call_2\<^sub>C M A\<^sub>1 A\<^sub>2;- M') = (\<sigma> \<Turnstile>  M (A\<^sub>1 \<sigma>) (A\<^sub>2 \<sigma>);- M')"
  by (simp add: assms bind_SE'_def non_exec_call_2)

lemma exec_call_2  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> ( _ \<leftarrow> call_2\<^sub>C M A\<^sub>1 A\<^sub>2; M')) = (\<sigma> \<Turnstile>  M')"
  by (simp add: assms call_2\<^sub>C_def exec_bind_SE_success)

lemma exec_call_2'  : 
assumes "exec_stop \<sigma>"
shows   "(\<sigma> \<Turnstile> (call_2\<^sub>C M A\<^sub>1 A\<^sub>2;- M')) = (\<sigma> \<Turnstile> M')"
  by (simp add: assms bind_SE'_def exec_call_2)


lemma exec_If\<^sub>C_If\<^sub>S\<^sub>E  : 
assumes "\<not> exec_stop \<sigma>"
shows  " ((if\<^sub>C P then B\<^sub>1 else B\<^sub>2 fi))\<sigma> = ((if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi)) \<sigma> "
  unfolding if_SE_def MonadSE.if_SE_def Symbex_MonadSE.valid_SE_def MonadSE.bind_SE'_def
  by (simp add: assms bind_SE_def if_C_def)
    
    
lemma valid_exec_If\<^sub>C  : 
assumes "\<not> exec_stop \<sigma>"
shows  "(\<sigma> \<Turnstile> (if\<^sub>C P then B\<^sub>1 else B\<^sub>2 fi);-M) = (\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi);-M)"
  by (meson assms exec_If\<^sub>C_If\<^sub>S\<^sub>E valid_bind'_cong)


      
lemma exec_If\<^sub>C'  : 
assumes "exec_stop \<sigma>"
shows  "(\<sigma> \<Turnstile> (if\<^sub>C P then B\<^sub>1 else B\<^sub>2 fi);-M) = (\<sigma> \<Turnstile> M)"    
  unfolding if_SE_def MonadSE.if_SE_def Symbex_MonadSE.valid_SE_def MonadSE.bind_SE'_def bind_SE_def
    by (simp add: assms if_C_def)
    
lemma exec_While\<^sub>C'  : 
assumes "exec_stop \<sigma>"
shows  "(\<sigma> \<Turnstile> (while\<^sub>C P do B\<^sub>1 od);-M) = (\<sigma> \<Turnstile> M)"    
  unfolding while_C_def MonadSE.if_SE_def Symbex_MonadSE.valid_SE_def MonadSE.bind_SE'_def bind_SE_def
  apply simp using assms by blast    



section\<open> Tactic Support: we use Eisbach to automate the process. \<close>

txt\<open> Necessary prerequisite: turning ematch and dmatch into a proper Isar Method. \<close>
(* TODO : this code shoud go to TestGen Method setups *)
ML\<open>
val _ =
  Theory.setup
   (Method.setup @{binding ematch}
      (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o (K(ematch_tac ctxt rules)) ))) 
      "fast elimination matching" #>
    Method.setup @{binding dmatch}
      (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o (K(dmatch_tac ctxt rules)) ))) 
       "fast destruction matching" #>
    Method.setup @{binding match}
      (Attrib.thms >> (fn rules => fn ctxt => METHOD (HEADGOAL o (K(match_tac ctxt rules)) )))
       "resolution based on fast matching")
\<close>

txt\<open> Various tactics for various coverage criteria \<close>

definition while_k :: "nat \<Rightarrow> (('\<sigma>_ext) control_state_ext \<Rightarrow> bool) 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E 
                        \<Rightarrow> (unit, ('\<sigma>_ext) control_state_ext)MON\<^sub>S\<^sub>E"
where     "while_k _ \<equiv> while_C"

lemma while_k_SE : "while_C = while_k k"
by (simp only: while_k_def)
    
    
lemma if\<^sub>C_cond_cong : "f \<sigma> = g \<sigma> \<Longrightarrow> 
                           (if\<^sub>C f then c else d fi) \<sigma> = 
                           (if\<^sub>C g then c else d fi) \<sigma>"
  unfolding if_C_def
   by simp 
   
     

lemma while\<^sub>C_skip [simp]: "(while\<^sub>C (\<lambda> x. False) do c od) = skip\<^sub>S\<^sub>E"
  apply(rule ext)
  unfolding while_C_def skip\<^sub>S\<^sub>E_def unit_SE_def
  apply auto
  unfolding exec_stop_def skip\<^sub>S\<^sub>E_def unset_break_status_def bind_SE'_def unit_SE_def bind_SE_def
  by simp
  

lemma break_assign_skip [simp]: "break ;- assign f = break"
  apply(rule ext)
  unfolding break_def assign_def exec_stop_def bind_SE'_def   bind_SE_def
  by auto



lemma break_if_skip [simp]: "break ;- (if\<^sub>C b then c else d fi) = break"
  apply(rule ext)
  unfolding break_def assign_def exec_stop_def if_C_def bind_SE'_def   bind_SE_def
  by auto
    
                       
lemma break_while_skip [simp]: "break ;- (while\<^sub>C b do c od) = break"
  apply(rule ext)
  unfolding while_C_def skip\<^sub>S\<^sub>E_def unit_SE_def bind_SE'_def bind_SE_def break_def exec_stop_def
  by simp

    
lemma unset_break_idem [simp] : 
 "( unset_break_status ;- unset_break_status ;- M) = (unset_break_status ;- M)"
  apply(rule ext)  unfolding unset_break_status_def bind_SE'_def bind_SE_def by auto

lemma return_cancel1_idem [simp] : 
 "( return\<^sub>C X E ;- assign_global X E' ;- M) = ( return\<^sub>C X E ;- M)"
  apply(rule ext, rename_tac "\<sigma>")  
  unfolding unset_break_status_def bind_SE'_def bind_SE_def
            assign_def return\<^sub>C_def assign_global_def assign_local_def
  apply(case_tac "exec_stop \<sigma>")
  apply auto
  by (simp add: exec_stop_def set_return_status_def)
    
lemma return_cancel2_idem [simp] : 
 "( return\<^sub>C X E ;- assign_local X E' ;- M) = ( return\<^sub>C X E ;- M)"
    apply(rule ext, rename_tac "\<sigma>")  
  unfolding unset_break_status_def bind_SE'_def bind_SE_def
            assign_def return\<^sub>C_def assign_global_def assign_local_def
  apply(case_tac "exec_stop \<sigma>")
   apply auto
  by (simp add: exec_stop_def set_return_status_def)


text\<open>Somewhat amazingly, this unfolding lemma crucial for symbolic execution still holds ... 
     Even in the presence of break or return...\<close> 
lemma exec_while\<^sub>C : 
"(\<sigma> \<Turnstile> ((while\<^sub>C b do c od) ;- M)) = 
 (\<sigma> \<Turnstile> ((if\<^sub>C b then c ;- ((while\<^sub>C b do c od) ;- unset_break_status) else skip\<^sub>S\<^sub>E fi)  ;- M))"
proof (cases "exec_stop \<sigma>")
  case True
  then show ?thesis 
    by (simp add: True exec_If\<^sub>C' exec_While\<^sub>C')
next
  case False
  then show ?thesis
    proof (cases "\<not> b \<sigma>")
      case True
      then show ?thesis
        apply(subst valid_bind'_cong)
        using \<open>\<not> exec_stop \<sigma>\<close> apply simp_all
        apply (auto simp: skip\<^sub>S\<^sub>E_def unit_SE_def)
          apply(subst while_C_def, simp)
         apply(subst bind'_cong)
         apply(subst MonadSE.while_SE_unfold)
          apply(subst if\<^sub>S\<^sub>E_cond_cong [of _ _ "\<lambda>_. False"])
          apply simp_all
        apply(subst if\<^sub>C_cond_cong [of _ _ "\<lambda>_. False"], simp add: )
        apply(subst exec_If\<^sub>C_If\<^sub>S\<^sub>E,simp_all)
        by (simp add: exec_stop_def unset_break_status_def)
    next
      case False
      have * : "b \<sigma>"  using False by auto
      then show ?thesis
           unfolding while_k_def 
           apply(subst  while_C_def)
           apply(subst  if_C_def)
           apply(subst  valid_bind'_cong)
            apply (simp add: \<open>\<not> exec_stop \<sigma>\<close>)
           apply(subst  (2) valid_bind'_cong)
            apply (simp add: \<open>\<not> exec_stop \<sigma>\<close>)
            apply(subst MonadSE.while_SE_unfold)
            apply(subst valid_bind'_cong)
            apply(subst bind'_cong)
             apply(subst if\<^sub>S\<^sub>E_cond_cong [of _ _ "\<lambda>_. True"])
              apply(simp_all add:   \<open>\<not> exec_stop \<sigma>\<close> )
            apply(subst bind_assoc', subst bind_assoc')
            proof(cases "c \<sigma>")
              case None
              then show "(\<sigma> \<Turnstile> c;-((while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break_status);-M) =
                         (\<sigma> \<Turnstile> c;-(while\<^sub>C b do c od) ;- unset_break_status ;- M)"
                by (simp add: bind_SE'_def exec_bind_SE_failure)
            next
              case (Some a)
              then show "(\<sigma> \<Turnstile> c ;- ((while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break_status);-M) =
                         (\<sigma> \<Turnstile> c ;- (while\<^sub>C b do c od) ;- unset_break_status ;- M)"
                apply(insert \<open>c \<sigma> = Some a\<close>, subst (asm) surjective_pairing[of a])
                apply(subst exec_bind_SE_success2, assumption)
                apply(subst exec_bind_SE_success2, assumption)
                proof(cases "exec_stop (snd a)")
                  case True
                  then show "(snd a \<Turnstile>((while\<^sub>S\<^sub>E (\<lambda>\<sigma>. \<not> exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break_status);-M)=
                             (snd a \<Turnstile> (while\<^sub>C b do c od) ;- unset_break_status ;- M)"
                       by (metis (no_types, lifting) bind_assoc' exec_While\<^sub>C' exec_skip if_SE_D2' 
                                                  skip\<^sub>S\<^sub>E_def while_SE_unfold)
                next
                  case False
                  then show "(snd a \<Turnstile> ((while\<^sub>S\<^sub>E(\<lambda>\<sigma>. \<not>exec_stop \<sigma> \<and> b \<sigma>) do c od);-unset_break_status);-M)=
                             (snd a \<Turnstile> (while\<^sub>C b do c od) ;- unset_break_status ;- M)"
                          unfolding  while_C_def
                          by(subst (2) valid_bind'_cong,simp)(simp)
                qed       
            qed  
    qed
qed
(* ... although it is, oh my god, amazingly complex to prove. *)
  
corollary exec_while_k : 
"(\<sigma> \<Turnstile> ((while_k (Suc n) b c) ;- M)) = 
 (\<sigma> \<Turnstile> ((if\<^sub>C b then c ;- (while_k n b c) ;- unset_break_status else skip\<^sub>S\<^sub>E fi)  ;- M))"
  by (metis exec_while\<^sub>C while_k_def)
    

lemmas exec_while_kD = exec_while_k[THEN iffD1]

end

  
  