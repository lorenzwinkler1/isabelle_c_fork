(******************************************************************************
 * Isabelle/C
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
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

section \<open> Clean Semantics : A Coding-Concept Example\<close>

text\<open>The following show-case introduces subsequently a non-trivial example involving
local and global variable declarations, declarations of operations with pre-post conditions as
well as direct-recursive operations (i.e. C-like functions with side-effects on global and
local variables. \<close>

theory Quicksort_concept
  imports Clean.Clean
begin

section\<open>The Quicksort Example\<close>

text\<open> We present the following quicksort algorithm in some conceptual, high-level notation:

\begin{isar}
algorithm (A,i,j) =
    tmp := A[i];
    A[i]:=A[j];
    A[j]:=tmp

algorithm partition(A, lo, hi) is
    pivot := A[hi]
    i := lo
    for j := lo to hi - 1 do
        if A[j] < pivot then
            swap A[i] with A[j]
            i := i + 1
    swap A[i] with A[hi]
    return i

algorithm quicksort(A, lo, hi) is
    if lo < hi then
        p := partition(A, lo, hi)
        quicksort(A, lo, p - 1)
        quicksort(A, p + 1, hi)

\end{isar}
\<close>

text\<open>In the following, we will present the Quicksort program alternatingly in Clean high-level
notation and simulate its effect by an alternative formalisation representing the semantic
effects of the high-level notation on a step-buy-step basis. Note that Clean does not posses
the concept of call-by-reference parameters; consequently, the algorithm must be specialized 
to a variant where @{term A} is just a global variable.\<close>

section\<open>Clean Encoding of the Global State of Quicksort\<close>

text\<open>We demonstrate the accumulating effect of some key Clean commands by highlighting the 
changes of  Clean's state-management module state. At the beginning, the state-type of 
the Clean state management is just the type of the @{typ "'a Clean.control_state.control_state_ext"},
while the table of global and local variables is empty.\<close>

ML\<open> val Type(s,t) = StateMgt_core.get_state_type_global @{theory};
    StateMgt_core.get_state_field_tab_global @{theory}; \<close>

text\<open>The \<open>global_vars\<close> command, described and defined in \<^verbatim>\<open>Clean.thy\<close>,
declares the global variable \<^verbatim>\<open>A\<close>. This has the following effect:\<close>

global_vars state
    A :: "int list"

text\<open>... which is reflected in Clean's state-management table:\<close>
ML\<open> val Type("Quicksort_concept.global_state_state_scheme",t) 
        = StateMgt_core.get_state_type_global @{theory};
    StateMgt_core.get_state_field_tab_global @{theory}\<close>
text\<open>Note that the state-management uses long-names for complete disambiguation.\<close>


subsection \<open>Encoding swap in Clean\<close>

subsubsection \<open>\<^verbatim>\<open>swap\<close> in High-level Notation\<close>

text\<open>Unfortunately, the name \<open>result\<close> is already used in the logical context; we use local binders
instead.\<close>
definition "i = ()" \<comment> \<open>check that \<^term>\<open>i\<close> can exist as a constant with an arbitrary type before treating \<^theory_text>\<open>function_spec\<close>\<close>
definition "j = ()" \<comment> \<open>check that \<^term>\<open>j\<close> can exist as a constant with an arbitrary type before treating \<^theory_text>\<open>function_spec\<close>\<close>
function_spec swap (i::"nat",j::"nat") \<comment> \<open>TODO: the hovering on parameters produces a number of report equal to the number of \<^ML>\<open>Proof_Context.add_fixes\<close> called in \<^ML>\<open>Function_Specification_Parser.checkNsem_function_spec\<close>\<close>
pre          "\<open>i < length A \<and> j < length A\<close>"    
post         "\<open>\<lambda>res. length A = length(old A) \<and> res = ()\<close>" 
local_vars   tmp :: int 
defines      " \<open> tmp := A ! i\<close>  ;-
               \<open> A := list_update A i (A ! j)\<close> ;- 
               \<open> A := list_update A j tmp\<close> " 

text\<open>The body --- heavily using the \<open>\<lambda>\<close>-lifting cartouche --- corresponds to the low level 
term: \<close>

text\<open> @{cartouche [display=true]
\<open>\<open>defines " ((assign_local tmp_update (\<lambda>\<sigma>. (A \<sigma>) ! i ))   ;-
            (assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (i) (A \<sigma> ! j))) ;- 
            (assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (j) ((hd o tmp) \<sigma>))))"\<close>\<close>}\<close>

text\<open>The effect of this statement is generation of the following definitions in the logical context:\<close>
term "(i, j)" \<comment> \<open>check that \<^term>\<open>i\<close> and \<^term>\<open>j\<close> are pointing to the constants defined before treating \<^theory_text>\<open>function_spec\<close>\<close>
thm push_local_swap_state_def
thm pop_local_swap_state_def
thm swap_pre_def
thm swap_post_def
thm swap_core_def
thm swap_def

text\<open>The state-management is in the following configuration:\<close>

ML\<open> val Type(s,t) = StateMgt_core.get_state_type_global @{theory};
    StateMgt_core.get_state_field_tab_global @{theory}\<close>

subsubsection \<open>A Similation of \<^verbatim>\<open>swap\<close> in elementary specification constructs:\<close>

text\<open>Note that we prime identifiers in order to avoid confusion with the definitions of the
previous section. The pre- and postconditions are just definitions of the following form:\<close>

definition swap'_pre :: " nat \<times> nat \<Rightarrow> 'a global_state_state_scheme \<Rightarrow> bool"
  where "swap'_pre \<equiv> \<lambda>(i, j) \<sigma>. i < length (A \<sigma>) \<and> j < length (A \<sigma>)"
definition swap'_post :: "'a \<times> 'b \<Rightarrow> 'c global_state_state_scheme \<Rightarrow> 'd global_state_state_scheme \<Rightarrow> unit \<Rightarrow> bool"
  where "swap'_post \<equiv> \<lambda>(i, j) \<sigma>\<^sub>p\<^sub>r\<^sub>e \<sigma> res. length (A \<sigma>) = length (A \<sigma>\<^sub>p\<^sub>r\<^sub>e) \<and> res = ()"
text\<open>The somewhat vacuous parameter \<open>res\<close> for the result of the swap-computation is the conseqeuence 
of the implicit definition of the return-type as @{typ "unit"}\<close>

text\<open>We simulate the effect of the local variable space declaration by the following command
     factoring out the functionality into the command \<open>local_vars_test\<close> \<close>
(*
local_vars_test swap' "unit"
   tmp :: "int"

ML\<open>
val Type(s,t) = StateMgt_core.get_state_type_global @{theory};
val tab = StateMgt_core.get_state_field_tab_global @{theory};
@{term "A::('a local_swap_state_scheme\<Rightarrow> int list)"}\<close>

text\<open>This has already the effect of the definition:\<close>
thm push_local_swap_state_def
thm pop_local_swap_state_def

text\<open>Again, we simulate the effect of this command by more elementary \HOL specification constructs:\<close>
(* Thus, the internal functionality in \<open>local_vars\<close> is the construction of the two definitions *)
definition push_local_swap_state' :: "(unit,'a local_swap'_state_scheme) MON\<^sub>S\<^sub>E"
  where   "push_local_swap_state' \<sigma> = 
                    Some((),\<sigma>\<lparr>local_swap_state.tmp :=  undefined # local_swap_state.tmp \<sigma> \<rparr>)"

definition pop_local_swap_state' :: "(unit,'a local_swap'_state_scheme) MON\<^sub>S\<^sub>E"
  where   "pop_local_swap_state' \<sigma> = 
                    Some(hd(local_swap_state.result_value \<sigma>), 
                                \<comment> \<open> recall : returns op value \<close>
                                \<comment> \<open> which happens to be unit \<close>
                         \<sigma>\<lparr>local_swap_state.tmp:= tl( local_swap_state.tmp \<sigma>) \<rparr>)"


definition swap'_core :: "nat \<times> nat \<Rightarrow>  (unit,'a local_swap'_state_scheme) MON\<^sub>S\<^sub>E"
    where "swap'_core  \<equiv> (\<lambda>(i,j). ((assign_local tmp_update (\<lambda>\<sigma>. A \<sigma> ! i ))   ;-
                            (assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (i) (A \<sigma> ! j))) ;- 
                            (assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (j) ((hd o tmp) \<sigma>)))))" 
thm swap_core_def


text\<open> a block manages the "dynamically" created fresh instances for the local variables of swap \<close>
definition swap' :: "nat \<times> nat \<Rightarrow>  (unit,'a local_swap'_state_scheme) MON\<^sub>S\<^sub>E"
  where   "swap' \<equiv> \<lambda>(i,j). block\<^sub>C push_local_swap_state' (swap_core (i,j)) pop_local_swap_state'"


text\<open>NOTE: If local variables were only used in single-assignment style, it is possible
   to drastically simplify the encoding. These variables were not stored in the state,
   just kept as part of the monadic calculation. The simplifications refer both to 
   calculation as well as well as symbolic execution and deduction.\<close>

text\<open>The could be represented by the following alternative, optimized version :\<close>
definition swap_opt :: "nat \<times> nat \<Rightarrow>  (unit,'a global_state_state_scheme) MON\<^sub>S\<^sub>E"
    where "swap_opt \<equiv> \<lambda>(i,j). (tmp \<leftarrow>  yield\<^sub>C (\<lambda>\<sigma>. A \<sigma> ! i) ;
                          ((assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (i) (A \<sigma> ! j))) ;- 
                           (assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (j) (tmp)))))" 
text\<open>In case that all local variables are single-assigned in swap, the entire local var definition
   could be ommitted.\<close>
*)

subsection \<open>Encoding partition in Clean\<close>

function_spec partition (lo::nat, hi::nat) returns nat
pre          "\<open>lo < length A \<and> hi < length A\<close>"    
post         "\<open>\<lambda>res::nat. length A = length(old A) \<and> res = 3\<close>" 
local_vars   pivot  :: int
             i      :: nat
             j      :: nat
defines      " (\<open>pivot := A ! hi \<close>  ;- \<open>i := lo \<close> ;- \<open>j := lo \<close> ;-
               (while\<^sub>C \<open>j \<le> hi - 1 \<close> 
                do (if\<^sub>C \<open>A ! j < pivot\<close>  
                    then  call\<^sub>C swap \<open>(i , j) \<close>  ;-
                          \<open>i := i + 1 \<close>
                    else skip\<^sub>S\<^sub>E 
                    fi) ;-
                    \<open>j := j + 1 \<close> 
                od) ;-
                call\<^sub>C swap \<open>(i, j)\<close>  ;-
                return\<^sub>C result_value_update \<open>i\<close>   
               ) " 

text\<open> The body is a fancy syntax for :

@{cartouche [display=true]
\<open>\<open>defines      " ((assign_local pivot_update (\<lambda>\<sigma>. A \<sigma> ! hi ))   ;- 
               (assign_local i_update (\<lambda>\<sigma>. lo )) ;-
 
               (assign_local j_update (\<lambda>\<sigma>. lo )) ;-
               (while\<^sub>C (\<lambda>\<sigma>. (hd o j) \<sigma> \<le> hi - 1 ) 
                do (if\<^sub>C (\<lambda>\<sigma>. A \<sigma> ! (hd o j) \<sigma> < (hd o pivot)\<sigma> ) 
                    then  call\<^sub>C (swap) (\<lambda>\<sigma>. ((hd o i) \<sigma>,  (hd o j) \<sigma>))  ;-
                          assign_local i_update (\<lambda>\<sigma>. ((hd o i) \<sigma>) + 1)
                    else skip\<^sub>S\<^sub>E 
                    fi) ;-
                    (assign_local j_update (\<lambda>\<sigma>. ((hd o j) \<sigma>) + 1)) 
                od) ;-
                call\<^sub>C (swap) (\<lambda>\<sigma>. ((hd o i) \<sigma>,  (hd o j) \<sigma>))  ;-
                assign_local result_value_update (\<lambda>\<sigma>. (hd o i) \<sigma>)  
                \<comment> \<open> the meaning of the return stmt \<close>
               ) "\<close>\<close>}\<close>


text\<open>The effect of this statement is generation of the following definitions in the logical context:\<close>
thm partition_pre_def
thm partition_post_def
thm push_local_partition_state_def
thm pop_local_partition_state_def
thm partition_core_def
thm partition_def

text\<open>The state-management is in the following configuration:\<close>

ML\<open> val Type(s,t) = StateMgt_core.get_state_type_global @{theory};
    StateMgt_core.get_state_field_tab_global @{theory}\<close>

subsubsection \<open>A Similation of \<^verbatim>\<open>partition\<close> in elementary specification constructs:\<close>

definition "partition'_pre \<equiv> \<lambda>(lo, hi) \<sigma>. lo < length (A \<sigma>) \<and> hi < length (A \<sigma>)"
definition "partition'_post \<equiv> \<lambda>(lo, hi) \<sigma>\<^sub>p\<^sub>r\<^sub>e \<sigma> res. length (A \<sigma>) = length (A \<sigma>\<^sub>p\<^sub>r\<^sub>e) \<and> res = 3"

text\<open>Recall: list-lifting is automatic in \<open>local_vars_test\<close>:\<close>

local_vars_test  partition' "nat"
    pivot  :: "int"
    i      :: "nat"
    j      :: "nat"

text\<open> ... which results in the internal definition of the respective push and pop operations 
for the @{term "partition'"} local variable space: \<close>

thm push_local_partition'_state_def
thm pop_local_partition'_state_def

(* equivalent to *)
definition push_local_partition_state' :: "(unit, 'a local_partition'_state_scheme) MON\<^sub>S\<^sub>E"
  where   "push_local_partition_state' \<sigma> = Some((),
                        \<sigma>\<lparr>local_partition_state.pivot := undefined # local_partition_state.pivot \<sigma>, 
                          local_partition_state.i     := undefined # local_partition_state.i \<sigma>, 
                          local_partition_state.j     := undefined # local_partition_state.j \<sigma>, 
                          local_partition_state.result_value   
                                           := undefined # local_partition_state.result_value \<sigma> \<rparr>)"

definition pop_local_partition_state' :: "(nat,'a local_partition_state_scheme) MON\<^sub>S\<^sub>E" 
  where   "pop_local_partition_state' \<sigma> = Some(hd(local_partition_state.result_value \<sigma>),
                       \<sigma>\<lparr>local_partition_state.pivot := tl(local_partition_state.pivot \<sigma>), 
                         local_partition_state.i     := tl(local_partition_state.i \<sigma>), 
                         local_partition_state.j     := tl(local_partition_state.j \<sigma>), 
                         local_partition_state.result_value := 
                                                        tl(local_partition_state.result_value \<sigma>) \<rparr>)"


definition partition'_core :: "nat \<times> nat \<Rightarrow>  (unit,'a local_partition'_state_scheme) MON\<^sub>S\<^sub>E"
  where   "partition'_core  \<equiv> \<lambda>(lo,hi).
              ((assign_local pivot_update (\<lambda>\<sigma>. A \<sigma> ! hi ))   ;- 
               (assign_local i_update (\<lambda>\<sigma>. lo )) ;-
 
               (assign_local j_update (\<lambda>\<sigma>. lo )) ;-
               (while\<^sub>C (\<lambda>\<sigma>. (hd o j) \<sigma> \<le> hi - 1 ) 
                do (if\<^sub>C (\<lambda>\<sigma>. A \<sigma> ! (hd o j) \<sigma> < (hd o pivot)\<sigma> ) 
                    then  call\<^sub>C (swap) (\<lambda>\<sigma>. ((hd o i) \<sigma>,  (hd o j) \<sigma>))  ;-
                          assign_local i_update (\<lambda>\<sigma>. ((hd o i) \<sigma>) + 1)
                    else skip\<^sub>S\<^sub>E 
                    fi) 
                od) ;-
               (assign_local j_update (\<lambda>\<sigma>. ((hd o j) \<sigma>) + 1)) ;-
                call\<^sub>C (swap) (\<lambda>\<sigma>. ((hd o i) \<sigma>,  (hd o j) \<sigma>))  ;-
                assign_local result_value_update (\<lambda>\<sigma>. (hd o i) \<sigma>)  
                \<comment> \<open> the meaning of the return stmt \<close>
               )"

thm partition_core_def

(* a block manages the "dynamically" created fresh instances for the local variables of swap *)
definition partition' :: "nat \<times> nat \<Rightarrow>  (nat,'a local_partition'_state_scheme) MON\<^sub>S\<^sub>E"
  where   "partition'  \<equiv> \<lambda>(lo,hi). block\<^sub>C push_local_partition_state 
                                   (partition_core (lo,hi)) 
                                   pop_local_partition_state"
             

subsection \<open>Encoding the core: quicksort in Clean\<close>


local_vars_test  quicksort' "unit"
    p  :: "nat"


ML\<open> val (x,y) = StateMgt_core.get_data_global @{theory}; \<close>

(*
funct quicksort(lo::nat, hi::nat) returns unit
     pre  "True"
     post "True"
     local_vars p :: int     
     \<open>if\<^sub>C\<^sub>L\<^sub>E\<^sub>A\<^sub>N \<open>lo < hi\<close> then
        p := partition(lo, hi) ;-
        quicksort(A, lo, p - 1) ;-
        quicksort(A, p + 1, hi)
      else Skip\<close>
      
*)

 



thm pop_local_quicksort'_state_def
thm push_local_quicksort'_state_def

(* this implies the definitions : *)
definition push_local_quicksort_state' :: "(unit, 'a local_quicksort'_state_scheme) MON\<^sub>S\<^sub>E"
  where   "push_local_quicksort_state' \<sigma> = 
                 Some((), \<sigma>\<lparr>local_quicksort'_state.p := undefined # local_quicksort'_state.p \<sigma>,
                            local_quicksort'_state.result_value := undefined # local_quicksort'_state.result_value \<sigma> \<rparr>)"




definition pop_local_quicksort_state' :: "(unit,'a local_quicksort'_state_scheme) MON\<^sub>S\<^sub>E"
  where   "pop_local_quicksort_state' \<sigma> = Some(hd(local_quicksort'_state.result_value \<sigma>),
                       \<sigma>\<lparr>local_quicksort'_state.p   := tl(local_quicksort'_state.p \<sigma>), 
                         local_quicksort'_state.result_value := 
                                                      tl(local_quicksort'_state.result_value \<sigma>) \<rparr>)"

(* recursion not yet treated. Either axiomatazitation hack (super-dangerous) or 
   proper formalization via lfp. *)

(*
funct quicksort(lo::int, hi::int) returns unit
     pre  "True"
     post "True"
     local_vars p :: int     
     \<open>if\<^sub>C\<^sub>L\<^sub>E\<^sub>A\<^sub>N \<open>lo < hi\<close> then
        p := partition(lo, hi) ;-
        quicksort(lo, p - 1) ;-
        quicksort(p + 1, hi)
      else Skip\<close>
      
*)

definition quicksort'_pre :: "nat \<times> nat \<Rightarrow> 'a local_quicksort'_state_scheme \<Rightarrow>   bool"
  where   "quicksort'_pre \<equiv> \<lambda>(i,j). \<lambda>\<sigma>.  True "

definition quicksort'_post :: "nat \<times> nat \<Rightarrow> unit \<Rightarrow> 'a local_quicksort'_state_scheme \<Rightarrow>  bool"
  where   "quicksort'_post \<equiv> \<lambda>(i,j). \<lambda> res. \<lambda>\<sigma>.  True"   


definition quicksort'_core :: "   (nat \<times> nat \<Rightarrow> (unit,'a local_quicksort'_state_scheme) MON\<^sub>S\<^sub>E)
                              \<Rightarrow> (nat \<times> nat \<Rightarrow> (unit,'a local_quicksort'_state_scheme) MON\<^sub>S\<^sub>E)"
  where   "quicksort'_core quicksort \<equiv> \<lambda>(lo, hi). 
                            ((if\<^sub>C (\<lambda>\<sigma>. lo < hi ) 
                              then (p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C partition (\<lambda>\<sigma>. (lo, hi)) ;
                                    assign_local p_update (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p)) ;-
                                    call\<^sub>C quicksort (\<lambda>\<sigma>. (lo, (hd o p) \<sigma> - 1)) ;-
                                    call\<^sub>C quicksort (\<lambda>\<sigma>. ((hd o p) \<sigma> + 1, hi))  
                              else skip\<^sub>S\<^sub>E 
                              fi))"

term " ((quicksort'_core X) (lo,hi))"

definition quicksort' :: " ((nat \<times> nat) \<times> (nat \<times> nat)) set \<Rightarrow>
                           (nat \<times> nat \<Rightarrow> (unit,'a local_quicksort'_state_scheme) MON\<^sub>S\<^sub>E)"
  where   "quicksort' order \<equiv> wfrec order (\<lambda>X. \<lambda>(lo, hi). block\<^sub>C push_local_quicksort'_state 
                                                                (quicksort'_core X (lo,hi)) 
                                                                pop_local_quicksort'_state)"






ML\<open>
fun wfrecT order recs = 
    let val funT = domain_type (fastype_of recs)
        val aTy  = domain_type funT
        val ordTy = HOLogic.mk_setT(HOLogic.mk_prodT (aTy,aTy))
    in Const(@{const_name "Wfrec.wfrec"},ordTy --> (funT --> funT) --> funT) $ order $ recs end

\<close>


(* bric a brac *)

definition "zz = ()"
ML\<open>@{term zz}\<close>  (* So : @(term "zz"} is now a constant*) 
ML\<open>Proof_Context.add_fixes [(@{binding "zz"}, SOME @{typ nat}, NoSyn)] @{context}
   |> (fn (S, ctxt) => (writeln (String.concat S); Syntax.read_term ctxt "zz")) \<close>
ML\<open>@{term zz}\<close>  (* So : @(term "zz"} is now a constant*) 
locale Z =
  fixes zz :: nat
begin
ML\<open>@{term "(zz)"}\<close>
end

lemma True
proof - fix a :: nat
  show True
    ML_prf \<open>@{term a}\<close>
    term a
    oops




term "Clean.syntax_assign"
term "B[x:=(B!n)]"
term "assign_local tmp_update (\<lambda>\<sigma>. A \<sigma> ! n )"  
term "assign(\<lambda>\<sigma>. ((upd o map_hd) (f \<sigma>)) \<sigma>)"

term "assign "
(*term "(A \<sigma>[n := A \<sigma> ! m]) = list_update (A \<sigma>) (n) (A \<sigma> ! m)"*)

term "assign(\<lambda>\<sigma>. ((A_update ) (\<lambda>_. list_update (A \<sigma>) (n) (A \<sigma> ! n))) \<sigma>)"
term " ((A_update o map_hd) f)"
term " body\<^sub>C push_local_state_swap pop_local_state_swap "
term "assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (n) (A \<sigma> ! m))"

term "B[k:=(B!m)]"


rec_function_spec quicksort (lo::nat, hi::nat) returns "unit"
pre          "\<open>True\<close>"
post         "\<open>\<lambda>res::unit. True\<close>"
(* variant      "XXX" *)
local_vars   p :: "nat" 
(*
defines      "call\<^sub>C (quicksort :: (nat \<times> nat \<Rightarrow> (unit, 'a local_quicksort_state_scheme) MON\<^sub>S\<^sub>E )) 
                    (\<lambda>\<sigma>. (lo, (hd o p) \<sigma> - hi))"
*)

defines      " ((if\<^sub>C (\<lambda>\<sigma>. lo < hi ) 
                 then (p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C partition (\<lambda>\<sigma>. (lo, hi)) ;
                       assign_local p_update (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p)) ;-
                       call\<^sub>C quicksort (\<lambda>\<sigma>. (lo, (hd o p) \<sigma> - 1)) ;-
                       call\<^sub>C quicksort (\<lambda>\<sigma>. ((hd o p) \<sigma> + 1, hi))  
                 else skip\<^sub>S\<^sub>E 
                 fi))"


thm quicksort_core_def

ML\<open>           val measure = @{term "Wellfounded.measure"}
\<close>
declare [[ML_print_depth=100]]

ML\<open>!Function_Specification_Parser.SPY1\<close>

ML\<open>!Function_Specification_Parser.SPY2\<close>

ML\<open>!Function_Specification_Parser.SPY3\<close>

end
