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

theory Quicksort_design
  imports CLEAN_logic.Clean
begin

(*
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


+====================================+
global_vars  (* state *)  
    A :: "int list "


funct swap (i::nat, j :: nat) returns unit 
      pre  "i < length A \<and> j < length A"
      post "length (pre A) = length (A) \<and> \<forall>n. n \<noteq> i \<and> n \<noteq> j \<and> n < length A \<longrightarrow> (pre A)!n = A!n 
            \<and> A!j = (pre A)!i \<and> A!i = (pre A)!j"
      local_vars tmp :: int
      \<open>\<open>tmp := A!i\<close> ;-
       \<open>A[i] := A[j]\<close> ;-   (* A := A[i:=A[j]] *)
       \<open>A[j] := tmp\<close>
      \<close>

funct partition (lo::nat, hi::nat) returns nat
     pre  "True"
     post "True"
     local_vars pivot :: nat  i :: nat  j :: nat
     \<open>\<open>pivot := A!hi\<close> ;-
      \<open>i := lo\<close> ;-
      for\<^sub>C\<^sub>L\<^sub>E\<^sub>A\<^sub>N (j=lo,  hi - 1 ,j++)  
         \<open>if\<^sub>C\<^sub>L\<^sub>E\<^sub>A\<^sub>N \<open>A!j < pivot\<close> then swap(i,j);- \<open>i := i + 1\<close>
                               else Skip;-
         \<close>
      swap(i,j);-
      return(i)
     \<close>
         
funct quicksort(lo::int, hi::int) returns unit
     pre  "True"
     post "True"
     local_vars p :: int     
     \<open>if\<^sub>C\<^sub>L\<^sub>E\<^sub>A\<^sub>N \<open>lo < hi\<close> then
        p := partition(lo, hi) ;-
        quicksort(A, lo, p - 1) ;-
        quicksort(A, p + 1, hi)
      else Skip\<close>
      
*)


global_vars state
    A :: "int list "
ML\<open> val Type(s,t) = StateMgt_core.get_state_type_global @{theory}; \<close>


subsection \<open>Encoding swap in CLEAN\<close>

(* for some strange reason, "result" is no longer a term. term "result" crashes. *)
(* list-lifting should be automatic in local_vars. *)

local_vars local_swap_state
   tmp :: "int list" 
   res :: "unit list"


definition push_local_state_swap :: "(unit,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
  where   "push_local_state_swap \<sigma> = 
                    Some((),\<sigma>\<lparr>local_swap_state.tmp :=  undefined # local_swap_state.tmp \<sigma> \<rparr>)"

definition pop_local_state_swap :: "(unit,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
  where   "pop_local_state_swap \<sigma> = 
                    Some(hd(local_swap_state.res \<sigma>), \<comment> \<open> recall : returns op value \<close>
                                                     \<comment> \<open> which happens to be unit \<close>
                         \<sigma>\<lparr>local_swap_state.tmp:= tl( local_swap_state.tmp \<sigma>) \<rparr>)"


definition swap_core :: "nat \<Rightarrow> nat \<Rightarrow>  (unit,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
    where "swap_core i j \<equiv> ((assign_local tmp_update (\<lambda>\<sigma>. A \<sigma> ! i ))   ;-
                            (assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (i) (A \<sigma> ! j))) ;- 
                            (assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (j) ((hd o tmp) \<sigma>))))" 
thm swap_core_def
(* future input cartouche syntax should be: 
definition swap_core :: "nat => nat =>  (unit,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
   where  "swap_core i j \<equiv> (\<open>tmp := A!i\<close>       ;-
                            \<open>A[i] := A!j)\<close> ;-   
                            \<open>A[j] := tmp\<close>)"
*)

(* a block manages the "dynamically" created fresh instances for the local variables of swap *)
definition swap :: "nat \<Rightarrow> nat \<Rightarrow>  (unit,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
  where   "swap i j \<equiv> block\<^sub>C push_local_state_swap (swap_core i j) pop_local_state_swap"
        
(* TODO : model the contract language. *)
definition swap_contract :: "nat \<Rightarrow> nat \<Rightarrow>  (unit,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
  where   "swap_contract i j \<equiv> undefined "

(* NOTE: If local variables were only used in single-assignment style, it is possible
   to drastically simplify the encoding. These variables were not stored in the state,
   just kept as part of the monadic calculation. The simplifications refer both to 
   calculation as well as well as symbolic execution and deduction. *) 


definition swap' :: "nat \<Rightarrow> nat \<Rightarrow>  (unit,'a state_scheme) MON\<^sub>S\<^sub>E"
    where "swap' i j \<equiv> (tmp \<leftarrow>  yield\<^sub>C (\<lambda>\<sigma>. A \<sigma> ! i) ;
                          ((assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (i) (A \<sigma> ! j))) ;- 
                           (assign_global A_update (\<lambda>\<sigma>. list_update (A \<sigma>) (j) (tmp)))))" 
(* Note that all local variables are single-assigned in swap, the entire local var definition
   can be ommitted *) 

subsection \<open>Encoding partition in CLEAN\<close>

(* recall: list-lifting should be automatic in local_vars. *)
local_vars  local_partition_state
    pivot  :: "int list"
    i      :: "nat list"
    j      :: "nat list"
    res    :: "nat list"

(* this implies the definitions : *)
definition push_local_partition_state :: "(unit, 'a local_partition_state_scheme) MON\<^sub>S\<^sub>E"
  where   "push_local_partition_state \<sigma> = Some((),
                        \<sigma>\<lparr>local_partition_state.pivot := undefined # local_partition_state.pivot \<sigma>, 
                          local_partition_state.i     := undefined # local_partition_state.i \<sigma>, 
                          local_partition_state.j     := undefined # local_partition_state.j \<sigma>, 
                          local_partition_state.res   := undefined # local_partition_state.res \<sigma> \<rparr>)"

definition pop_local_partition_state :: "(nat,'a local_partition_state_scheme) MON\<^sub>S\<^sub>E" 
  where   "pop_local_partition_state \<sigma> = Some(hd(local_partition_state.res \<sigma>),
                       \<sigma>\<lparr>local_partition_state.pivot := tl(local_partition_state.pivot \<sigma>), 
                         local_partition_state.i     := tl(local_partition_state.i \<sigma>), 
                         local_partition_state.j     := tl(local_partition_state.j \<sigma>), 
                         local_partition_state.res   := tl(local_partition_state.res \<sigma>) \<rparr>)"


definition partition_core :: "nat \<Rightarrow> nat \<Rightarrow>  (unit,'a local_partition_state_scheme) MON\<^sub>S\<^sub>E"
  where   "partition_core lo hi \<equiv> 
              ((assign_local pivot_update (\<lambda>\<sigma>. A \<sigma> ! hi ))   ;- 
               (assign_local i_update (\<lambda>\<sigma>. lo )) ;-
 
               (assign_local j_update (\<lambda>\<sigma>. lo )) ;-
               (while\<^sub>C (\<lambda>\<sigma>. (hd o j) \<sigma> \<le> hi - 1 ) 
                do (if\<^sub>C (\<lambda>\<sigma>. A \<sigma> ! (hd o j) \<sigma> < (hd o pivot)\<sigma> ) 
                    then  call_2\<^sub>C (swap) (\<lambda>\<sigma>. (hd o i) \<sigma>) (\<lambda>\<sigma>. (hd o j) \<sigma>)  ;-
                          assign_local i_update (\<lambda>\<sigma>. ((hd o i) \<sigma>) + 1)
                    else skip\<^sub>S\<^sub>E 
                    fi) 
                od) ;-
               (assign_local j_update (\<lambda>\<sigma>. ((hd o j) \<sigma>) + 1)) ;-
                call_2\<^sub>C (swap) (\<lambda>\<sigma>. (hd o i) \<sigma>) (\<lambda>\<sigma>. (hd o j) \<sigma>)  ;-
                assign_local res_update (\<lambda>\<sigma>. (hd o i) \<sigma>)  \<comment> \<open> the meaning of the return stmt \<close>
               )"

thm partition_core_def

(* a block manages the "dynamically" created fresh instances for the local variables of swap *)
definition partition :: "nat \<Rightarrow> nat \<Rightarrow>  (nat,'a local_partition_state_scheme) MON\<^sub>S\<^sub>E"
  where   "partition lo hi \<equiv> block\<^sub>C push_local_partition_state 
                                    (partition_core lo hi) 
                                    pop_local_partition_state"
        
(* TODO : model the contract language. *)
definition partition_contract :: "nat \<Rightarrow> nat \<Rightarrow>  (nat,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
  where   "partition_contract lo hi \<equiv> undefined "

(*
    \<open>\<open>pivot := A!hi\<close> ;-
      \<open>i := lo\<close> ;-
      for\<^sub>C\<^sub>L\<^sub>E\<^sub>A\<^sub>N (j=lo,  hi - 1 ,j++)  
         \<open>if\<^sub>C\<^sub>L\<^sub>E\<^sub>A\<^sub>N \<open>A!j < pivot\<close> then swap(i,j);- \<open>i := i + 1\<close>
                               else Skip;-
         \<close>
      swap(i,j);-
      return(i)
     \<close>
*)         

subsection \<open>Encoding quicksort in CLEAN\<close>

local_vars  local_quicksort_state
    p  :: "nat list"
    res:: "unit list"


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

(* this implies the definitions : *)
definition push_local_quicksort_state :: "(unit, 'a local_quicksort_state_scheme) MON\<^sub>S\<^sub>E"
  where   "push_local_quicksort_state \<sigma> = 
                 Some((), \<sigma>\<lparr>local_quicksort_state.p := undefined # local_quicksort_state.p \<sigma>,
                            local_quicksort_state.res := undefined # local_quicksort_state.res \<sigma> \<rparr>)"

definition pop_local_quicksort_state :: "(unit,'a local_quicksort_state_scheme) MON\<^sub>S\<^sub>E" 
  where   "pop_local_quicksort_state \<sigma> = Some(hd(local_quicksort_state.res \<sigma>),
                       \<sigma>\<lparr>local_quicksort_state.p   := tl(local_quicksort_state.p \<sigma>), 
                         local_quicksort_state.res := tl(local_quicksort_state.res \<sigma>) \<rparr>)"

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

axiomatization  quicksort_core :: "nat \<Rightarrow> nat \<Rightarrow> (unit,'a local_quicksort_state_scheme) MON\<^sub>S\<^sub>E"
           and  quicksort      :: "nat \<Rightarrow> nat \<Rightarrow> (unit,'a local_quicksort_state_scheme) MON\<^sub>S\<^sub>E" 

  where  core: "quicksort_core lo hi \<equiv> 
                  ((if\<^sub>C (\<lambda>\<sigma>. lo < hi ) 
                    then (p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call_2\<^sub>C (partition) (\<lambda>\<sigma>. lo) (\<lambda>\<sigma>. hi) ;
                          assign_local p_update (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p)) ;-
                          call_2\<^sub>C (quicksort) (\<lambda>\<sigma>. lo) (\<lambda>\<sigma>. (hd o p) \<sigma> - 1)  ;-
                          call_2\<^sub>C (quicksort) (\<lambda>\<sigma>. (hd o p) \<sigma> + 1) (\<lambda>\<sigma>. hi)  
                    else skip\<^sub>S\<^sub>E 
                    fi))"


  and   block: "quicksort lo hi \<equiv> block\<^sub>C push_local_quicksort_state 
                                         (quicksort_core lo hi) 
                                         pop_local_quicksort_state"

(* bric a brac *)
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


end