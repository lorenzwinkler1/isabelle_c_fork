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
    A :: "int list"


ML\<open> val Type(s,t) = StateMgt_core.get_state_type_global @{theory};
    StateMgt_core.get_state_field_tab_global @{theory}\<close>


subsection \<open>Encoding swap in CLEAN\<close>

(* for some strange reason, "result" is no longer a term. term "result" crashes. *)
(* list-lifting should be automatic in local_vars. *)


local_vars swap "unit"
   tmp :: "int" 
ML\<open> val Type(s,t) = StateMgt_core.get_state_type_global @{theory};
    StateMgt_core.get_state_field_tab_global @{theory};
    val binding = !SPY1;
    val sty = !SPY2;
    val rty = !SPY3; 
    Named_Target.theory_map;
    val lthy = (Named_Target.init "" @{theory}); 
    Syntax.read_typ_global  @{theory} "'a Quicksort_design.local_swap_state_scheme";
 \<close>

ML\<open>
            val name:bstring = Binding.name_of binding 
            val name_pushop =  mk_push_name binding
            val rty = \<^typ>\<open>unit\<close>
            val eq = push_eq binding name (Binding.name_of name_pushop) rty sty lthy
            val _ = (SPY := eq)
            val mty = StateMgt_core.MON_SE_T rty sty 
            val args = (SOME(name_pushop,SOME mty,NoSyn),(Binding.empty_atts,eq),[],[]);
cmd args false lthy
\<close>

find_theorems (150) name:"swap"

definition push_local_state_swap :: "(unit,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
  where   "push_local_state_swap \<sigma> = 
                    Some((),\<sigma>\<lparr>local_swap_state.tmp :=  undefined # local_swap_state.tmp \<sigma> \<rparr>)"

definition pop_local_state_swap :: "(unit,'a local_swap_state_scheme) MON\<^sub>S\<^sub>E"
  where   "pop_local_state_swap \<sigma> = 
                    Some(hd(local_swap_state.result_value \<sigma>), 
                                \<comment> \<open> recall : returns op value \<close>
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
local_vars  local_partition_state "nat"
    pivot  :: "int"
    i      :: "nat"
    j      :: "nat"

(* this implies the definitions : *)
definition push_local_partition_state :: "(unit, 'a local_partition_state_scheme) MON\<^sub>S\<^sub>E"
  where   "push_local_partition_state \<sigma> = Some((),
                        \<sigma>\<lparr>local_partition_state.pivot := undefined # local_partition_state.pivot \<sigma>, 
                          local_partition_state.i     := undefined # local_partition_state.i \<sigma>, 
                          local_partition_state.j     := undefined # local_partition_state.j \<sigma>, 
                          local_partition_state.result_value   
                                           := undefined # local_partition_state.result_value \<sigma> \<rparr>)"

definition pop_local_partition_state :: "(nat,'a local_partition_state_scheme) MON\<^sub>S\<^sub>E" 
  where   "pop_local_partition_state \<sigma> = Some(hd(local_partition_state.result_value \<sigma>),
                       \<sigma>\<lparr>local_partition_state.pivot := tl(local_partition_state.pivot \<sigma>), 
                         local_partition_state.i     := tl(local_partition_state.i \<sigma>), 
                         local_partition_state.j     := tl(local_partition_state.j \<sigma>), 
                         local_partition_state.result_value := 
                                                        tl(local_partition_state.result_value \<sigma>) \<rparr>)"


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
                assign_local result_value_update (\<lambda>\<sigma>. (hd o i) \<sigma>)  
                \<comment> \<open> the meaning of the return stmt \<close>
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

record a = 
   b :: int

local_vars  local_quicksort_state "unit"
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


ML\<open>
 HOLogic.listT ;

 HOLogic.nil_const ;

 HOLogic.cons_const ;

\<close>

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


(* the meat *)
local open StateMgt_core

    fun get_result_value_conf name thy = 
            let val  S = filter_attr_of name thy
            in  hd(filter (fn ((a,b),c) => b = "result_value") S) 
                handle _ => error("internal error: get_result_value_conf") end; 



    fun mk_lookup_result_value_term name sty thy =
        let val ((prefix,name),local_var(Type("fun", [_,ty]))) = get_result_value_conf name thy;
            val long_name = Sign.intern_const  thy (prefix^"."^name)
            val term = Const(long_name, sty --> ty)
        in  mk_hdT (term $ Free("\<sigma>",sty)) end


    fun mk_push_name s p = Binding.name("push_local_"^s^"_state")
    fun mk_pop_name s p  = Binding.make("pop_local_"^s^"_state",p)

    fun  map_to_update sty is_pop thy ((struct_name, attr_name), local_var (Type("fun",[_,ty]))) term = 
           let val tlT = if is_pop then Const(\<^const_name>\<open>List.tl\<close>, ty --> ty)
                         else Const(\<^const_name>\<open>List.Cons\<close>, dest_listTy ty --> ty --> ty)
                              $ mk_undefined (dest_listTy ty)
               val update_name = Sign.intern_const  thy (struct_name^"."^attr_name^"_update")
           in (Const(update_name, (ty --> ty) --> sty --> sty) $ tlT) $ term end
       | map_to_update _ _ _ ((_, _),_) _ = error("internal error map_to_update")     
    
    in fun construct_update is_pop name sty thy = 
           let val long_name = "local_"^name^"_state"
               val attrS = StateMgt_core.filter_attr_of long_name thy
           in  fold (map_to_update sty is_pop thy) (attrS) (Free("\<sigma>",sty)) end

    fun push_eq name name_op rty sty lthy = 
             let val mty = MON_SE_T rty sty 
                 val thy = Proof_Context.theory_of lthy
                 val term = construct_update false name sty thy
             in  mk_meta_eq((Free(name_op, mty) $ Free("\<sigma>",sty)), 
                             mk_Some ( HOLogic.mk_prod (mk_undefined rty,term)))
                              
             end;
    
    fun pop_eq name name_op rty sty lthy = 
             let val mty = MON_SE_T rty sty 
                 val thy = Proof_Context.theory_of lthy
                 val res_access = mk_lookup_result_value_term ("local_"^name^"_state") sty thy
                 val term = construct_update true name sty thy                 
             in  mk_meta_eq((Free(name_op, mty) $ Free("\<sigma>",sty)), 
                             mk_Some ( HOLogic.mk_prod (res_access,term)))
                              
             end;
    
    
    val cmd = (fn (((decl, spec), prems), params) =>
                            #2 oo Specification.definition' decl params prems spec)
    

    fun mk_push_def name p  sty lthy = 
        let val nameb =  mk_push_name name p
            val nameb_str = Binding.name_of nameb
            val rty = \<^typ>\<open>unit\<close>
            val eq = push_eq name nameb_str rty sty lthy
            val mty = StateMgt_core.MON_SE_T rty sty 
            val args = (((SOME(nameb,SOME mty,NoSyn),(Binding.empty_atts,eq)),[]),[])
        in cmd args true lthy
        end;
    
    
    fun mk_pop_def name p rty sty lthy = 
        let val mty = StateMgt_core.MON_SE_T rty sty 
            val nameb =  mk_pop_name name p
            val nameb_str = Binding.name_of nameb
            val _ = writeln nameb_str
            val eq = pop_eq name nameb_str rty sty lthy
            val args = (((SOME(nameb,SOME mty,NoSyn),(Binding.empty_atts,eq)),[]),[])
        in cmd args true lthy
        end;

end


\<close>

 

ML\<open>
construct_update true  "quicksort" @{typ "'a local_quicksort_state_scheme"} @{theory};
construct_update false "quicksort" @{typ "'a local_quicksort_state_scheme"} @{theory};
@{term "List.Cons"}

\<close>

setup\<open>Named_Target.theory_map (mk_push_def "quicksort" @{here} @{typ "'a local_quicksort_state_scheme"})\<close>
setup\<open>Named_Target.theory_map (mk_pop_def "quicksort" @{here} @{typ "unit"} @{typ "'b local_quicksort_state_scheme"})\<close>
<<<<<<< HEAD
=======

>>>>>>> 9d4f1fd7b73196e351b8d51c73b8b4a251213348


thm pop_local_quicksort_state_def
thm push_local_quicksort_state_def

(* this implies the definitions : *)
definition push_local_quicksort_state' :: "(unit, 'a local_quicksort_state_scheme) MON\<^sub>S\<^sub>E"
  where   "push_local_quicksort_state' \<sigma> = 
                 Some((), \<sigma>\<lparr>local_quicksort_state.p := undefined # local_quicksort_state.p \<sigma>,
                            local_quicksort_state.result_value := undefined # local_quicksort_state.result_value \<sigma> \<rparr>)"

<<<<<<< HEAD
thm pop_local_quicksort_state_def
thm push_local_quicksort_state_def

(* this implies the definitions : *)
definition push_local_quicksort_state' :: "(unit, 'a local_quicksort_state_scheme) MON\<^sub>S\<^sub>E"
  where   "push_local_quicksort_state' \<sigma> = 
                 Some((), \<sigma>\<lparr>local_quicksort_state.p := undefined # local_quicksort_state.p \<sigma>,
                            local_quicksort_state.result_value := undefined # local_quicksort_state.result_value \<sigma> \<rparr>)"

=======
>>>>>>> 9d4f1fd7b73196e351b8d51c73b8b4a251213348



definition pop_local_quicksort_state' :: "(unit,'a local_quicksort_state_scheme) MON\<^sub>S\<^sub>E"
  where   "pop_local_quicksort_state' \<sigma> = Some(hd(local_quicksort_state.result_value \<sigma>),
                       \<sigma>\<lparr>local_quicksort_state.p   := tl(local_quicksort_state.p \<sigma>), 
                         local_quicksort_state.result_value := 
                                                      tl(local_quicksort_state.result_value \<sigma>) \<rparr>)"

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