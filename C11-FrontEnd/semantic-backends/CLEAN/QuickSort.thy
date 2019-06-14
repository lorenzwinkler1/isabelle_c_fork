theory QuickSort
  imports Clean
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


funct swap (i::int, j :: int) returns unit 
     pre  "True"
     post "True"
     local_vars tmp :: int
     \<open>\<open>tmp := A!i\<close> ;-
      \<open>A[i] := A[j]\<close> ;-   (* A := A[i:=A[j]] *)
      \<open>A[j] := tmp\<close>
     \<close>

funct partition (li::int, hi::int) returns int
     pre  "True"
     post "True"
     local_vars pivot :: int  i :: int  j :: int
     \<open>\<open>pivot := A!hi\<close> ;-
      \<open>i := lo\<close> ;-
      for\<^sub>C\<^sub>L\<^sub>E\<^sub>A\<^sub>N (j=lo,  hi - 1 ,j++)  
         \<open>if\<^sub>C\<^sub>L\<^sub>E\<^sub>A\<^sub>N \<open>A!j < pivot\<close> then swap(i,j);- \<open>i := i + 1\<close>
                               else Skip;-
          swap(i,j);-
          return(i)
         \<close>
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


ML\<open>
val Type(s,t) = StateMgt_core.get_state_type_global @{theory};
\<close>

         ML\<open>Record.last_extT @{typ state}\<close>
         ML\<open>Record.get_extension @{theory} "state"\<close>


find_theorems name:state

(* for some strange reason, "result" is no longer a term. term "result" crashes. *)
local_vars local_swap_state  
   tmp :: "int list" 
   res :: "unit list"

ML\<open>@{typ local_swap_state}\<close>
definition push_local_state_swap :: "(unit,local_swap_state) MON\<^sub>S\<^sub>E"
  where   "push_local_state_swap \<sigma> = Some((),
                                          \<sigma>\<lparr>local_swap_state.tmp := 
                                               undefined # local_swap_state.tmp \<sigma> \<rparr>)"

definition pop_local_state_swap :: "(unit,local_swap_state) MON\<^sub>S\<^sub>E"
  where   "pop_local_state_swap \<sigma> = Some(hd(local_swap_state.res \<sigma>), \<comment> \<open> recall : returns unit \<close>
                                        \<sigma>\<lparr>local_swap_state.tmp:= tl( local_swap_state.tmp \<sigma>) \<rparr>)"
term "Clean.syntax_assign"
term "B[x:=(B!j)]"
term assign
definition swap :: "int => int =>  (unit,local_swap_state) MON\<^sub>S\<^sub>E"
   where  "swap i j \<equiv> (\<open>tmp := A!i\<close>       ;-
                       \<open>A := (A[i:=(A!j)])\<close> ;-   
                       \<open>A := (A[j:=tmp])\<close>)"



local_vars  local_partition_state
    pivot  :: "int list"
    i      :: "int list" 
    res   :: "int list"


(* this implies the definitions : *)
definition push_local_partition_state :: "(unit,local_partition_state) MON\<^sub>S\<^sub>E"
  where "push_local_partition_state \<sigma> = Some((),
                                   \<sigma>\<lparr>local_partition_state.pivot:= undefined # local_partition_state.pivot \<sigma>, 
                                     local_partition_state.i:=undefined # local_partition_state.i \<sigma>, 
                                     local_partition_state.res := undefined # local_partition_state.res \<sigma> \<rparr>)"

definition pop_local_partition_state :: "(int,local_partition_state) MON\<^sub>S\<^sub>E" 
  where "pop_local_partition_state \<sigma> = Some(hd(local_partition_state.res \<sigma>),
                                  \<sigma>\<lparr>local_partition_state.pivot:= tl( local_partition_state.pivot \<sigma>), 
                                    local_partition_state.i:=tl( local_partition_state.i \<sigma>), 
                                    local_partition_state.res :=tl( local_partition_state.res \<sigma>) \<rparr>)"

term "B[k:=(B!j)]"


end