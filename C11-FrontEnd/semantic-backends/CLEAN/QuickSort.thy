theory QuickSort
  imports Clean
begin

term "A!n"

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

global_vars 'a state  
    A :: "int list "
    tmp :: int

find_theorems name:state

(*
local_vars for partition :
*)
record  local_state_swap = "unit QuickSort.state" +
    tmp  :: "int list"

definition push_local_state_swap :: "(unit,local_state_swap) MON\<^sub>S\<^sub>E"
  where "push_local_state_swap \<sigma> = Some((),
                                   \<sigma>\<lparr>local_state_swap.tmp:= undefined # local_state_swap.tmp \<sigma> \<rparr>)"

definition pop_local_state_swap :: "(unit,local_state_swap) MON\<^sub>S\<^sub>E"
  where "pop_local_state_swap \<sigma> = Some((), \<comment> \<open> recall : returns unit \<close>
                                   \<sigma>\<lparr>local_state_swap.tmp:= tl( local_state_swap.tmp \<sigma>) \<rparr>)"


definition swap :: "int => int =>  (unit,local_state_swap) MON\<^sub>S\<^sub>E"
   where  "swap i j \<equiv> (\<open>tmp := A!i\<close>       ;-
                       \<open>A := A[i:=(A!j)]\<close> ;-   
                       \<open>A := A[j:=tmp]\<close>)"



record  local_state_partition = "unit QuickSort.state" + (* local_state_swap ? *)
    pivot  :: "int list"
    i      :: "int list" 
    result :: "int list"


(* this implies the definitions : *)
definition push_local_state :: "(unit,local_state_partition) MON\<^sub>S\<^sub>E"
  where "push_local_state \<sigma> = Some((),
                                   \<sigma>\<lparr>local_state_partition.pivot:= undefined # local_state_partition.pivot \<sigma>, 
                                     local_state_partition.i:=undefined # local_state_partition.i \<sigma>, 
                                     local_state_partition.result := undefined # local_state_partition.result \<sigma> \<rparr>)"

definition pop_local_state :: "(int,local_state_partition) MON\<^sub>S\<^sub>E" 
  where "pop_local_state \<sigma> = Some(hd(local_state_partition.result \<sigma>),
                                  \<sigma>\<lparr>local_state_partition.pivot:= tl( local_state_partition.pivot \<sigma>), 
                                    local_state_partition.i:=tl( local_state_partition.i \<sigma>), 
                                    local_state_partition.result :=tl( local_state_partition.result \<sigma>) \<rparr>)"

term "B[k:=(B!j)]"


end