theory "Coder_Test_TUnits"
  imports
          "../src/compiler/Clean_Annotation"
          "../src/CleanTranslation"
begin

declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]

ML\<open>
val a = (Abs ("\<sigma>", StateMgt.get_state_type ( @{context}),
      Const ("Orderings.ord_class.greater_eq", @{typ "_"}) $ Const ("Groups.one_class.one",  @{typ "int"}) $
        Const ("Groups.one_class.one", @{typ "int"})))

val a' = absfree ("a",@{typ "int"}) (absfree ("b", @{typ "int"}) (Syntax.check_term @{context} a))

val b = HOLogic.mk_case_prod a'
\<close>


C\<open>
int multiply1(int a, int b){
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>1 \<ge> 1\<close> */
  return a;
}\<close>


term\<open>nat\<close>
C\<open>
int u;
int arrr[];
\<close>
C\<open>
int globvar;
unsigned nat1;
int u;
int fun_with_pre_test(int u){
  int localvar;

  localvar = u;
  /* pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>u\<close> > 1\<close> */
  /* post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<lambda>ret::int.\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>u\<close> > 1 \<and> ret > 0\<close> */

  while(localvar>0){
  /* inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>u\<close> \<ge> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>localvar\<close> \<close> */
  /*@ measure\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>nat1\<close>\<close> */
    localvar = localvar -1;
  }

  return 1;
}\<close>
find_theorems fun_with_pre_test_core


section\<open>Demonstration\<close>

subsection\<open>Global definitions\<close>
C\<open>
int global_integer;
unsigned global_nat;
\<close>
(*variables are declared accordingly*)
find_theorems global_integer
find_theorems global_nat
term\<open>global_integer\<close>
term\<open>global_nat\<close>




subsection\<open>Function definitions\<close>
C\<open>int threefunc(){
  return 1+2;
}

int sum5(int p1, int p2){
  return p1+p2;
}

void addToGlobalInteger(int value){
  global_integer = global_integer+value;
}
\<close>

find_theorems threefunc_core
term\<open>threefunc\<close>
find_theorems sum_core
term\<open>sum\<close>




subsection\<open>And function calls\<close>
C\<open>
void addPlusThree(int val){
  int three; /*Init expression currently unsupported*/
  three = threefunc();
  addToGlobalInteger(three+val);
}
\<close>


text\<open>we compare this to an equivalent definition\<close>
function_spec addPlusThree1(val :: int) returns unit
pre          "\<open>True\<close>" 
post         "\<open>\<lambda>res::unit. True \<close>"
local_vars   three :: int
defines "p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C threefunc \<open>()\<close> ; assign_local three_update (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p);-
         call\<^sub>C addToGlobalInteger \<open>(three + val)\<close>"

find_theorems addPlusThree_core
find_theorems addPlusThree1_core
term\<open>addPlusThree\<close>
term\<open>addPlusThree1\<close>




subsection \<open>Recursive functions\<close>
find_theorems global_integer
rec_function_spec recursive_add1(n::int) returns unit
pre          "\<open>True\<close>" 
post         "\<open>\<lambda>res::unit. True \<close>"
local_vars   localvar1 :: int
defines "if\<^sub>C \<open>n > 0\<close>  
         then (\<open> global_integer :=  global_integer + 1\<close>);-
               call\<^sub>C recursive_add1 \<open>(n-1)\<close>
         else skip\<^sub>S\<^sub>E 
         fi"

C\<open>
void recursive_add(int n){
  if(n > 0){
    global_integer = global_integer + 1;
    recursive_add(n-1);
  }
}\<close>

find_theorems recursive_add_core
find_theorems recursive_add1_core
term recursive_add
term recursive_add1




subsection\<open>(multidimensional) arrays are also supported\<close>
C\<open>
int globalArray[][];
int something(){
  int localvar;
  localvar = globalArray[0][3];
}
\<close>




subsection\<open>A fully annotated program\<close>
text\<open>disclaimer: C_expr antiquotation does not yet work\<close>



C\<open>
int multiply(int a, int b){
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>1 \<ge> 1\<close> */
  /*@ post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<lambda>ret::int. ret = \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a*b\<close>\<close> */
  int s;
  int counter;
  int counter_b;
  counter = 0;
  s = 0;

  while(counter < a){
    /*@ inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>counter*b\<close> = \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>s\<close> \<and> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>counter\<close> \<le> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a\<close>\<close> */
    counter_b = 0;
    while(counter_b < b){
      /*@ inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>counter_b\<close> \<le> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>b\<close>\<close> */      
      counter_b = counter_b +1;
    }
    
    s = s + counter_b;
    counter = counter + 1;
  }
  return s;
}
\<close>







section\<open>Some other tests\<close>

C\<open>
int intarr[][][];
int x;
\<close>
term x
find_theorems x
C\<open>
int sum1(int param1,int param2){
  x = threefunc();
  intarr[2][3][1] = x + param1 + param2;
  return 1;
}

int sum3(int param1,int param2){
  int x; // test to override
  x = sum1(param1, param2);
  return x;
}\<close>
find_theorems x
find_theorems sum1_core
C\<open>
int test_scope(){
  x = 1;
  return x;
}
\<close>

find_theorems sum3_core
term\<open>intarr\<close>


C\<open>
int a;
int testfunction(int v1, int v2){
  global_integer = sum1(v1,v2);
  return global_integer;
}
\<close>

C\<open>
int b;
\<close>

text\<open>Now the declaration of local variables\<close>
C\<open>
int funwithlocalvars(){
  int localvar1;
  localvar1 = threefunc();
  return localvar1;
}
\<close>
term localvar1
find_theorems funwithlocalvars_core
term funwithlocalvars_core

ML\<open>
val ast = @{C11_CTranslUnit}
\<close>
ML\<open>
val env = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>

function_spec testfunction1(param1 :: int, param2::int) returns int
pre          "\<open>True\<close>" 
post         "\<open>\<lambda>res::int. True \<close>"
local_vars   localvar1 :: int
defines "p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C sum1 \<open>(2::int, 3::int)\<close> ; assign_global global_integer_update (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p);-
         return\<^bsub>local_testfunction1_state.result_value_update\<^esub> \<open>global_integer\<close>"

find_theorems testfunction1_core
term\<open>testfunction1_core\<close>



(*
Recursions with return values are currently unsupported in CLEAN, but are about to be fixed by someone else

rec_function_spec recursive_function2(n::int) returns int
pre          "\<open>True\<close>" 
post         "\<open>\<lambda>res::int. True \<close>"
local_vars   localvar1 :: int
defines "p\<^sub>t\<^sub>m\<^sub>p \<leftarrow> call\<^sub>C recursive_function2 \<open>2::int\<close> ; assign_local localvar1_update (\<lambda>\<sigma>. p\<^sub>t\<^sub>m\<^sub>p);-
return\<^bsub>local_recursive_function2_state.result_value_update\<^esub> \<open>1::int\<close>"
*)


text\<open>Now the pre and post conditions\<close>



C\<open>
int xx;
int fun_with_pre(int u){
  int local1;
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>xx\<close> > 0\<close> */
  /*@ post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<lambda>ret::int.3 > \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>u\<close>\<close> */
  return local1;
}
int fun_with_pre2(int u){
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>u\<close>  > 0\<close> */

  return 1;
}
\<close>

ML\<open>

val annotation_data = Clean_Annotation.Data_Clean_Annotations.get (Context.Theory @{theory})
\<close>                                          


text\<open>Invariants are more tricky, as there can be several within one function\<close>

text\<open>Lets start with a simple example with two loops, 
    which computes a*b, given a and b are positive!

    The following program is fully annotated with pre-, and postcondition, aswell as 2 invariants\<close>
C\<open>int a;\<close>
C\<open>
int multiply2(int a, int b){
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a\<close> > 0\<close> */
  /*@ post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<lambda>ret::int. ret = \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a*b\<close>\<close> */
  int sum;
  int counter;
  int counter_b;

  while(counter < a){
    /* here we have a loop without an invariant */
    counter = counter + 1;
  }
  counter = 0;
  sum = 0;

  while(counter < a){
    /*@ inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>counter\<close> \<le> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a\<close>\<close> */
    counter = counter + 1;
  }

  while(counter > 0){
    /* inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>(a-counter)*b\<close> = \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>sum\<close> \<and> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>counter\<close> \<ge> 0\<close> */
    counter_b = 0;
    while(counter_b < b){
      /* inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>C\<open>counter_b\<close> \<le> b\<close>*/      
      counter_b = counter_b +1;
    }
    
    sum = sum + counter_b;
    counter = counter -1;

  }
  return sum;
}
\<close>

C\<open>
int globarr[];\<close>
C\<open>
void somefunction123(){
int localArray[];

}\<close>

find_theorems multiply_core

ML\<open>
val annotation_data = Clean_Annotation.Data_Clean_Annotations.get (Context.Theory @{theory})
\<close>   

