theory "Coder_Test_Coercions"
  imports
          "../src/compiler/Clean_Annotation"
          "../src/CleanTranslationHook"
begin

ML\<open>
@{term "a \<ge> 2"}
\<close>


ML\<open>
\<close>

C\<open>
int b;
int a[];

void test(){
  b =  a[b];
}
\<close>

find_theorems test_core

C\<open>
int test1(){
  b = 1;
  return  a[b];
}
\<close>

find_theorems test1_core

