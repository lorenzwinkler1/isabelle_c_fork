theory "Coder_Test_Coercions"
  imports
          "../src/compiler/Clean_Annotation"
          "../src/CleanTranslationHook"
begin

declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]


ML\<open>
@{term "a \<ge> 2"}
\<close>


ML\<open>
\<close>

C\<open>
int b;
int a[];

void test(int c){
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

C\<open>
void test2(){
  b = test1();
}\<close>


