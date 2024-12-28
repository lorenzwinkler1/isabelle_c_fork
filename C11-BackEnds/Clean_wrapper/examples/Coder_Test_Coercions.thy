theory "Coder_Test_Coercions"
  imports
          "../src/compiler/Clean_Annotation"
          "../src/CleanTranslationHook"
begin

declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]


ML\<open>
@{term "a \<noteq>2"}
\<close>


section\<open>int to nat coercions\<close>

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

section\<open>boolean coercions\<close>

text\<open>Direction integer --> boolean\<close>
C\<open>
_Bool global_bool;
\<close>



C\<open>
void test_bool1(int c, int d,int e){
  global_bool =  d ^ e;
}
\<close>

C\<open>
void test_bool2(int c, int d,int e){
  global_bool = d & e; // bitwise and
}
\<close>

C\<open>
void test_bool3(int c, int d,int e){
  global_bool = d && e; // logical and
}
\<close>
