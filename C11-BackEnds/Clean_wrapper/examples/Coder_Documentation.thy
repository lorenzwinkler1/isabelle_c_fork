(*In this file the current limitations of the translation from C to Clean are shown.*)
theory "Coder_Documentation"
  imports
          "../src/compiler/Clean_Annotation"
          "../src/CleanTranslationHook"
begin


section\<open>Architecture remarks\<close>
text\<open>
The function \<open>handle_declarations::nodeInfo cTranslationUnit ->Context.generic -> Context.generic\<close>
can be called with the AST of a translation unit to handle all the definitions. Within that, for every
function the \<open>convertStmt\<close> (CleanCoder) is called to create a translation of the function body.

The \<open>setup C_Module.C_Term.map_expression\<close> command handles the C-Term-Antiquotation, which is used for the annotations.
The parsing of the annotation is delayed, for the reason that they need a contet within which sigma (and vars)
are already defined. For that reason, they are stored in \<open>Data_Clean_Annotations\<close> as functions with the
signature \<open>Context.generic \<rightarrow> term\<close>. This functions are then called when the new context is available.
Additionally the position and function names are saved, which are needed for assigning pre- and postconditions to
the functions and assigning invariants and measures to a loop (via positions).

Importantly, the parsing of the expressions still needs the "old" env because it contains informations
about local vars and parameters, therefore this is saved in the beginning of the \<open>map_context_annotation_declaration\<close> function.
The environment is then passed by writing it to the \<open>Data_Surrounding_Env\<close> GenericData-store.

To prevent Isabelle from coercing types of returned terms \<open>Syntax.parse_term\<close> is used instead of \<open>Syntax.read_term\<close>.
Furthermore as parameters are represented as free variables, all constants that would be "selected" through
a parameter name need to be hidden (\<open>remove_params_from_proof\<close>).

Environment:
The scope of a parameter now is visible in the environment's var table. It is either "Global", "Local" or "Parameter".
Furthermore each identifier has a field \<open>functionArgs\<close> which is an optional list of function parameters.
When an identifier has \<open>functionArgs = NONE\<close>, then it is a variable. \<open>functionArgs=SOME []\<close> corresponds to a parameterless function.

Nice to know:
- The environment of the last completely parsed C-context can be retrieved using \<open>C_Module.Data_In_Env\<close>.
- Intermediate envs, containing parameters and local vars can be retrieved using \<open>C_Env.Data_Lang.get'\<close>.
See C5.thy in the examples of C11-Frontend.
\<close>

section\<open>Limitations\<close>
text\<open>
- Only two types are currently mapped to isabelle types, 
  namely int -> int and unsigned -> nat.

- Function calls can only occur as statements or on the right hand side of an assignment.
  For example \<open>a = b + foo();\<close> is not allowed. This must be rewritten as \<open>tmp = foo(); a=b+tmp;\<close>

- Recursive functions must have "void" as return value. This is caused by an issue within
  Clean and is about to be fixed. The current translation should work for this case then.

- Scoping: refrain from defining variables more than once. A read/write from a local variable
  always affects the most recent definition. Scoping using curly braces does not work as in C!
    example:  
    \<open>int foo(){
        int x = 3;
        {
          int x = 5;
        }
        return x;  // wrongly returns 5
      }\<close>
  Also defining global variables twice within one translation unit will result in only one definition, 
  thus the second definition does not "reset" the value of the variable

- Method overloading: Do not use function names multiple times, as this will break the whole
  translation process in several ways.
\<close>

section\<open>Some examples\<close>
text\<open>See \<open>Coder_Test_T_Units\<close> for more examples\<close>

C\<open>
int sum_of_array(int arr[], int length){
  int i;
  int sum;
  i = 0;
  sum = 0;
  while(i < length){
    /*@ inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>i\<close> \<le> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>length\<close>\<close> */
    /*@ measure\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>nat \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>length-i\<close>\<close> */
    sum = sum + arr[i];
    i = i+1;
  }
  return sum;
}
\<close>
(*look at the annotated while loop - it has the inv as first and the measure as snd argument*)
find_theorems sum_of_array_core

text\<open>The following program would not work in C - Clean admits it however, but produces warnings\<close>
C\<open>
int A[5][4];
int swap_rows(unsigned idx1, unsigned idx2){
  int tmp[];
  tmp = A[idx1];
  A[idx1] = A[idx2];
  A[idx2] = tmp;
}
\<close>
find_theorems swap_rows_core

text\<open>A fully annotated multiply\<close>
C\<open>
int multiply(int a, int b){
  /*@ pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a\<close> \<ge> 0\<close> */
  /*@ post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<lambda>ret::int. ret = \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a*b\<close>\<close> */
  int sum;
  int counter;
  sum = 0;
  counter = 0;

  while(counter < a){
    /*@ inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n  \<open>\<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>counter*b\<close> = \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>sum\<close> \<and> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>counter\<close> \<le> \<^C>\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<open>a\<close>\<close> */
    sum = sum + b;
    counter = counter + 1;
  }
  return sum;
}
\<close>
find_theorems multiply
find_theorems multiply_pre
find_theorems multiply_post

text\<open>A recursive function calculating the \<close>
C\<open>
int factorial_result;
void factorial(int n){
  if(n > 1){
    factorial(n-1);
    factorial_result = multiply(factorial_result, n);
  }else{
    factorial_result = 1;
  }
}\<close>
find_theorems factorial_core
