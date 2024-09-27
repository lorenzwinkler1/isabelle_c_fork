theory "Coder_Test_StmtTUnits"
  imports "Isabelle_C.C_Main"
          "HOL.Real"
          "../src/CleanCoder"
begin


section\<open>C11 Translation Units \<close>
(* Note: see C_Term.env0 in C_Command.thy
   C environment is updated with each added C context *)
declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]

C\<open>int global1;\<close>

ML\<open>
local open C_AbsEnv in
val (identifiers, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty 
val () = List.app printIdentifier identifiers
end
\<close>

C\<open>int global2[];
  int m();\<close>

ML\<open>
local open C_AbsEnv in
val (identifiers, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier identifiers
end
\<close>

C\<open>int global3[][], global4 = fibo(global1), global5;
unsigned int global6, global7;\<close>

ML\<open>
local open C_AbsEnv in
val (identifiers, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier identifiers
end
\<close>

C\<open>
int a[], b;
int c = foo(a), d;
\<close>

ML\<open>
local open C_AbsEnv in
val (identifiers, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier identifiers
end\<close>

C\<open>
void test() {
  int a[], b;
  int c = foo(a), d;
  bar(d);
}
\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier nEnv
end\<close>

(* Grab the /local/ state by declaring a dummy local variable in `identity`.
   What this effectively does is trick Isabelle in ignoring the context that holds the
   function definition of `identity` *)
local_vars_test  (identity "int")
    z  :: "int"
ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}

val Type(ty_name, _) = sigma_i
\<close>

C\<open>int identity(int a) {
  return a;
}\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier nEnv
val ast_stmt = extractStatement nEnv "identity"
end
\<close>




ML\<open>
open C11_Stmt_2_Clean;

(* This may or may not be useful later:
val state_field = StateMgt_core.get_state_field_tab_global @{theory};
val lookup=Symtab.lookup state_field p *)

val [S] =  (C11_Ast_Lib.fold_cStatement 
              regroup 
              (convertStmt false sigma_i nEnv @{theory} "" (K (NONE, NONE)))
              ast_stmt []);
\<close>

ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

ML\<open>
(* We create an abstraction over the term: iterate backwards using the param list *)
fun mk_final_term identifiers id t =
  let fun lookupParams identList funName =
        List.filter (fn C_AbsEnv.Identifier(_, _, _, cat) => case cat of C_AbsEnv.Parameter(s) => s = funName | _ => false) identList
      val rev_param_list = rev (map (fn C_AbsEnv.Identifier(name, _, ty,_) => (name, ty)) (lookupParams identifiers id)) 
  in mk_pat_tupleabs rev_param_list t end

val final_term = mk_final_term nEnv "identity" S
\<close>

(* We type-certify the term in Isabelle/HOL *)
ML\<open>
Sign.certify_term @{theory} final_term
\<close>

(* We pretty-print the term in lambda notation *)
ML\<open>
writeln (Syntax.string_of_term_global @{theory} final_term);
\<close>

local_vars_test  (add "int")
    z  :: "int"
ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}\<close>

(* Example of non recursive function *)
C\<open>
float add(int a, int b) {
  return a + b;
}
\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier nEnv
val add_ast = @{C11_CTranslUnit}
val ast_stmt = extractStatement nEnv "add"
end
\<close>


ML\<open>

val [S] =  (C11_Ast_Lib.fold_cStatement 
              regroup 
              (convertStmt false sigma_i nEnv @{theory} "" (K (NONE,NONE)) )
              ast_stmt []);
\<close>

ML\<open>
val final_term = mk_final_term nEnv "add" S
\<close>

ML\<open>
Sign.certify_term @{theory} final_term
\<close>

ML\<open>
writeln (Syntax.string_of_term_global @{theory} final_term);
\<close>

(* Example of function with parameter variable assignment *)

local_vars_test  (increment "int")
    a  :: "int" (* for some reason, required for assigns *)
ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}\<close>

C\<open>
int increment(int a) {
  a = a + 1;
  return a + 1;
}\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier nEnv
val ast_stmt = extractStatement nEnv "increment";
end

\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
              regroup 
              (convertStmt false sigma_i nEnv @{theory} "" (K(NONE,NONE))) 
              ast_stmt [])
           handle ERROR _ => [S];
\<close>



(* Example of function with global variable assignment *)

global_vars (foo)
    a  :: "int"
ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}\<close>

C\<open>
int a;
void foo() {
  a = 1;
}
\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier nEnv
val ast_stmt = extractStatement nEnv "foo";
end

\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
              regroup 
              (convertStmt true sigma_i nEnv @{theory} "" (K(NONE,NONE)))
              ast_stmt []);
\<close>

ML\<open>
val final_term = mk_final_term identifiers "foo" S
\<close>

ML\<open>
Sign.certify_term @{theory} (Syntax.check_term @{context} final_term)
\<close>

ML\<open>
writeln (Syntax.string_of_term_global @{theory} final_term);
\<close>

(* Example of function call *)

global_vars (state)
    A :: "int list"

function_spec swap (i::nat,j::nat) returns unit
pre          "\<open>i < length A \<and> j < length A\<close>"    
post         "\<open>\<lambda>res. length A = length(old A) \<and> res = ()\<close>" 
local_vars   tmp :: int 
defines      " \<open> tmp := A ! i\<close>  ;-
               \<open> A := list_update A i (A ! j)\<close> ;- 
               \<open> A := list_update A j tmp\<close> "

local_vars_test  (paws "unit")
    z  :: "int"
ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}\<close>
ML\<open>val init_ident = [C_AbsEnv.Identifier("swap", Position.none, @{typ "unit"}, C_AbsEnv.FunctionCategory(C_AbsEnv.Final, NONE))]\<close>             


(* TODO: should also be defined analogously to unsigned int, unsigned long, ... *)
C\<open>
void paws(unsigned a, unsigned b) {
  swap(a, b);
}\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} init_ident [] Symtab.empty 
val () = List.app printIdentifier nEnv
val ast_stmt = extractStatement nEnv "paws";
end
\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
              regroup 
              (convertStmt true sigma_i nEnv @{theory} "" (K(NONE,NONE)))
              ast_stmt []);
\<close>

ML\<open>
val final_term = mk_final_term identifiers "paws" S
\<close>

ML\<open>
Sign.certify_term @{theory} final_term
\<close>

ML\<open>
writeln (Syntax.string_of_term_global @{theory} final_term);
\<close>

(* Example of local variable assignment *)

local_vars_test (bar "int")
    c  :: "int"
ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}\<close>

(* Function that automagically parses the state_field_tab and returns a list of declared local variables *)
ML\<open>
fun mk_namespace thy =
  let val Type(str_local_state_scheme, _) = StateMgt_core.get_state_type_global thy;
      val str_local_state = String.substring (str_local_state_scheme, 0, 
                             String.size str_local_state_scheme - (String.size "_scheme"))
  in Path.explode str_local_state end
(* rubbish *)
fun parse_state_field_tab thy =
  let val ns = mk_namespace thy |> Path.implode
      val tab = StateMgt.get_state_field_tab_global thy
      val l = Symtab.dest tab
      fun pred (s, _) = (String.isSubstring ns s) 
                         andalso not ((ns ^ "." ^ StateMgt.result_name) = s)
      val filtered_l = filter pred l
      val init_idents = map (fn (s, StateMgt.local_var(ty)) => 
                                let val id = String.extract (s, (String.size ns) + 1, NONE)
                                    val pos = Position.none
                                    val t = (fn (Type (@{type_name "list"}, [T])) => T) 
                                                (lastype_of ty)
                                    val cat = C_AbsEnv.Local("_")
                                in C_AbsEnv.Identifier(id, pos, t, cat) end
                              | (s, StateMgt.global_var(ty)) => 
                                let val id = String.extract (s, (String.size ns) + 1, NONE)
                                    val pos = Position.none
                                    val t = lastype_of ty
                                    val cat = C_AbsEnv.Global
                                in C_AbsEnv.Identifier(id, pos, t, cat) end) 
                             filtered_l
  in init_idents end
\<close>


ML\<open>val init_idents = parse_state_field_tab @{theory}\<close>

C\<open>
int bar(int a, int b) {
  int d;
  c = 0;
  return 0;
  
}
\<close>


ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} init_idents [Identifier("c",@{here},HOLogic.intT, Global)] Symtab.empty
val () = List.app printIdentifier nEnv
val ast_stmt = extractStatement nEnv "bar";

val env = @{C\<^sub>e\<^sub>n\<^sub>v}
end
\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
              regroup 
              (convertStmt true sigma_i nEnv @{theory} "" (K(NONE,NONE)))
              ast_stmt []);
\<close>

ML\<open>
val final_term = mk_final_term identifiers "bar" S
\<close>

ML\<open>
Sign.certify_term @{theory} (Syntax.check_term @{context} final_term)
\<close>

ML\<open>
writeln (Syntax.string_of_term_global @{theory} final_term);
\<close>

(* Example of recursive function with maximum 1 function call *)

local_vars_test  (factorial "int")
    z  :: "int"
ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}\<close>

C\<open>
int factorial(int n) {
  if (n <= 1) return 1;
  return n * factorial(n - 1);
}
\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier nEnv
val ast_stmt = extractStatement nEnv "factorial";
end
\<close>

(* recursive function call in expression not yet supported in Clean even if side-effect free.*)

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
              regroup 
              (convertStmt false sigma_i nEnv @{theory} "" (K(NONE,NONE)))
              ast_stmt [])
           handle ERROR _ => (writeln "correct crash: recursion not supported"; 
                              [@{term "undefined"}])
\<close>

(* should be represented by : *)


C\<open>
int factorial(int n) { int temp;
  if (n <= 1) return 1;
  temp = factorial(n - 1);
  return n * temp;
}
\<close>


ML\<open>
val final_term = mk_final_term identifiers "factorial" S
\<close>

ML\<open>
Sign.certify_term @{theory} final_term
\<close>

ML\<open>
writeln (Syntax.string_of_term_global @{theory} final_term);
\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier nEnv
end\<close>

(* Example of mutually recursive functions *)

local_vars_test  (is_even "int")
    z  :: "int"
ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}\<close>

C\<open>
int is_even(unsigned  n) {
    if (n == 0)
        return 0;
    else
        return is_odd(n - 1);
}

int is_odd(unsigned  n) {
    if (n == 0)
        return -1;
    else
        return is_even(n - 1);
}
\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier nEnv
val ast_stmt = extractStatement nEnv "is_even";
end
\<close>

(* Not yet supported: Mutual recursion. *)
ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
              regroup 
              (convertStmt false sigma_i nEnv @{theory} "" (K(NONE,NONE)))
              ast_stmt []) 
            handle ERROR _ => (writeln "correct crash: recursion not supported"; 
                              [@{term "undefined"}]);
\<close>

local_vars_test  (sqrt "int")
    i  :: "int"
    tm  :: "int"
    sum  :: "int"
ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}\<close>
ML\<open>val init_idents = parse_state_field_tab @{theory}\<close>

C\<open>
int sqrt(int a) {
  i = 0;
  tm = 1;
  sum = 1;

  while (sum <= a) {      
    i = i + 1;
    tm = tm + 2;
    sum = sum + tm;
  }

  return i;
}
\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} 
                                  init_idents [] Symtab.empty
val () = List.app printIdentifier nEnv
val ast_stmt = extractStatement nEnv "sqrt";
end
\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
              regroup 
              (convertStmt false sigma_i nEnv @{theory} "" (K(NONE,NONE)))
              ast_stmt []);
\<close>

ML\<open>
val final_term = mk_final_term identifiers "sqrt" S
\<close>

ML\<open>
Sign.certify_term @{theory} (Syntax.check_term @{context} final_term)
\<close>

ML\<open>
writeln (Syntax.string_of_term_global @{theory} final_term);
\<close>

local_vars_test  (allzeros "int")
    k  :: "int"
ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}\<close>
ML\<open>val nEnv_0 = parse_state_field_tab @{theory}\<close>


C\<open>
int allzeros(int t[], int n) {
  int k = 0;

  while(k < n) {
    if (t[k] == 0) return 0;
    k = k + 1;
  }
  return 1;
}

\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} 
                                      nEnv_0 [] Symtab.empty
val () = List.app printIdentifier nEnv
val ast_stmt = extractStatement nEnv "allzeros";
end
\<close>

(* PROBLEM *)
ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
              regroup 
              (convertStmt false sigma_i nEnv @{theory} "" (K(NONE,NONE)))
              ast_stmt []);
\<close>

C\<open>
int binarysearch(int t[], int n, int v) {
  int l = 0;
  int u = n-1;

  while (l <= u) {
    int m = (l + u) / 2;
    if (t[m] < v) {
      l = m + 1;
    } else if (t[m] > v) {
      u = m - 1;
    }
    else return m; 
  }
  return -1;
}
\<close>

ML\<open>
local open C_AbsEnv in
val (identifiers, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier identifiers
end\<close>


C\<open>
int linearsearch(int x, int t[], int n) {
  int i = 0;

  while (i < n) {
    if (t[i] < x) {
      i++;
    } else {
      return (t[i] == x);
    }
  }

  return 0;
}
\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier nEnv
end\<close>

C\<open>
#include <stdio.h>
 
int main()
{
  int array[100], n, c, d, position, swap;
 
  printf("Enter number of elements\n");
  scanf("%d", &n);
 
  printf("Enter %d integers\n", n);
 
  for (c = 0; c < n; c++) scanf("%d", &array[c]);
 
  for (c = 0; c < (n - 1); c++)
  {
    position = c;
   
    for (d = c + 1; d < n; d++)
    {
      if (array[position] > array[d])
        position = d;
    }
    if (position != c)
    {
      swap = array[c];
      array[c] = array[position];
      array[position] = swap;
    }
  }

printf("Sorted list in ascending order:\n");
 
  for (c = 0; c < n; c++)
    printf("%d\n", array[c]);
 
  return 0;
}
\<close>

ML\<open>
local open C_AbsEnv in
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier nEnv
end\<close>

global_vars (test)  (*intern label *)
            a     :: "int"
            b     :: "int"

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "statement"]]
C\<open>{ return a + b; }\<close>
ML\<open>val ast_stmt = @{C11_CStat}   \<comment> \<open>C11 ast\<close>
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>        \<comment> \<open>C11 c-env\<close>

ML\<open>val nEnv_0 = parse_state_field_tab @{theory};\<close>

ML\<open>val menv = Symtab.dest (#idents (#var_table env_stmt));
   \<close>

ML\<open>add_ast\<close>

ML\<open>
local open HOLogic C_Ast in

fun get_return_type (CTranslUnit0 ([CFDefExt0 (CFunDef0 (ret_ty,params,a,body,c))],_)) = 
    (case ret_ty of
      [] => SOME unitT
    | sign => C11_TypeSpec_2_CleanTyp.conv_cDeclarationSpecifier_typ (SOME sign))
    
val ty = get_return_type add_ast

end
\<close>
ML\<open>
local open C_Env C_AbsEnv C11_TypeSpec_2_CleanTyp HOLogic in 
fun convertEnv (name,(pos_list,serial,{ global = true , params = [] , ret = Parsed Z }))
               = SOME(Identifier(name, hd pos_list, 
                      the(conv_cDeclarationSpecifier_typ(SOME Z)), Global))
   |convertEnv (name,(pos_list,serial,{ global = true , params = P as (C_Ast.CArrDeclr0 G::R) , ret = Parsed Z }))
               = SOME(Identifier(name, hd pos_list, 
                      C11_TypeSpec_2_CleanTyp.conv_cDerivedDeclarator_typS P
                       (the(conv_cDeclarationSpecifier_typ(SOME Z))), Global))
   |convertEnv (name,(pos_list,serial,{ global = true , params = P as (C_Ast.CFunDeclr0 G::R) , ret =  Z }))
               = let val curried_w_dummyreturn = C11_TypeSpec_2_CleanTyp.conv_CDerivedDecl_typ P dummyT
                     val (tyS,ty) = strip_type curried_w_dummyreturn
                     val uncurried_w_dummyreturn = HOLogic.mk_tupleT tyS --> ty
                 in   SOME(Identifier(name, hd pos_list, uncurried_w_dummyreturn, 
                                      FunctionCategory(Final, NONE))) end
   |convertEnv (name,(pos_list,serial,{ global = true , params = [] , ret = _ }))
               = (writeln("Can't type global variable :"^name ); NONE)
   |convertEnv (name,_)
               = (writeln("Can't type item :"^name ); NONE)

end
\<close>

ML\<open>nth menv 5\<close>
ML\<open>val (name,(pos_list,serial,{ scope = C_Env.Global , functionArgs=_,
                                params = P as (C_Ast.CFunDeclr0 G::R) , ret =  Z })) = nth menv 5;
   val curried_w_dummyreturn = C11_TypeSpec_2_CleanTyp.conv_CDerivedDecl_typ P dummyT
   val (tyS,ty) = strip_type curried_w_dummyreturn
   val uncurried_w_dummyreturn = HOLogic.mk_tupleT tyS --> ty
\<close>
ML\<open>nth menv 5;
   \<close>

(* dies ist ein Versuch, ein return in einem globalen Kontext auszufuehren. 
   Dieser Test macht keinen Sinn.

ML\<open> 
val [body] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt false (StateMgt_core.get_state_type @{context}) nEnv_0 @{theory} "" (K(NONE,NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close>


ML\<open>
open C_AbsEnv;
val Identifier(name, pos, ret_typ, _) = hd identifiers;
val add_bind = Binding.make (name, pos);
val sty = StateMgt_core.get_state_type @{context};
val param_list = map (fn Identifier(name, pos, typ, _) => ( Binding.make(name, pos), typ))
                     (tl identifiers);
val mon_se_ty = StateMgt_core.MON_SE_T ret_typ sty;
val ctxt = @{context};
val args_ty = HOLogic.mk_tupleT (map snd param_list);
val local_thy = Function_Specification_Parser.define_body_core add_bind ret_typ args_ty
                        param_list body;
Function_Specification_Parser.define_body_core add_bind args_ty sty param_list body ctxt
(*Function_Specification_Parser.define_body_main { recursive = false } add_bind ret_typ sty param_list NONE 0 ctxt*)
\<close>
*)