theory "Coder_Test_ExprStmt"
  imports "../src/CleanCoder"  (* Coder_Test_Env_AEnv *)
begin


section \<open>Tests on Expressions\<close>

subsection\<open>Ground Expressions\<close>

(*integer :*)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
C\<open>12\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v};
   val mt_A_env = []
   val sigma_i = StateMgt.get_state_type_global @{theory}

\<close>


ML\<open>
open C11_Expr_2_Clean HOLogic;

val S = (C11_Ast_Lib.fold_cExpression (K I) 
                                      (convertExpr false sigma_i  mt_A_env  @{theory} "" (K NONE))
                                      ast_expr []);
val S = conv_Cexpr_lifted_term  sigma_i mt_A_env @{theory} "" (K NONE) ast_expr

\<close>

\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open> Sign.certify_term @{theory} S \<close>

(*2*****************************************************************************************************)

(*string :*)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
C\<open>"char string"\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (K I) 
                                      (convertExpr false sigma_i  mt_A_env @{theory} "" (K NONE)) 
                                      ast_expr []);
val S = conv_Cexpr_lifted_term  sigma_i mt_A_env @{theory} "" (K NONE) ast_expr

\<close>

\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open> Sign.certify_term @{theory} S \<close>

(*3*****************************************************************************************************)

(*char :*)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
C\<open>'c'\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>
val S = (C11_Ast_Lib.fold_cExpression (K I) 
                                      (convertExpr false sigma_i  mt_A_env @{theory} "" (K NONE)) 
                                      ast_expr []);
val S = conv_Cexpr_lifted_term  sigma_i mt_A_env @{theory} "" (K NONE) ast_expr
\<close>
\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open> Sign.certify_term @{theory} S \<close>

(*4*****************************************************************************************************)

(*float :*)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
C\<open>2.997924587\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (K I) 
                                      (convertExpr false sigma_i  mt_A_env @{theory} "" (K NONE)) 
                                      ast_expr []);
val S = conv_Cexpr_lifted_term  sigma_i mt_A_env @{theory} "" (K NONE) ast_expr

\<close>

ML\<open>@{term "2.997924587"}\<close>

\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open> Sign.certify_term @{theory} S \<close>

(*5*****************************************************************************************************)


C\<open>1 + 1\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (K I) 
                                      (convertExpr false sigma_i  mt_A_env @{theory} "" (K NONE)) 
                                      ast_expr []);
val S = conv_Cexpr_lifted_term  sigma_i mt_A_env @{theory} "" (K NONE) ast_expr

\<close>

\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open> Sign.certify_term @{theory} S \<close>

(*6*****************************************************************************************************)

subsection\<open>Expressions using Global and Local Variables\<close>

(* construct environment with global variable on the Isabelle_C side:*)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]
declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
C\<open>int a; int b[5];\<close>

ML\<open>
val X = Unsynchronized.ref (0)
;
X := !X + 1;
!X;
X := !X + 1;
!X;

@{make_string} (!X)
\<close>
(* to mimick the effect on the Clean side: *)
global_vars (test)  (*intern label *)
            a     :: "int"
            b     :: "int list"
            c     :: "int list list"
            n1    :: "nat"
            n2    :: "nat"
            var1  :: "int"
            var2  :: "int"

    find_theorems a
                                                                 
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
C\<open>1 * a\<close>

ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}

local open C_AbsEnv HOLogic in
(* we construct suitable environments by hand for testing: *)
   val A_env0 = [ Identifier("a", @{here}, intT, Global),
                  Identifier("b", @{here}, listT intT, Global),
                  Identifier("c", @{here}, listT (listT intT), Global),
                  Identifier("n1", @{here}, natT, Global),
                  Identifier("n2", @{here}, natT, Global),
                  Identifier("localArr", @{here}, listT intT, Local "to some function"),
                  Identifier("localArrArr", @{here}, listT (listT intT), Local "to some function")];
   val A_env2 = [ Identifier("a", @{here}, intT, Parameter "of some function")];

   val sigma_i = StateMgt.get_state_type_global @{theory}
end
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (K I) 
                                      (convertExpr false sigma_i  A_env0 @{theory} "" (K NONE)) 
                                      ast_expr []);
val S = conv_Cexpr_lifted_term  sigma_i A_env0 @{theory} "" (K NONE) ast_expr

val S'' = (C11_Ast_Lib.fold_cExpression (K I) 
                                      (convertExpr false sigma_i  A_env2 @{theory} "" (K NONE)) 
                                      ast_expr []);
val S'' = conv_Cexpr_lifted_term  sigma_i A_env2 @{theory} "" (K NONE) ast_expr

\<close>

\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open> Sign.certify_term @{theory} (Syntax.check_term @{context} S) \<close>

(* This local variable space also creates the update function for the return_result. *)
local_vars_test  (test_return "int")
    x  :: "int"
    y  :: "int list"
    localArr :: "int list"
    localArrArr :: "int list list"
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]
declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
C\<open>int x; int y[3];\<close>

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
term\<open>result_value\<close>
find_theorems result_value

C\<open>1 * x\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}

local open C_AbsEnv HOLogic in
   val A_env1 = [ Identifier("a", @{here}, intT, Global ),
                  Identifier("b", @{here}, listT intT, Global ),
                  Identifier("x", @{here}, intT, Local "to some function"),
                  Identifier("y", @{here}, listT intT, Local "to some function")];
   val sigma_i = StateMgt.get_state_type_global @{theory}
end
\<close>

ML\<open>
val S' = (C11_Ast_Lib.fold_cExpression (K I) 
                                      (convertExpr false sigma_i  A_env1 @{theory} "" (K NONE)) 
                                      ast_expr []);
val S' = conv_Cexpr_lifted_term  sigma_i A_env1 @{theory} "" (K NONE) ast_expr
\<close>



C\<open>1 * b[5-a] + y[a]\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>


ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (K I) 
                                      (convertExpr false sigma_i  A_env1 @{theory} "" (K NONE)) 
                                      ast_expr []);
val S = conv_Cexpr_lifted_term  sigma_i A_env1 @{theory} "" (K NONE) ast_expr
\<close>
\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open>Sign.certify_term @{theory} (Syntax.check_term @{context} S)\<close>


(*7*****************************************************************************************************)

C\<open>a == 1\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (K I) 
                                      (convertExpr true sigma_i  A_env0 @{theory} "" (K NONE)) 
                                      ast_expr []);
val S = conv_Cexpr_lifted_term  sigma_i A_env0 @{theory} "" (K NONE) ast_expr

\<close>

\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open>Sign.certify_term @{theory} (Syntax.check_term @{context} S)\<close>

section \<open>statements\<close>

text \<open>Then, start the study of the statements (while, for, if then else, return, skip, ...)\<close>

(*1*****************************************************************************************************)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "statement"]]
C\<open>{a = a+a;
   while(1 && 1){a = a * a; a = a + 1; }
  }
 \<close>
ML\<open>open C11_Stmt_2_Clean;


   val ast_stmt = @{C11_CStat}   \<comment> \<open>C11 ast\<close>
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>        \<comment> \<open>C11 c-env\<close>

ML\<open>val C_Ast.CCompound0(a, b, c) = ast_stmt;\<close> \<comment> \<open>grabbing into an AST\<close>

\<comment> \<open>a C11 AST to Clean compilation, written as the internal Isabelle representation in Term.term.\<close>
\<comment> \<open>verbous tracing on.\<close>
ML\<open> 
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt true sigma_i A_env0 @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close> 

\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open>Sign.certify_term @{theory} (Syntax.check_term @{context} S)\<close>


text\<open>Write to array\<close>

text\<open>Global\<close>
C\<open>c[1][a] = a;\<close>
ML\<open>
val ast_stmt = @{C11_CStat}
val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt false sigma_i A_env0 @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close>

ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

ML\<open> Sign.certify_term @{theory} S \<close>

text\<open>local\<close>
C\<open>localArrArr[1][a] = a;\<close>
ML\<open>
val ast_stmt = @{C11_CStat}
val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt false sigma_i A_env0 @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close>

ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

ML\<open> Sign.certify_term @{theory} S \<close>


text\<open>Read global array\<close>
C\<open>a = c[1][a];\<close>
ML\<open>
val ast_stmt = @{C11_CStat}
val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt false sigma_i A_env0 @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close>

ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

ML\<open> Sign.certify_term @{theory} S \<close>

text\<open>Read local array\<close>
C\<open>a = localArrArr[1][a];\<close>
ML\<open>
val ast_stmt = @{C11_CStat}
val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt false sigma_i A_env0 @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close>

ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

ML\<open> Sign.certify_term @{theory} S \<close>


text\<open>mode complex array stuff\<close>
C\<open>localArr[a] = localArrArr[1][b[c[1][2]]];\<close>
ML\<open>
val ast_stmt = @{C11_CStat}
val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt false sigma_i A_env0 @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close>

ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

ML\<open> Sign.certify_term @{theory} S \<close>



(*2*****************************************************************************************************)

(*if the body is empty, then we put a skip :*)

C\<open>
while(1==1){a = a+1;}
\<close>
ML\<open>val ast_stmt = @{C11_CStat}
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>


ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt false sigma_i A_env0 @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close>
\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open>Sign.certify_term @{theory} (Syntax.check_term @{context} S)\<close>

(*3*****************************************************************************************************)

C\<open>
for(a = 0; a < 2; a = a + 1){
   a = a + 5;
}
\<close>
 ML\<open>val ast_stmt = @{C11_CStat}\<close>

(* crash due to typing problem *)
ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt true sigma_i A_env0 @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close>
\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open>Sign.certify_term @{theory} (Syntax.check_term @{context} S)\<close>

(*4*****************************************************************************************************)

C\<open>
if(a == 1){
  a = 1 + 2;
}
else{
  a = 3*3;
}
\<close>
ML\<open>val ast_stmt = @{C11_CStat}
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt false sigma_i A_env0 @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close>
\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open>Sign.certify_term @{theory} (Syntax.check_term @{context} S)\<close>


(*5*****************************************************************************************************)

(*work in progress for skip, break and return : *)


C\<open>
for(a = 0; a < 10; a = a + 1){
  while(a < 10){
    break;
  }
  return a;
}
\<close>
ML\<open>val ast_stmt = @{C11_CStat} \<close>
ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt false sigma_i A_env0 @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close>
ML\<open>fun read_N_coerce thy name ty = 
       (* a very dirty hack ... but reconstructs the true \<open>const_name\<close> 
          along the subtype hierarchy, but coerces it to the current sigma*)
       let val s = drop_dark_matter(Syntax.string_of_typ_global thy ty)
           val str = name ^ " :: " ^ s 
       in  Syntax.read_term_global thy str end \<close>
ML\<open> read_N_coerce @{theory} "a" (sigma_i --> intT)\<close>
\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

\<comment> \<open>type-check of the latter\<close>
ML\<open>Sign.certify_term @{theory} (Syntax.check_term @{context} S)\<close>
(* a very serious problem : the inheritance on state spaces is not appropriately mirrored. *)


(*following : unfinished work.*)

section \<open>Expressions in Declarations\<close>

text \<open>The next step is to study the declarations. There are globals or locals declarations, 
and functions or variables declarations.\<close>

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "external_declaration"]]
C\<open> int b,a;\<close>
ML\<open>val ast_ext_decl = @{C11_CExtDecl}
   val env_ext_decl =  @{C\<^sub>e\<^sub>n\<^sub>v}

\<close>

(* initializers not yet supported; so this gives a local error *)
ML \<open>
val S =  (C11_Ast_Lib.fold_cExternalDeclaration regroup
                  (convertExpr false sigma_i A_env1 @{theory} "" (K (NONE, NONE))) (* DOES THIS MAKE SENSE ??? *)
                  ast_ext_decl 
                  [])
\<close>

(*4*****************************************************************************************************)

declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]

C\<open>int  yyy ;\<close>

ML\<open>val ast_unit = @{C11_CTranslUnit}
   val env_unit = @{C\<^sub>e\<^sub>n\<^sub>v}
  \<close>

C\<open>int  zzz = 13 ;\<close>

ML\<open>val ast_unit' = @{C11_CTranslUnit}
   val env_unit' = @{C\<^sub>e\<^sub>n\<^sub>v}
  \<close>


ML\<open>
local open C_Ast in
fun conv_C11Positiona_Position (Position0(k : int, 
                                SS_base(ST (st: string)), 
                                m: int, n: int))
   = (warning"Not Correct Position:" ; Position.none)             
  | conv_C11Positiona_Position NoPosition0  = Position.none
  | conv_C11Positiona_Position BuiltinPosition0 =  Position.none
  | conv_C11Positiona_Position InternalPosition0 = Position.none

fun conv_C11NodeInfo (OnlyPos0 (p1: positiona, (p2 : positiona, lab: int))) =
       (conv_C11Positiona_Position p1, conv_C11Positiona_Position p2, "")
  | conv_C11NodeInfo (NodeInfo0 (p1 : C_Ast.positiona, (p2: positiona, lab: int), Name0 x)) =
       (conv_C11Positiona_Position p1, conv_C11Positiona_Position p2, "")

end
\<close>

section \<open>Calls\<close>

ML\<open>val sigma_i = StateMgt.get_state_type_global @{theory}\<close>

declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]

C\<open>
int var1;
int var2;
int a;
int b[];
void foo(int xy) {
  int z = xy+2;
  return z+1;
}

void three_args_function(int x, int y, int z){
  x = foo(x);
}

int fun_with_ret_value(int x){
  return x;
}
\<close>

ML\<open>
val cenv = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>
local open C_AbsEnv in
(* val translUnit = @{C11_CTranslUnit} *)
val (nEnv, callTable) = parseTranslUnitIdentifiers @{C11_CTranslUnit} [] [] Symtab.empty
val () = List.app printIdentifier nEnv
val ast_stmt = extractStatement nEnv "foo"
end\<close>

C\<open>
void test1(int abc, int def) {
  return abc;
}

void test2(){
  return 12;
}
\<close>

ML\<open>
Theory.setup
  (C_Inner_Syntax.command_no_range
       (C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup
         \<open>fn ((v1, (v2, pos1, pos2)) :: _) =>
              (fn v3 => fn v4 =>
                tap (fn v5 =>
                      Position.reports_text [((Position.range (pos1, pos2)
                                               |> Position.range_position, Markup.intensify), "")]))
           | _ => fn _ => fn _ => I\<close>)
       ("store_env", \<^here>, \<^here>))
\<close>

ML \<open>


Theory.setup
  (C_Inner_Syntax.command_no_range
       (C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup
         \<open>fn ((v1, (v2, pos1, pos2)) :: _) =>
              (fn v3 => fn v4 =>
                tap (fn v5 =>
                      (SPY_ENV := SOME (C_Module.env v5);Position.reports_text [((Position.range (pos1, pos2)
                                               |> Position.range_position, Markup.intensify), "")])))
           | _ => fn _ => fn _ => I\<close>)
       ("store_env1", \<^here>, \<^here>))
\<close>

ML\<open>
 

\<close>


C\<open>
void test5(){
}\<close>

ML\<open>
val SPY_ENV =  Unsynchronized.ref(NONE:C_Env.env_lang option);\<close>
C\<open>


void test3(char ab[][], int* *c, int *d){
  int aasdfwqer;
  
  return 12;   /*@ \<approx>setup \<open>fn a => fn b => fn env =>
               (writeln(@{make_string} env);(SPY_ENV := SOME env);I) \<close> */;

}
\<close>

ML\<open>
val a = let fun last (a::b::R) = last (b::R)
               | last [a] = a

in last (#scopes (the (!SPY_ENV))) end
\<close>

ML\<open>

val tmp1 = (map (fn (a,(_,_,b)) => (a,#scope b,#functionArgs b)) (Symtab.dest (
 #idents(#var_table(the (!SPY_ENV))))
))
\<close>

ML\<open>
val cenv = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

term\<open>skip\<^sub>S\<^sub>E\<close>
ML\<open>StateMgt.MON_SE_T HOLogic.unitT sigma_i\<close>
consts foo :: "int \<Rightarrow> (unit,'a local_test_return_state_scheme)MON\<^sub>S\<^sub>E "

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "statement"]]

C\<open>
 foo(5);
\<close>

ML\<open>
local open C_AbsEnv in
val foo_stmt = @{C11_CStat};
end
\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt false sigma_i nEnv @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                foo_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close>

ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

ML\<open>Sign.certify_term @{theory} (Syntax.check_term @{context} S)\<close>

subsection\<open>Call with no return type\<close>
(*Methods call only with sideeffects*)
consts three_args_function :: "(int * int * int) \<Rightarrow> (unit,'a local_test_return_state_scheme)MON\<^sub>S\<^sub>E "
C\<open>three_args_function(3+3,4,8);\<close>
ML\<open>
val ast_stmt = @{C11_CStat}
val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt false sigma_i nEnv @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 


\<close>
term assign_to_a

ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

ML\<open>Sign.certify_term @{theory} (Syntax.check_term @{context} S)\<close>

subsection\<open>Call with return type\<close>
consts fun_with_ret_value :: "(int) \<Rightarrow> (int,'a local_test_return_state_scheme)MON\<^sub>S\<^sub>E "

C\<open>localArr[0]=fun_with_ret_value(3+3);\<close>
ML\<open>
val ast_stmt = @{C11_CStat}
val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>
(* build the new env with local vars for test purposes *)
local open C_AbsEnv HOLogic in
val localVarEnv = [
                  Identifier("x", @{here}, intT, Local "to some function"),
                  Identifier("localArr", @{here}, listT intT, Local "to some function"),
                  Identifier("localArrArr", @{here}, listT (listT intT), Local "to some function")
]
end
val nEnv1 = nEnv@localVarEnv
\<close>

ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt false sigma_i nEnv1 @{theory} "" (K (NONE, NONE))) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 


\<close>
term assign_to_a

ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

ML\<open>Sign.certify_term @{theory} (Syntax.check_term @{context} S)\<close>

section \<open>Experiments with Local Scopes\<close>

ML\<open> local open C_Ast 
in
val CTranslUnit0
    ([CDeclExt0
       ( CDecl0
           ([CTypeSpec0 ( CIntType0 (NodeInfo0 A))],
            [((Some(CDeclr0(Some(Ident0(SS_base(ST "yyy"),_,NodeInfo0 AA)),[],None,[],NodeInfo0 AAA)),
               None), None)], NodeInfo0 AAAA)
       )
    ],  
    NodeInfo0 XAAA):
   C_Grammar_Rule_Lib.CTranslUnit = ast_unit

fun conv_cid [((Some(CDeclr0(Some(Ident0(SS_base(ST x),lab,nid1)),[],None,[],NodeInfo0 AAA)),
               None), None)] ctxt = (x,lab,nid1)
  | conv_cid _ _  = error "conv_cid (0) format not defined. [Clean restriction]"

(* FIRST DRAFT - INCOMPLETE *)
fun conv_transl_unit ( CTranslUnit0 (CDeclExt0 (CDecl0(tys,cid, nid1)) :: R,nid2)) thy = 
         let val cid_name = #1(conv_cid cid thy)
             val typ = C11_TypeSpec_2_CleanTyp.conv_cDeclarationSpecifier_typ (SOME tys)
             val pos = @{here} (* should be derived from nid1 *)
             val S = [(Binding.make(cid_name, pos), the typ, Mixfix.NoSyn)]
        
         in thy |> StateMgt.new_state_record' true (NONE,S)
                |> conv_transl_unit (CTranslUnit0 (R, nid2)) 
         end
    | conv_transl_unit (CTranslUnit0 ([], _)) thy  = thy 
    | conv_transl_unit _ _  = error "transl_unit (0) format not defined. [Clean restriction]"

end
\<close>

ML    \<open>(Symtab.dest)(StateMgt_core.get_state_field_tab_global @{theory})\<close>
setup \<open>conv_transl_unit ast_unit\<close>
ML    \<open>(Symtab.dest)(StateMgt_core.get_state_field_tab_global @{theory})\<close>
(* A Cadaver ... *)
setup \<open>conv_transl_unit ast_unit'\<close>
ML    \<open>(Symtab.dest)(StateMgt_core.get_state_field_tab_global @{theory});\<close>

end