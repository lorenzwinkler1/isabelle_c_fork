theory "Coder_Example_1"
  imports "../src/CleanCoder"
begin

section \<open>converters\<close>

ML\<open>
fun map_option f (SOME X) = SOME(f X)
   |map_option f NONE     = NONE   

fun lookup_Cid_info (C_env:C_Module.Data_In_Env.T) id = Symtab.lookup(#idents(#var_table C_env)) id


fun is_global_Cid Cenv Cid   = map_option (fn (_,_,X) => #global X) (lookup_Cid_info Cenv Cid);
fun is_fun_Cid Cenv Cid      = map_option (fn (_,_,X) => [] <> #params X) (lookup_Cid_info Cenv Cid);
fun get_CDeclSpecS_Cid Cenv id= map_option (fn (_,_,X) => #ret X) (lookup_Cid_info Cenv id);

fun conv_ParseStatus_CDeclSpecS (SOME(C_Env.Parsed S)) = SOME S
   |conv_ParseStatus_CDeclSpecS _ = NONE

\<close>
section \<open>expressions\<close>

text \<open>
First, we translate the expressions;
we can have binary operators, unary operators, or constants.
The attributs can be constantes or variables. 
In order to simulate the use of variables, we construct a "fake" record local_state
\<close>

global_vars test  (*intern label *)
            a     :: "int"

ML\<open>val Const(longid_a,Type("fun",[sigma_i, _])) = @{term "a"} \<close>

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]
declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]

C\<open> int a[10+12][34][] = 1;
   int f(short int x [], long double y);
\<close>

ML\<open>val env_expr : C_Module.Data_In_Env.T =  @{C\<^sub>e\<^sub>n\<^sub>v};\<close>

ML\<open>
   val SOME(pos_list,ser,S)    = lookup_Cid_info env_expr "a";
   val SOME(pos_list',ser',S') = lookup_Cid_info env_expr "f";
\<close>

ML\<open>
local open C_Ast C_Env in

(*
fold (fn C_Ast.CArrDeclr0 _ => (fn tyf => HOLogic.listT o tyf)
        |C_Ast.CFunDeclr0 _ => (fn tyf => curry (op -->) tyf)
        | _ => error "non-convertible C-type")
*)
val _ = C_Ast.CTypeSpec0 : 'a C_Ast.cTypeSpecifier ->  'a C_Ast.cDeclarationSpecifier;
val _ = C_Ast.CFunDeclr0;
val _ = C_Ast.Right
val [CArrDeclr0 (HH,CArrSize0 (_,CBinary0 X),_),
     CArrDeclr0 (_,CArrSize0  (_,CConst0 Y), _), 
     CArrDeclr0 (_,CNoArrSize0 Z,_)] = #params S
val [CFunDeclr0 (Right([CDecl0 (A, A',_),CDecl0 (B,B',_)],s), _, _)] = #params S'

end
\<close>

ML\<open>
fold_rev (fn C_Ast.CDecl0 (A, _ ,_) => fn S => (SOME A) :: S) ;
A;
B;
\<close>
ML\<open>
local open C_Ast C_Env in

(* mk_CFunDeclr0; *)
(*val CSpec = (get_CDeclSpecS_Cid env_expr "a"); *)
val CTypeSpec = conv_ParseStatus_CDeclSpecS (get_CDeclSpecS_Cid env_expr "a");
val CTypeSpec' = conv_ParseStatus_CDeclSpecS (get_CDeclSpecS_Cid env_expr "f");
(*
  and 'a cTypeSpecifier = CVoidType0 of 'a | CCharType0 of 'a | CShortType0 of 'a 
                       | CIntType0 of 'a | CLongType0 of 'a | CFloatType0 of 'a 
                       | CDoubleType0 of 'a | CSignedType0 of 'a | CUnsigType0 of 'a | CBoolType0 of 'a |
*)
fun conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CUnsigType0 _)])) = SOME(HOLogic.intT)
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CIntType0 _)]))   = SOME(HOLogic.intT)
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CLongType0 _),
                                          CTypeSpec0 (CIntType0 _)]))   = SOME(HOLogic.intT)
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CShortType0 _),
                                          CTypeSpec0 (CIntType0 _)]))   = SOME(HOLogic.intT)
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CUnsigType0 _), 
                                          CTypeSpec0 (CIntType0 _)]))   = SOME(HOLogic.natT)   
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CUnsigType0 _),
                                          CTypeSpec0 (CLongType0 _), 
                                          CTypeSpec0 (CIntType0 _)]))   = SOME(HOLogic.natT)   
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CShortType0 _)])) = SOME(HOLogic.intT)
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CLongType0 _)]))  = SOME(HOLogic.intT)
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CFloatType0 _)])) = SOME(HOLogic.realT)
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CDoubleType0 _)]))= SOME(HOLogic.realT)
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CLongType0 _),
                                          CTypeSpec0 (CDoubleType0 _)]))= SOME(HOLogic.realT)
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CVoidType0 _)]))  = SOME(HOLogic.unitT)
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CCharType0 _)]))  = SOME(HOLogic.charT)
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CUnsigType0 _),
                                          CTypeSpec0 (CCharType0 _)]))  = SOME(HOLogic.charT)
   |conv_cDeclarationSpecifier_typ (SOME([CTypeSpec0 (CSignedType0 _),
                                          CTypeSpec0 (CCharType0 _)]))  = SOME(HOLogic.charT)
   |conv_cDeclarationSpecifier_typ _ = error("Type format not defined. [Clean restriction]")

fun conv_cDerivedDeclarator_cArraySize_term (CArrDeclr0 (_,CArrSize0 (_,C_expr),_)) C_env thy = 
            SOME(hd((C11_Ast_Lib.fold_cExpression 
                               (convertExpr_raw false sigma_i C_env thy) C_expr [])))
   |conv_cDerivedDeclarator_cArraySize_term (CArrDeclr0 (_,CNoArrSize0 Z,_)) _ _ =NONE
   |conv_cDerivedDeclarator_cArraySize_term (_)  _ _ = 
            error("Derived declarator format not defined. [Clean restriction]")

fun conv_cDerivedDeclarator_cSizeExpr_term (CArrDeclr0 (_,CArrSize0 (_,C_expr),_)) C_env thy = 
            SOME(hd((C11_Ast_Lib.fold_cExpression 
                                 (convertExpr_raw false sigma_i C_env thy) C_expr [])))
   |conv_cDerivedDeclarator_cSizeExpr_term (CArrDeclr0 (_,CNoArrSize0 Z,_)) _ _ = NONE
   |conv_cDerivedDeclarator_cSizeExpr_term (_)  _ _ =  
            error("DeclarationSpec format not defined. [Clean restriction]")


fun conv_cDerivedDeclarator_typS (CArrDeclr0 (_,CArrSize0 _ ,_)) C_env thy = HOLogic.listT 
                    (*no enumerations ? nat ? *)
   |conv_cDerivedDeclarator_typS (CFunDeclr0 (Right(S,_), _, _)) C_env thy = I

end;
conv_cDeclarationSpecifier_typ CTypeSpec;
conv_cDeclarationSpecifier_typ CTypeSpec';
C_Ast.CFunSpec0;
fun conv_CDecls_typS X = fold_rev (fn C_Ast.CDecl0 (A, _ ,_) => fn S => the (conv_cDeclarationSpecifier_typ (SOME A)) --> S) X ;
val [C_Ast.CFunDeclr0 (C_Ast.Right(SS,_), _, _)] = #params S';
conv_CDecls_typS SS HOLogic.boolT; 
\<close>

ML\<open>
A'
\<close>

(*1*****************************************************************************************************)

(*integer :*)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
C\<open>12\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v};
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr []);
val S = conv_Cexpr_term env_expr sigma_i @{theory} ast_expr

\<close>

(*2*****************************************************************************************************)

(*string :*)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
C\<open>"char string"\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr []);
val S = conv_Cexpr_term env_expr sigma_i @{theory} ast_expr

\<close>

(*3*****************************************************************************************************)

(*char :*)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
C\<open>'c'\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr []);
val S = conv_Cexpr_term env_expr sigma_i @{theory} ast_expr

\<close>

(*4*****************************************************************************************************)

(*float :*)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
C\<open>2.997924587\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr []);
val S' = conv_Cexpr_term env_expr sigma_i @{theory} ast_expr

\<close>

(*5*****************************************************************************************************)


C\<open>1 + 1\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr []);
val S' = conv_Cexpr_term env_expr sigma_i @{theory} ast_expr

\<close>

(*6*****************************************************************************************************)

(* construct environment with global variqble *)
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]
C\<open> int a = 1;\<close>

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
C\<open>1 * a\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr [])
val S' = conv_Cexpr_term env_expr sigma_i @{theory} ast_expr

\<close>

(*7*****************************************************************************************************)


C\<open>a == 1\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr []);

\<close>

section \<open>statements\<close>

text \<open>Then, start the study of the statements (while, for, if then else, return, skip, ...)\<close>

(*1*****************************************************************************************************)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "statement"]]
C\<open>
while(1){
  a = a + 1;
  }
\<close>
ML\<open>val ast_stmt = @{C11_CStat}
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>


ML\<open>
val S =  (C11_Ast_Lib.fold_cStatement (convertStmt_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_stmt []); 
\<close>

(*2*****************************************************************************************************)

(*if the body is empty, then we put a skip :*)

C\<open>
while(1){
  }
\<close>
ML\<open>val ast_stmt = @{C11_CStat}
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>


ML\<open>
val S =  (C11_Ast_Lib.fold_cStatement (convertExpr false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_stmt []); 
\<close>

(*3*****************************************************************************************************)

C\<open>
for(a = 0; a < 2; a = a + 1){
  
  }
\<close>
ML\<open>val ast_stmt = @{C11_CStat}
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>


ML\<open>
val S =  (C11_Ast_Lib.fold_cStatement (convertExpr false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_stmt []); 
\<close>

(*4*****************************************************************************************************)

C\<open>
if(a = 1){
  a = 1 + 2;
}
else{
  a = 3*3;
}
\<close>
ML\<open>val ast_stmt = @{C11_CStat}
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>

(*5*****************************************************************************************************)

(*work in progress for skip, break and return : *)

C\<open>
for(a = 0; a < 10; a = a + 1){
  while(a < 10){
    break;
  }
  continue;
  return a;
}
\<close>
ML\<open>val ast_stmt = @{C11_CStat}
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>


ML\<open>
val S =  (C11_Ast_Lib.fold_cStatement (convertExpr false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_stmt []); 
\<close>

(*following : unfinished work.*)

section \<open>declarations\<close>

text \<open>The next step is to study the declarations. There are globals or locals declarations, 
and functions or variables declarations.\<close>

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "external_declaration"]]
C\<open> int b = 1;\<close>
ML\<open>val ast_ext_decl = @{C11_CExtDecl}
   val env_ext_decl =  @{C\<^sub>e\<^sub>n\<^sub>v}

\<close>

ML \<open>
val S =  (C11_Ast_Lib.fold_cExternalDeclaration (convertExpr false boolT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_ext_decl []);
\<close>

(*4*****************************************************************************************************)

declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]
C\<open>int a = 0;
\<close>
ML\<open>val ast_unit = @{C11_CTranslUnit}
   val env_unit = @{C\<^sub>e\<^sub>n\<^sub>v}

  \<close>

ML \<open>
val S =  (C11_Ast_Lib.fold_cTranslationUnit (convertExpr false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_unit []);
\<close>








end