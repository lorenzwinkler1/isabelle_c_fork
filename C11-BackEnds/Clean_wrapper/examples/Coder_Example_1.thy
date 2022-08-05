theory "Coder_Example_1"
  imports "../src/CleanCoder"
begin


section \<open>Accessors to C-Env\<close>

ML\<open>
fun map_option f (SOME X) = SOME(f X)
   |map_option f NONE     = NONE   

fun lookup_Cid_info (C_env:C_Module.Data_In_Env.T) id = Symtab.lookup(#idents(#var_table C_env)) id

fun is_global_Cid Cenv Cid     = map_option (#global o #3) (lookup_Cid_info Cenv Cid);
fun is_fun_Cid Cenv Cid        = map_option ((fn [C_Ast.CFunDeclr0 _] => true | _ => false) 
                                               o (#params o #3)) 
                                            (lookup_Cid_info Cenv Cid);
fun get_CDeclSpecS_Cid Cenv id = map_option (#ret o #3) (lookup_Cid_info Cenv id);


\<close>
section\<open>Preliminary Spy\<close>

ML\<open>
val ENV = Unsynchronized.ref (@{C\<^sub>e\<^sub>n\<^sub>v})
fun print_env' s _ stack _ env thy =
  let
    val () = (ENV:=env; writeln ("ENV " ^ C_Env.string_of env))
  in thy end
\<close>
setup \<open>ML_Antiquotation.inline @{binding print_env'}
                               (Scan.peek (fn _ => Scan.option Args.text)
                                >> (fn name => ("print_env' "
                                                ^ (case name of NONE => "NONE"
                                                              | SOME s => "(SOME \"" ^ s ^ "\")")
                                                ^ " " ^ ML_Pretty.make_string_fn)))\<close>
(*
ML\<open>
C_Inner_Syntax.command;
C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup;
C_Inner_Syntax.command  (C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup);
\<close>
ML\<open>fn ((_, (_, pos1, pos2)) :: _) =>
              (fn _ => fn _ =>
                tap (fn ctxt:Context.generic =>
                      Position.reports_text [((Position.range (pos1, pos2)
                                               |> Position.range_position, Markup.intensify), "")]))
           | _ => fn _ => fn _ => I:Context.generic -> Context.generic\<close>
ML\<open>
C_Inner_Syntax.command_no_range
       (C_Inner_Toplevel.generic_theory oo C_Inner_Isar_Cmd.setup
         \<open>fn ((_, (_, pos1, pos2)) :: _) =>
              (fn _ => fn _ =>
                tap (fn ctxt:Context.generic =>
                      Position.reports_text [((Position.range (pos1, pos2)
                                               |> Position.range_position, Markup.intensify), "")]))
           | _ => fn _ => fn _ => I:Context.generic -> Context.generic\<close>)
       ("highlight", \<^here>, \<^here>)
\<close>
*)

C \<comment> \<open>Nesting ML code in C comments\<close> \<open>
int a (int b){int c; 
              return c;
              /*@@ \<approx>setup \<open>@{print_env'}\<close> */
              /*@@ highlight */
             }; 
                 
\<close>
ML\<open>
lookup_Cid_info (!ENV) "a";
lookup_Cid_info (!ENV) "c"
\<close>
(* Problematic : *)
C \<comment> \<open>Nesting ML code in C comments\<close> \<open>
int a (int b){int b; 
              return b;
              /*@@ highlight */
              /*@@ \<approx>setup \<open>@{print_env'}\<close> */}; 
                 
\<close>
ML\<open>
lookup_Cid_info (!ENV) "a";
lookup_Cid_info (!ENV) "b"
\<close>



section \<open>Converters for C-types\<close>

ML\<open>
local open C_Ast C_Env in

(*
  and 'a cTypeSpecifier = CVoidType0 of 'a | CCharType0 of 'a | CShortType0 of 'a 
                       | CIntType0 of 'a | CLongType0 of 'a | CFloatType0 of 'a 
                       | CDoubleType0 of 'a | CSignedType0 of 'a | CUnsigType0 of 'a | CBoolType0 of 'a |
*)
fun conv_ParseStatus_CDeclSpecS (SOME(C_Env.Parsed S)) = SOME S
   |conv_ParseStatus_CDeclSpecS _ = NONE


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


fun conv_cDerivedDeclarator_cSizeExpr_term (CArrDeclr0 (_,CArrSize0 (_,C_expr),_)) C_env thy = 
            SOME(hd((C11_Ast_Lib.fold_cExpression 
                                 (convertExpr_raw false dummyT C_env thy) C_expr [])))
   |conv_cDerivedDeclarator_cSizeExpr_term (CArrDeclr0 (_,CNoArrSize0 Z,_)) _ _ = NONE
   |conv_cDerivedDeclarator_cSizeExpr_term (_)  _ _ =  
            error("DeclarationSpec format not defined. [Clean restriction]")


fun conv_cDerivedDeclarator_typS (CArrDeclr0 (_,CArrSize0 _ ,_)) C_env thy = HOLogic.listT 
                    (*no enumerations ? nat ? *)
   |conv_cDerivedDeclarator_typS (CFunDeclr0 (Right(S,_), _, _)) C_env thy = I

(*
val [((Some (CDeclr0 (_,s,_,_,_)),_),_)] = A'
val [((Some (CDeclr0 (_,t,_,_,_)),_),_)] = B'
*)

fun conv_CDerivedDecl_typ [CFunDeclr0 (Right(SS,_), _, _)] = 
        fold_rev (fn CDecl0 (A, [((Some (CDeclr0 (_,TT,_,_,_)),_),_)], _) => 
                        (fn S => let val A_ty = the(conv_cDeclarationSpecifier_typ(SOME A))
                                     val TT_ty= case TT of 
                                                   [] => I
                                                  | _ => conv_CDerivedDecl_typ TT
                                 in  (TT_ty A_ty) --> S end)
                    | _ => error "CDerivedDecl (0) format not defined. [Clean restriction]") SS 
   |conv_CDerivedDecl_typ (S as (CArrDeclr0 _) :: _) = 
        fold     (fn (CArrDeclr0 _  ) => (fn tyF => HOLogic.listT o tyF)
                     | _ => error "CDerivedDecl (1) format not defined. [Clean restriction]") S I 
   |conv_CDerivedDecl_typ _ = error "CDerivedDecl (2) format not defined. [Clean restriction]"


fun conv_GlobalIdDescr_typ (S:C_Env.markup_ident) = 
    conv_CDerivedDecl_typ 
        (#params S) 
        (SOME(#ret S)  |> conv_ParseStatus_CDeclSpecS 
                       |> conv_cDeclarationSpecifier_typ
                       |> the) ;

end;
\<close>


section \<open>Tests on Expressions\<close>

text \<open>
First, we translate the expressions;
we can have binary operators, unary operators, or constants.
The attributs can be constantes or variables. 
In order to simulate the use of variables, we construct a "fake" record local_state
\<close>

global_vars test  (*intern label *)
            a     :: "int"

(* creation of a global variable Clean state with "a" *)
ML\<open>val Const(longid_a,Type("fun",[sigma_i, _])) = @{term "a"} \<close>


(* creation of two declarations with "a" an array and "f" a function *)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]
declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]

C\<open> int a[10+12][34][] = 1;
   short int f(int x [][], long double y);
\<close>

(* binding the resulting C_Env to env_expr *)

ML\<open>val env_expr : C_Module.Data_In_Env.T =  @{C\<^sub>e\<^sub>n\<^sub>v};\<close>

(* messing around with the C identifier "a" and "f" *)
ML\<open>
   val SOME(pos_list,ser,S)    = lookup_Cid_info env_expr "a";
   val SOME(pos_list',ser',S') = lookup_Cid_info env_expr "f";
\<close>
(* handy decompositions *)
ML\<open>

local open C_Ast C_Env in

   val [CArrDeclr0 (HH,CArrSize0 (_,CBinary0 X),_),
        CArrDeclr0 (_,CArrSize0  (_,CConst0 Y), _), 
        CArrDeclr0 (_,CNoArrSize0 Z,_)] = #params S
   val [CFunDeclr0 (Right([CDecl0 (A,A' as [((Some (CDeclr0 (_,TT,_,_,_)),_),_)],_),
                           CDecl0 (B,B' as [((Some (CDeclr0 (_,TT',_,_,_)),_),_)],_)],s), _, _)] = #params S'


val [((Some (CDeclr0 (_,s,_,_,_)),_),_)] = A'
val [((Some (CDeclr0 (_,t,_,_,_)),_),_)] = B'

end
\<close>


(* and the whole thing a bit more abstract with "a" and "f" *)
ML\<open>
map_option (conv_GlobalIdDescr_typ o #3) (lookup_Cid_info env_expr "a" );
map_option (conv_GlobalIdDescr_typ o #3) (lookup_Cid_info env_expr "f" );
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
val S =  (C11_Ast_Lib.fold_cStatement (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_stmt []); 
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
if(a == 1){
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
val S =  (C11_Ast_Lib.fold_cExternalDeclaration (convertExpr_raw false boolT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_ext_decl []);
\<close>

(*4*****************************************************************************************************)

declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]

C\<open>int a;\<close>

ML\<open>val ast_unit = @{C11_CTranslUnit}
   val env_unit = @{C\<^sub>e\<^sub>n\<^sub>v}
  \<close>

ML\<open>@{C\<^sub>e\<^sub>n\<^sub>v}\<close>

ML \<open>
val S =  (C11_Ast_Lib.fold_cTranslationUnit (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_unit []);
\<close>

ML\<open> open C_Ast;
val CTranslUnit0
    ([CDeclExt0
       ( CDecl0
           ([CTypeSpec0 ( CIntType0 (NodeInfo0 _))],
            [((Some(CDeclr0(Some(Ident0(SS_base(ST "a"),97,NodeInfo0 _)),[],None,[],NodeInfo0 _)),
               None), None)], NodeInfo0 _)
       )
    ],  
    NodeInfo0 _):
   C_Grammar_Rule_Lib.CTranslUnit = ast_unit
\<close>






end