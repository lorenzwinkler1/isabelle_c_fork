theory "Coder_Example_1"
  imports "../src/CleanCoder"
begin

section \<open>C-to-HOL Converters for C-types\<close>

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
            SOME(hd((C11_Ast_Lib.fold_cExpression (K I)
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

(* Fundsachen *)
C11_Ast_Lib.encode_positions;
C11_Ast_Lib.decode_positions;
C11_Ast_Lib.toString_abr_string;
C11_Ast_Lib.toString_nodeinfo;

C_Ast.SS_base
\<close>

section \<open>Global Variables, Local Variables, and Local Parameters\<close>
subsection\<open>An Environment Spy\<close>

ML\<open>
val ENV = Unsynchronized.ref (@{C\<^sub>e\<^sub>n\<^sub>v})
fun print_env' s _ stack _ env thy =
  let
    val () = (ENV:=env; writeln ("ENV " ^ C_Env.string_of env))
  in thy end
\<close>

ML\<open>open Position\<close>
setup \<open>ML_Antiquotation.inline @{binding print_env'}
                               (Scan.peek (fn _ => Scan.option Args.text)
                                >> (fn name => ("print_env' "
                                                ^ (case name of NONE => "NONE"
                                                              | SOME s => "(SOME \"" ^ s ^ "\")")
                                                ^ " " ^ ML_Pretty.make_string_fn)))\<close>

subsection\<open>Accessing the C_Env in an Example\<close>

C \<comment> \<open>Nesting ML code in C comments\<close> \<open>
int a(int b){int c; 
              return c;
              /*@@ \<approx>setup \<open>@{print_env'}\<close> */
              /*@@ highlight */
             }; 
                 
\<close>


ML\<open>
val a_res = lookup_Cid_info (!ENV) "a";
val b_res = lookup_Cid_info (!ENV) "b";
val c_res = lookup_Cid_info (!ENV) "c"
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





section \<open>Global Declarations via CEnv and via the Clean API\<close>

text \<open>
First, we translate the expressions;
we can have binary operators, unary operators, or constants.
The attributs can be constantes or variables. 
In order to simulate the use of variables, we construct a "fake" record local_state
\<close>

global_vars (test)  (*intern label *)
            a     :: "int"

(* creation of a global variable Clean state with "a" *)
ML\<open>val Const(longid_a,Type("fun",[sigma_i, _])) = @{term "a"}; \<close>


(* creation of two declarations with "a" an array and "f" a function *)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]
declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]

C\<open> int a[10+12][34][] = 1;
   short int f(int x [][], long double y)
     {int y; x=x;
      /*@@ \<approx>setup \<open>@{print_env'}\<close> */
      /*@@ highlight */}
     ;
      
\<close>

(* binding the resulting C_Env to env_expr *)

ML\<open>val env_expr : C_Module.Data_In_Env.T =  @{C\<^sub>e\<^sub>n\<^sub>v};\<close>

(* messing around with the C identifier "a" and "f" in the env AFTER the translation unit*)
ML\<open>
   val SOME(pos_list,ser,S)    = lookup_Cid_info env_expr "a";
   val SOME(pos_list',ser',S') = lookup_Cid_info env_expr "f";
   val NONE = lookup_Cid_info env_expr "x";
\<close>
(* handy decompositions *)
ML\<open>

local open C_Ast C_Env in

   val [CArrDeclr0 (HH,CArrSize0 (_,CBinary0 X),_),
        CArrDeclr0 (_,CArrSize0  (_,CConst0 Y), _), 
        CArrDeclr0 (_,CNoArrSize0 Z,_)] = #params S
   val [CFunDeclr0 (Right([CDecl0 (A,A' as [((Some (CDeclr0 (_,TT,_,_,_)),_),_)],_),
                           CDecl0 (B,B' as [((Some (CDeclr0 (_,TT',_,_,_)),_),_)],_)],s), _, _)] 
       = #params S'


val [((Some (CDeclr0 (_,s,_,_,_)),_),_)] = A'
val [((Some (CDeclr0 (_,t,_,_,_)),_),_)] = B'

end
\<close>

ML\<open>(#ret o #3 o the)(lookup_Cid_info env_expr "f" );\<close>

ML\<open>
conv_CDerivedDecl_typ;C_Ast.CFunDeclr0;
val S = hd ((#params o  #3 o the)(lookup_Cid_info env_expr "f" ));
val S' = conv_CDerivedDecl_typ [S] dummyT
\<close>
(* and the whole thing a bit more abstract with "a" and "f" *)
ML\<open>
map_option (conv_GlobalIdDescr_typ o #3) (lookup_Cid_info env_expr "a" );
(* map_option (conv_GlobalIdDescr_typ o #3) (lookup_Cid_info env_expr "f" ); *)
map_option (conv_GlobalIdDescr_typ o #3) (lookup_Cid_info env_expr "x" );
map_option (conv_GlobalIdDescr_typ o #3) (lookup_Cid_info env_expr "y" );
\<close>

section \<open>Tests on Expressions\<close>

subsection\<open>Ground Expressions\<close>

(*integer :*)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
C\<open>12\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v};
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (K I) (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr []);
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

val S = (C11_Ast_Lib.fold_cExpression (K I) (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr []);
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

val S = (C11_Ast_Lib.fold_cExpression (K I) (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr []);
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

val S = (C11_Ast_Lib.fold_cExpression (K I) (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr []);
val S' = conv_Cexpr_term env_expr sigma_i @{theory} ast_expr

\<close>

(*5*****************************************************************************************************)


C\<open>1 + 1\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (K I) (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr []);
val S' = conv_Cexpr_term env_expr sigma_i @{theory} ast_expr

\<close>

(*6*****************************************************************************************************)

(* construct environment with global variqble *)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "expression"]]
C\<open>1 * a\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (K I) (convertExpr_raw false unitT @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr [])
val S' = conv_Cexpr_term env_expr sigma_i @{theory} ast_expr

\<close>


(*7*****************************************************************************************************)


C\<open>a == 1\<close>
ML\<open>val ast_expr = @{C11_CExpr}
   val env_expr = @{C\<^sub>e\<^sub>n\<^sub>v}
\<close>

ML\<open>

val S = (C11_Ast_Lib.fold_cExpression (K I) (convertExpr_raw false sigma_i @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) ast_expr []);

\<close>

section \<open>statements\<close>

text \<open>Then, start the study of the statements (while, for, if then else, return, skip, ...)\<close>

(*1*****************************************************************************************************)

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "statement"]]
C\<open>{a = a+a;
   while(1 && 1){a = a * a; a = a + 1; }
  }
 \<close>
ML\<open>val ast_stmt = @{C11_CStat}   \<comment> \<open>C11 ast\<close>
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>        \<comment> \<open>C11 c-env\<close>

ML\<open>val C_Ast.CCompound0(a, b, c) = ast_stmt;\<close> \<comment> \<open>grabbing into an AST\<close>

\<comment> \<open>a C11 AST to Clean compilation, written as the internal Isabelle representation in Term.term.\<close>
\<comment> \<open>verbous tracing on.\<close>
ML\<open> 
val [S] =  (C11_Ast_Lib.fold_cStatement 
               regroup    \<comment> \<open>real rearrangements of stack for statement compounds\<close>
               (convertStmt_raw true sigma_i @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) 
                          \<comment> \<open>combinator handlicng an individual statement\<close>
                ast_stmt  \<comment> \<open>C11 ast\<close>
                []        \<comment> \<open>mt stack\<close>); 
\<close>

ML\<open>S\<close>
\<comment> \<open>pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

(*2*****************************************************************************************************)

(*if the body is empty, then we put a skip :*)

C\<open>
while(1){
         a = a+1;
}
\<close>
ML\<open>val ast_stmt = @{C11_CStat}
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>


ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
              regroup 
              (convertStmt_raw true sigma_i @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) 
              ast_stmt []); 
\<close>
\<comment> \<open>Clean pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

(*3*****************************************************************************************************)

C\<open>
for(a = 0; a < 2; a = a + 1){
   a = a + 5;
}
\<close>
 ML\<open>val ast_stmt = @{C11_CStat}
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>

(* crash due to typing problem *)
ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
           regroup 
           (convertStmt_raw true sigma_i @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) 
           ast_stmt 
           []); 
\<close>
\<comment> \<open>Clean pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>

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
              regroup 
              (convertStmt_raw true sigma_i @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) 
              ast_stmt 
              []); 
\<close>
\<comment> \<open>Clean pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>


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
ML\<open>val ast_stmt = @{C11_CStat}
   val env_stmt = @{C\<^sub>e\<^sub>n\<^sub>v}\<close>

(* problems with typing *)
ML\<open>
val [S] =  (C11_Ast_Lib.fold_cStatement 
            regroup 
            (convertStmt_raw true sigma_i @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) 
            ast_stmt []); 
\<close>
\<comment> \<open>Clean pretty print of the latter\<close>
ML\<open>writeln (Syntax.string_of_term_global @{theory} S);\<close>
(* the result is structurally incorrect. Where does the if come from ? *)

(*following : unfinished work.*)

section \<open>declarations\<close>

text \<open>The next step is to study the declarations. There are globals or locals declarations, 
and functions or variables declarations.\<close>

declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "external_declaration"]]
C\<open> int b = 1;\<close>
ML\<open>val ast_ext_decl = @{C11_CExtDecl}
   val env_ext_decl =  @{C\<^sub>e\<^sub>n\<^sub>v}

\<close>

(* initializers not yet supported; so this gives a local error *)
ML \<open>
val S =  (C11_Ast_Lib.fold_cExternalDeclaration regroup
                  (convertExpr_raw false sigma_i @{C\<^sub>e\<^sub>n\<^sub>v} @{theory}) 
                  ast_ext_decl 
                  []);
\<close>

(*4*****************************************************************************************************)

declare [[C\<^sub>e\<^sub>n\<^sub>v\<^sub>0 = last]]
declare [[C\<^sub>r\<^sub>u\<^sub>l\<^sub>e\<^sub>0 = "translation_unit"]]

C\<open>int  yyy ;\<close>

ML\<open>val ast_unit = @{C11_CTranslUnit}
   val env_unit = @{C\<^sub>e\<^sub>n\<^sub>v}
  \<close>

C\<open>int  zzz ;\<close>

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
             val typ = conv_cDeclarationSpecifier_typ (SOME tys)
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
setup \<open>conv_transl_unit ast_unit'\<close>
ML    \<open>(Symtab.dest)(StateMgt_core.get_state_field_tab_global @{theory});\<close>

end