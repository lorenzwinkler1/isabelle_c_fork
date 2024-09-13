(******************************************************************************
 * Isabelle/C/Clean
 *
 * Copyright (c) 2023 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)


theory CleanCoderTypAEnv
  imports "Isabelle_C.C_Main"
          "HOL.Real"
          "Clean.Clean"
begin

ML\<open>val VERBOSE = Unsynchronized.ref false

fun debug str = if !VERBOSE then writeln str else ();\<close>

subsection\<open>Auxilliary Functions: Printing Functions\<close>

text \<open>We will use different auxiliary functions to do operations on the terms, and to help
to understand what kind of types and objects we do manipulate. \<close>



ML\<open>

(*------toStrings et affichages-------*)

(*renvoie un string représentant un objet data*)
fun toString_data data = case data of
      C11_Ast_Lib.data_bool e      => "Bool : "^Bool.toString e
     |C11_Ast_Lib.data_int e       => "Int : "^Int.toString e
     |C11_Ast_Lib.data_string e    => "String : "^e
     |C11_Ast_Lib.data_absstring e => "AbsString : "^e
     |C11_Ast_Lib.data_nodeInfo e  => "nodeInfo : "^ @{make_string} e

 
fun toString_args args = "["^(String.concatWith ", "(List.map (toString_data) args))^ "]"


fun to_String_positiona (C_Ast.Position0 (i,S, k,l)) = "POS "^ @{make_string} S
  | to_String_positiona C_Ast.NoPosition0 = ""
  | to_String_positiona C_Ast.BuiltinPosition0 = ""
  | to_String_positiona C_Ast.InternalPosition0 = ""

fun toString_nodeInfo (C_Ast.OnlyPos0(p, (_, _))) = to_String_positiona p
   |toString_nodeInfo (C_Ast.NodeInfo0(p, (_, _), C_Ast.Name0 name))  
                                                  = to_String_positiona p ^ Int.toString name

val toString_nodeInfo = C11_Ast_Lib.toString_nodeinfo

(*affiche le contenue d'un nodeInfo*)
fun print_node_info (a as { tag, sub_tag, args }:C11_Ast_Lib.node_content) 
                    (b :  C_Ast.nodeInfo ) 
                    (c : term list) = 
           (writeln ("tag : \""^tag^"\""^
              (*("\ncode ascii :\n"^toString_ascii_code ((String.size tag) - 1) tag)^*)
              "\n subtag   : "  ^sub_tag^
              "\n args     : "  ^(toString_args args)^
              "\n nodeInfo : "  ^(toString_nodeInfo b)^
              "\n termList : "  ^(String.concatWith ","(List.map (@{make_string}) c)) 
              ^"\n --------------------\n")
          )

(*------------compiler-----------*)



fun drop_dark_matter x =(XML.content_of o YXML.parse_body) x 


(*récupère un node_content, et renvoie simplement Free(label, type)*)
fun node_content_2_free (x : C11_Ast_Lib.node_content) =
  let val C11_Ast_Lib.data_string a_markup = hd(#args(x));         
      val id = hd(tl(String.tokens (fn x => x = #"\"")(drop_dark_matter a_markup)))
    in Free(id,dummyT) end  (* no type inference *);

(*supprime toutes les occurences de c dans s*)
    
fun remove_char_from_string c s =
  let  fun aux c s acc n =
          case n of
             (~1) => acc
          |  0 => if String.sub (s, 0) = c then acc else (Char.toString (String.sub (s, 0)))^acc
          |  n => if String.sub (s, n) = c then aux c s acc (n - 1)
                  else aux c s ((Char.toString (String.sub (s, n)))^acc) (n - 1)
  in   aux c s "" ((String.size s) - 1)
  end

(*si le term est un nombre, alors le transforme en bool*)
\<close>


subsection\<open>Conversion of \<^verbatim>\<open>C_Ast.cDeclarationSpecifier\<close> to HOL types\<close>

ML\<open>

structure C11_TypeSpec_2_CleanTyp =
struct 

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


fun conv_cDerivedDeclarator_typS (CArrDeclr0 (_, _ ,_) :: R) = 
                    HOLogic.listT o (conv_cDerivedDeclarator_typS R)
                    (*no enumerations ? nat ? *)
   |conv_cDerivedDeclarator_typS (CFunDeclr0 (Right(S,_), _, _) :: R) = I
   |conv_cDerivedDeclarator_typS _ = I

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
end
\<close>


subsection\<open>Reconstruction of another version of C Environment\<close>


(* 
In the abstract syntax, the Ident0 constructors found in CDeclr0 are variable and function 
declarations, which occupy an element in our final list. Ident0 may also appear as references 
to variables and function calls, here we only care about the function calls.

In the other words: in

int call = fibo(global)

  call is part of Declr
  call, fibo and global are part of Decl

We keep the information of call Declr in our list
We take not of fibo in Decl if and only if we're in a function body, AKA CCompound0 constructor
*)

(* read_function_spec in Clean.thy *)
(* or define_body_main, their params must be  *)
(* get the term list of stmt block from convStmt *)

ML\<open>
signature C_ABS_ENVIRONMENT = 
  sig

  datatype functionCategory = Final (* no function calls *)
                            | NonFinal (* at least 1 foreign function call *)
                            | Recursive      (* at least 1 self call *)
                            | MutuallyRecursive of string list (* at least 1 foreign function call, 
                                                  in which the foreign function calls the former *)

  datatype identType = Global
                     | FunctionCategory of functionCategory 
                                           * C_Ast.nodeInfo C_Ast.cStatement option
                     | Local     of string (* name of function *)
                     | Parameter of string (* name of function *)
  
  datatype identifier = Identifier of string * Position.T * typ * identType

  val parseTranslUnitIdentifiers: C_Ast.nodeInfo C_Ast.cTranslationUnit 
                                  -> identifier list 
                                  -> identifier list 
                                  -> string list Symtab.table 
                                  -> identifier list * string list Symtab.table

  val printIdentifier: identifier -> unit

  val extractStatement: identifier list -> string -> C_Ast.nodeInfo C_Ast.cStatement

  end

structure C_AbsEnv : C_ABS_ENVIRONMENT = 
struct

datatype functionCategory = Final          (* no function calls *)
                          | NonFinal       (* at least 1 foreign function call *)
                          | Recursive      (* at least 1 self call, poss. other calls *)
                          | MutuallyRecursive of string list 
                                           (* at least 1 mutual rec. function call, 
                                              possible other calls *)

datatype identType = Global
                   | FunctionCategory of functionCategory * C_Ast.nodeInfo C_Ast.cStatement option
                   | Local of string       (* name of function *)
                   | Parameter of string   (* name of function *)

datatype identifier = Identifier of string * Position.T * Basic_Term.typ * identType

open C_Ast C11_TypeSpec_2_CleanTyp;

(*** --- HELPER FUNCTIONS --- ***)

fun selectFromNodeContent tagList (a: C11_Ast_Lib.node_content) (b: C_Ast.nodeInfo) c =
    if List.exists (fn t => t = #tag a) tagList  then (a, b) :: c else c;


(* TODO: string -> HOLogic.typ function or node_content \<rightarrow> HOLogic.typ with #tag = CTypeSpec0 *)
(* TODO: add HOLogic.listT HOLogic.intT *)
fun str2HOLogic str =
  case str of
    "CIntType0" => HOLogic.intT
  | "CUnsigType0" => HOLogic.natT
  | s => error ("Unknown: " ^ s)

(* Infers the name of the node_content, which should be #tag node_content = "Ident0 *)
fun node_content_parser (x : C11_Ast_Lib.node_content) =
  (debug ("node_content_parser: "  ^ @{make_string} x); 
   let fun drop_dark_matter x =(XML.content_of o YXML.parse_body) x 
      val  C11_Ast_Lib.data_string a_markup = hd(#args(x))
      val id = hd(tl(String.tokens (fn x => x = #"\"")(drop_dark_matter a_markup)))
   in id end)  (* no type inference *);

fun cutDownTypeSpec ((nameNodeContent: C11_Ast_Lib.node_content, nameNodeInfo) :: R) =
  (debug("cutDownTypeSpec: " ^ @{make_string} R);
  (* This function only removes 1 node_content with the tag "CTypeSpec0" and not successive ones. *)
  (* When `R` is replaced with `cutDownTypeSpec` to make this function recursive, 
     the output is an empty list *)
  if #tag nameNodeContent = "CTypeSpec0" then 
      (debug("cutting: " ^ @{make_string} nameNodeContent); cutDownTypeSpec R)
  else (debug("not cutting: " ^ @{make_string} nameNodeContent); (
        nameNodeContent: C11_Ast_Lib.node_content, nameNodeInfo) :: R))
  | cutDownTypeSpec [] = []

fun isFunction identType =
  case identType of
    FunctionCategory(_) => true
  | _ => false

fun isMutuallyRecursive identType =
  case identType of
    FunctionCategory(MutuallyRecursive(_), _) => true
  | _ => false

fun identifierExists identList identName = 
  List.exists (fn Identifier(name, _, _, _) => (name = identName)) identList

fun functionIdentifierExists identList functionName =
  List.exists (fn Identifier(name, _, _, identType) => (name = functionName) 
  andalso isFunction identType) identList

fun changeFunctionCategory (Identifier(name, pos, ty, idType) :: s) functionName newCategory =
  if name = functionName then Identifier(name, pos, ty, FunctionCategory(newCategory)) :: s
  else Identifier(name, pos, ty, idType) :: changeFunctionCategory s functionName newCategory
  | changeFunctionCategory [] _ _ = []
                                    
fun getMutuallyRecursiveCalls (Identifier(name, pos, ty, idType) :: s) functionName =
  if name = functionName andalso isMutuallyRecursive idType
  then let val FunctionCategory(MutuallyRecursive(l), _) = idType
       in l end
  else getMutuallyRecursiveCalls s functionName
  | getMutuallyRecursiveCalls [] _ = []

fun isCall0
    ((nc, _) :: R) =
    if #tag nc = "CCall0" then true
    else isCall0 R
  | isCall0 [] = false
fun readCall0
    ((nc, _) :: R) =
    if #tag nc = "CCall0" then R
    else readCall0 R
  | readCall0 [] = error("(readCall0) CCall0 not found")

(*** --- HELPER FUNCTIONS END ***)

(* parses a (node_content * nodeInfo) list
   a list of identifiers and list of (unique!) function calls *)
fun parseNodeContent
    (HOLType: Basic_Term.typ option)
    ((nc, ni) :: R)
    identList
    oldIdents
    functionCallList
    (idType: identType) =
    let val Left(posL, posR) = C_Grammar_Rule_Lib.decode ni
    in (debug("node content parsing: " ^ @{make_string} ((nc, ni) :: R));
       case #tag nc of
         "CTypeSpec0" (* this is the start variable declaration list (one or multiple) *)
         => let val HOLType = #sub_tag nc |> str2HOLogic
            in parseNodeContent (SOME HOLType) (cutDownTypeSpec (R)) identList oldIdents functionCallList idType
            end
       | "Ident0"
         => let val name = node_content_parser nc
                fun transform_list_type ((r,_)::R) ty = if #tag r = "CArrDeclr0" then HOLogic.listT (transform_list_type R ty) else ty
                   | transform_list_type [] ty = ty 
                fun skip_arr_decls ((r,b)::R) = if #tag r = "CArrDeclr0" then skip_arr_decls R else ((r,b)::R)
                   | skip_arr_decls [] = []
            in (debug("(parseNodeContent) parsing: " ^ name);
               if (* if the identifier already exists, this is either a reference to a variable 
                     (which we ignore) or a declared function call *)
                  (identifierExists (identList) name) orelse null R
               then if functionIdentifierExists (identList@oldIdents) name (*potential error when function is redefined as variable*) 
                    then parseNodeContent NONE R identList oldIdents (name :: functionCallList) idType
                    else parseNodeContent NONE R identList oldIdents functionCallList idType
               else (* otherwise, it is a variable declaration or an undeclared function call or a reference to a variable defined elsewhere*) 
                    let val (nc2, ni2) :: R = R
                    in case #tag nc2 of
                     "CDeclr0" (* this is the end of one variable declaration *)
                      => (debug("(parseNodeContent) this is a DECLARATION: "^name);
                          parseNodeContent HOLType R (Identifier(node_content_parser nc, posL, 
                             (fn (SOME(a)) => a) HOLType, idType) :: identList) oldIdents functionCallList idType)
                   | "CArrDeclr0" (* this is an array variable declaration, thus we count how many ArrDecls are here
                                      #tag (hd R) is "CDeclr0" so we skip it *)
                     => 
                          parseNodeContent HOLType (skip_arr_decls R) (Identifier(node_content_parser nc, posL, 
                             transform_list_type R (HOLogic.listT (the HOLType)), idType) :: identList) oldIdents 
                             functionCallList idType
                   | "CTypeSpec0"
                     => parseNodeContent HOLType (R) (Identifier(node_content_parser nc, posL,
                             (fn (SOME(a)) => a) HOLType, idType) :: identList) oldIdents functionCallList idType
                   | s  =>(* this is a function call, #tag nc2 is either another Ident0 which is a 
                          parameter which we ignore or CCall0 in which the function calls ends *)
                     if (isCall0 ((nc2, ni2) :: R)) then (debug("function call detected (tag = " ^ s ^ ") : " ^ @{make_string} (R));
                         parseNodeContent HOLType (readCall0 ((nc2, ni2) :: R)) identList oldIdents
                             (node_content_parser nc :: functionCallList) idType) else
                          parseNodeContent HOLType R identList oldIdents functionCallList idType
                   end)
             end
        | "CDeclr0" (* artifact: list of params have a CDeclr0 at the end, so we ignore this *)
          => parseNodeContent HOLType R identList oldIdents functionCallList idType
        | "CCall0" (* artifact: list of params have a CDeclr0 at the end, so we ignore this *)
          => parseNodeContent HOLType R identList oldIdents functionCallList idType
        | _
          => error("node content parsing failure: " ^ @{make_string} ((nc, ni) :: R)))
    end
  | parseNodeContent _ [] identList oldIdents functionCallList _ = 
    (debug("(parseNodeContent) finished: identList--" ^ @{make_string} identList 
                             ^ " functionCallList--" ^ @{make_string} functionCallList);
    (identList, functionCallList))

(* takes in the functionName, the functionCallTable, and functionCalls 
   (list of function calls called by functionName) and determines the function category of 
   functionName and updates the functionCallTable *)
fun parseFunctionCalls
    A
    identList
    functionCallTable
    (B :: R)
    functionCategory = 
    let (* if this function has been defined before, we get a list of function calls in its definition *)
        val BFunctionCalls = case Symtab.lookup functionCallTable B of
                                   SOME(functionCalls) => functionCalls
                                 | NONE => []
        val AFunctionCalls = case Symtab.lookup functionCallTable A of
                                   SOME(functionCalls) => functionCalls
                                 | NONE => []
        (* We do not update the list of identifiers `identList` *)
        (* Instead, we update the function call table *)
    in  (* Case 1: if A calls B, and AFunctionCalls (empty/contains B)
                                 and BFunctionCalls does not contain A
                                 and identList contains B
                   => A is Non-Final *)
        if not (List.exists (fn name => A = name) BFunctionCalls) 
            andalso Symtab.exists (fn (k, _) => B = k) functionCallTable
            andalso not (A = B)
        then let val newFunctionCallTable = Symtab.update (A, B :: AFunctionCalls) functionCallTable
             in (debug("CASE 1: " ^ B); 
                 parseFunctionCalls A  identList newFunctionCallTable R NonFinal) 
             end
        else 
        (* Case 2: if A calls B, BFunctionCalls does not contain A
                                 and identList does not contain B
                   => A is EITHER MutuallyRecursive or Non-Final, depending on B's definition
                      But for now, we will name it Non-Final *)
        if not (List.exists (fn name => A = name) BFunctionCalls)
            andalso not (Symtab.exists (fn (k, _) => B = k) functionCallTable)
            andalso not (A = B)
        then let val newFunctionCallTable = Symtab.update (A, B :: AFunctionCalls) functionCallTable
             in (debug("CASE 2: " ^ B); 
                 parseFunctionCalls A identList newFunctionCallTable R NonFinal) 
             end
        else
        (* Case 3: if A calls B, and AFunctionCalls (empty/contains B)
                                 and BFunctionCalls contains A
                   => A is MutuallyRecursive *)
        if List.exists (fn name => A = name) BFunctionCalls
            andalso not (A = B)
        then let fun extractStatement identList ident =
                    let val SOME(identifier) = List.find (fn Identifier(name, _, _, _) => name = ident) identList
                        val Identifier(_, _, _, FunctionCategory(_, SOME(ast_stmt))) = identifier
                    in ast_stmt end
                 val newIdentList = changeFunctionCategory identList B 
                                       (MutuallyRecursive(A :: getMutuallyRecursiveCalls identList B), 
                                        SOME(extractStatement identList B))
                 val newFunctionCallTable = Symtab.update (A, B :: AFunctionCalls) functionCallTable
             in (debug("CASE 3: " ^ B); 
                 parseFunctionCalls A newIdentList newFunctionCallTable R 
                        (MutuallyRecursive(B :: getMutuallyRecursiveCalls identList A))) 
             end
        else
        (* Case 4: if A calls A => A is Recursive *)
        if B = A
        then let val newFunctionCallTable = Symtab.update (A, B :: AFunctionCalls) functionCallTable
             in (debug("CASE 4: " ^ B); 
                 parseFunctionCalls A identList newFunctionCallTable R Recursive) 
             end
        else error("We've found an edge case!" ^ "\nA: " ^ A ^ "\nB: " ^ B)
      end
  | parseFunctionCalls _ identList functionCallTable [] functionCategory = 
              (functionCategory, identList, functionCallTable) 

fun parseParams L (functionName: string) =
    let val (identList, _) = parseNodeContent NONE L [] [] [] (Parameter(functionName))
    in identList end
 
(* Parses identifiers in a function body.
  We are looking for variable declarations and function calls.
  In order to look for function calls, we have a SML variable `functionCallTable`
  that records all function calls in a given function definition *)
fun parseLocals 
    (* List of node_content * nodeInfo of local identifiers *)
    L 
    (* Function name of the function body we're currently in *)
    (functionName: string) 
    (* Table of previous function names with list of function calls *)
    (functionCallTable: string list Symtab.table)
    (* Previous identifiers *)
    (identList: identifier list)
    (* Identifiers from a previous translation unit (synthesized from env)*)
    (oldIdents: identifier list) =
    (debug("parsing locals: " ^ @{make_string} L);
    let val (identList, functionCalls) = parseNodeContent NONE L identList oldIdents [] (Local(functionName))
        val (functionCategory, identList, functionCallTable) = 
                     parseFunctionCalls functionName identList functionCallTable functionCalls Final
    in (identList, functionCategory, functionCallTable) end)

(* Parse a cExternalDeclaration datatype (which can either be a variable declaration in a
  CDeclExt0 constructor or a function declaration/definition (to be checked) in a CFunDef0
  constructor. *) 
fun parseExternalDeclaration 
    (CDeclExt0(declaration : nodeInfo cDeclaration))
    identList 
    oldIdents
    functionCallTable =
  (* Select Ident0 constructors in a cDeclaration. Here we suppose that there is only 1 *)
  let val CDecl0(declarationSpecifierList, _, _) = declaration
          (* declarationHOLType should not be NONE. Hence, we remove SOME, this will appropriately
            trigger an error otherwise *)
      (*val declarationHOLType = conv_cDeclarationSpecifier_typ (SOME(declarationSpecifierList)) 
                |>  (fn (SOME(a)) => a)*)
      val nodeContentList = rev (C11_Ast_Lib.fold_cDeclaration (K I) 
                 (selectFromNodeContent ["Ident0", "CTypeSpec0", "CArrDeclr0", "CDeclr0", "CCall0"]) 
                 declaration [])
      val (newIdentList, _) = parseNodeContent NONE nodeContentList identList oldIdents [] Global
  in (debug("parsing global variable: " ^ @{make_string} nodeContentList); 
      (newIdentList, functionCallTable)) 
  end
  | parseExternalDeclaration (CFDefExt0(CFunDef0((* return type of function *)
                                                 declarationSpecifierList: nodeInfo cDeclarationSpecifier list, 
                                                 (* function name, and parameter names and types *)
                                                 declarator: nodeInfo cDeclarator,
                                                 (* dunno, it's empty *)
                                                 declarationList: nodeInfo cDeclaration list,
                                                 (* function body *)
                                                 statement: nodeInfo cStatement,
                                                 ndInfo: nodeInfo)))
                              identList 
                              oldIdents
                              (functionCallTable: string list Symtab.table) =
    let val functionReturnHOLType = conv_cDeclarationSpecifier_typ (SOME(declarationSpecifierList)) 
                                    |>  (fn (SOME(a)) => a)
           (* To be renamed something else... *)
        val (functionNodeContent, functionNodeInfo) :: param = rev (C11_Ast_Lib.fold_cDeclarator (K I) 
              (selectFromNodeContent ["Ident0", "CTypeSpec0", "CArrDeclr0", "CDeclr0"]) declarator []) 
        val functionName = node_content_parser functionNodeContent
        val Left(posL, posR) = C_Grammar_Rule_Lib.decode functionNodeInfo
        val paramIdentifiers = parseParams param functionName
        val statementContentList = rev (C11_Ast_Lib.fold_cStatement (K I) 
                                        (selectFromNodeContent ["Ident0", "CTypeSpec0", 
                                                                "CArrDeclr0", "CDeclr0", "CCall0"]) 
                                        statement [])
        val (newIdentList, functionCategory, newFunctionCallTable) = 
                                    parseLocals statementContentList functionName functionCallTable 
                                        (paramIdentifiers @ identList) oldIdents
    in (Identifier(functionName, posL, functionReturnHOLType, 
                       FunctionCategory(functionCategory, SOME(statement))) :: newIdentList, 
                       newFunctionCallTable) 
    end

  | parseExternalDeclaration s _ _ _= error("Unsupported:  " ^ @{make_string} s)

fun parseTranslUnitIdentifiers 
        (CTranslUnit0(externalDeclaration :: R, translUnitNodeInfo)) 
        identList
        oldIdents
        (functionCallTable: string list Symtab.table) =
        let val (newIdentList, newFunctionCallTable) = 
                    parseExternalDeclaration externalDeclaration identList oldIdents functionCallTable
        in (debug("newIdentList (parseTranslUnitIdentifiers): " ^ @{make_string} newIdentList); 
            parseTranslUnitIdentifiers (CTranslUnit0(R, translUnitNodeInfo)) 
                                       newIdentList oldIdents newFunctionCallTable) 
        end
  | parseTranslUnitIdentifiers _ identList oldIdents functionCallTable = (identList, functionCallTable)

fun printIdentifier (Identifier(name, pos, typ, idType)) =
    writeln("Identifier: " ^ name ^ " " ^ Position.here pos ^
            "\nType: " ^ @{make_string} typ ^
            "\nCategory: " ^ (fn idType => case idType of FunctionCategory(s, _) 
                                  => @{make_string} s | e => @{make_string} e) idType)

fun extractStatement identList ident =
  let val SOME(identifier) = List.find (fn Identifier(name, _, _, _) => name = ident) identList
      val Identifier(_, _, _, FunctionCategory(_, SOME(ast_stmt))) = identifier
  in ast_stmt end

end (* structure *)
\<close>

end