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


theory "CleanCoder"
  imports "Isabelle_C.C_Main" 
          "Clean.Clean"
          "CleanCoderTypAEnv"
begin




section\<open>A small compiler to Isabelle Clean term's.\<close>

text \<open>
The goal of this project is to develop a translation function from the language C11 to
Clean. In particular, the function take as an argument the result of the parser, and create 
a typed \<lambda>-term which encoded the semanticaly equivalent program in Clean.\<close>


subsection\<open>Auxilliary Functions: Elementary Term Conversions\<close>

ML\<open>

fun term_to_bool term = case term of
        Const ("Groups.one_class.one", _) => \<^term>\<open>True\<close>
      | Const ("Groups.zero_class.zero", _) => \<^term>\<open>False\<close> 
      |(Const ("Num.numeral_class.numeral", _) $ _) => \<^term>\<open>True\<close>
      |_ => term

exception EmptyList
exception WrongFormat of string
exception UnknownTyp of string


(*renvoie le type final d'une fonction, ou le type d'une constante*)
fun lastype_of (Type(_, [x])) = x | lastype_of (Type(_, [_, y])) = y
(*renvoie le type du premier attribut d'une fonction, ou le type d'une constante*)
fun firstype_of (Type(_, [x])) = x | firstype_of (Type(_, x::_)) = x 

(* Creates a result_update_term for the local state *)
fun mk_result_update thy sigma_i=
  let
   val _ = writeln("TRACE 1.8: "^(@{make_string} sigma_i))
   val Type(ty_name,_) = sigma_i
   val _ = writeln("TRACE 1.9: "^(@{make_string} ty_name))
   val s = ty_name |> String.tokens (fn x => x =  #".") |> tl |> hd
   val s' = String.substring(s, 0, size s - size "_scheme")^".result_value_update"
   val _ = writeln("TRACE 2.0: "^s)
  in Syntax.read_term_global thy s' end;

fun extract_ids long_id sigma_i =
  let  val id = List.last(String.tokens (fn x => x = #".") long_id)
       val Type(ty_name, _) = sigma_i;
       val ty_name = ty_name |> String.tokens (fn x => x =  #".") |> tl |> hd
       val local_state = String.substring (ty_name, 0, 
                                           String.size ty_name 
                                           - (String.size "_scheme"))
                                                     (*dangerous. will work only for the local case *)
  in  (id, local_state^"."^id) end

fun read_N_coerce thy name ty = 
       (* a very dirty hack ... but reconstructs the true \<open>const_name\<close> 
          along the subtype hierarchy, but coerces it to the current sigma*)
       let val s = drop_dark_matter(Syntax.string_of_typ_global thy ty)
           val str = name ^ " :: " ^ s 
       in  Syntax.read_term_global thy str end
\<close>

subsection\<open>C11 Expressions to Clean Terms\<close>


ML\<open>

(*
verbose : boolean (to do some printing and help to debug)
sigma_i : typ (actual type)
env : context (unuse right now but will probably be usefull)
thy : theory (the actual theory)
a, b, c : those values are from the parser
*)

structure C11_Expr_2_Clean =

struct

local open HOLogic in


(* Copied from CleanCoder2... *)
fun node_content_parser (x : C11_Ast_Lib.node_content) =
  let fun drop_dark_matter x =(XML.content_of o YXML.parse_body) x 
      val  C11_Ast_Lib.data_string a_markup = hd(#args(x))
      val id = hd(tl(String.tokens (fn x => x = #"\"")(drop_dark_matter a_markup)))
    in id end  (* no type inference *);

fun convertExpr verbose (sigma_i: typ) env thy 
           (a as { tag, sub_tag, args }:C11_Ast_Lib.node_content) 
           (b:  C_Ast.nodeInfo )   
           (c : term list) =
    ((if verbose then print_node_info a b c else ());
    case tag of
(*variables*)
(*here, we get the full name of the variable, then we return the term well named and typed.
Bound 0 is usefull for the statements, and can easily be deleted if necessary*)
      "Ident0" =>  (let val id = node_content_parser a
                        fun is_id_name (C_AbsEnv.Identifier(id_name, _, _, _)) = (id_name = id)
                           |is_id_name _ = false
                        val C_AbsEnv.Identifier(_, _, ty, cat) = case List.find is_id_name env of
                                                SOME(identifier) => identifier
                                              | NONE => error("(convertExpr) identifier " 
                                                              ^ id ^ " not recognised")
                        val Type(local_state_scheme, _) = sigma_i;
                        val local_state = String.substring (local_state_scheme, 0, 
                                                                String.size local_state_scheme 
                                                                 - (String.size "_scheme"))
                                              (*dangerous. will work only for the local case *)
                        val lid = local_state^"."^id
                    in case cat of
                        C_AbsEnv.Global => read_N_coerce thy id (sigma_i --> ty) $ Free("\<sigma>",sigma_i) :: c
                      | C_AbsEnv.Local(_) => Const(@{const_name "comp"}, 
                                                   (HOLogic.listT ty --> ty) 
                                                   --> (sigma_i --> HOLogic.listT ty) 
                                                   --> sigma_i --> ty) 
                                              $ Const(@{const_name "hd"}, HOLogic.listT ty --> ty) 
                                              $ read_N_coerce thy lid (sigma_i --> HOLogic.listT ty) 
                                              $ Free("\<sigma>",sigma_i) :: c
                      | C_AbsEnv.Parameter(_) => Free (id, ty) :: c
                      | C_AbsEnv.FunctionCategory(C_AbsEnv.MutuallyRecursive(_), _) =>
                                error("Mutual recursion is not supported in Clean")
                      | C_AbsEnv.FunctionCategory(_, _) => 
                            let val Const(id, ty) = Syntax.read_term_global thy id
                                val args = firstype_of ty
                            in Const(id, ty) :: c end
                      | c => error("(convertExpr) unrecognised category : " ^ @{make_string} c)
                    end)
     |"Vars0" => c
     |"CVar0" => c
(*expressions*)
(*At this point, what we do for binary or unary epressions is simple thanks to the makers. *)
     (*binary operations*)
     |"CBinary0" => (case (drop_dark_matter sub_tag, c) of
                      (*arithmetic operations*) 
                      ("CAddOp0",b::a::R) => (Const(@{const_name "plus"}, fastype_of a --> fastype_of b --> intT) $ a $ b :: R)
                    | ("CMulOp0",b::a::R) => (Const(@{const_name "times"}, fastype_of a --> fastype_of b --> intT) $ a $ b :: R)
                    | ("CDivOp0",b::a::R) => (Const(@{const_name "divide"}, fastype_of a --> fastype_of b --> intT) $ a $ b :: R)
                    | ("CSubOp0",b::a::R) => (Const(@{const_name "minus"}, fastype_of a --> fastype_of b --> intT) $ a $ b :: R)
                      (*boolean operations*) 
(*for boolean operations, because in C boolean are in fact integers, we need to
translate integers in booleans. That's what term_to_bool t do.
  -if t integer and t = 0 then false else if t integer and t > 0 then true else t
  -for example, 1 \<and> 0 will be true \<and> false, and 1000 \<or> a will be true \<or> a
*)
                    | ("CAndOp0", b::a::R) => (mk_conj (term_to_bool a, term_to_bool b) :: R)
                    | ("CLndOp0", b::a::R) => (mk_conj (term_to_bool a, term_to_bool b) :: R)
                    | ("COrOp0", b::a::R) => (mk_disj (term_to_bool a, term_to_bool b) :: R)
                    | ("CLorOp0", b::a::R) => (mk_disj (term_to_bool a, term_to_bool b) :: R)
                    | ("CXorOp0", b::a::R) => (mk_not (mk_eq (term_to_bool a, term_to_bool b))::R)
                      (*equality*)
                    | ("CEqOp0", b::a::R) => (mk_eq ( a, b) :: R)
                    | ("CNeqOp0", b::a::R) => (mk_not (mk_eq ( a, b))::R)
                      (*comp*)
                    | ("CLeOp0", b::a::R) => (Const(@{const_name "less"}, 
                                                    fastype_of a --> fastype_of b --> boolT) 
                                             $ a $ b :: R) 
                    | ("CGrOp0", b::a::R) => (Const(@{const_name "less"}, 
                                                    fastype_of a --> fastype_of b --> boolT) 
                                             $ b $ a :: R) 
                    | ("CLeqOp0", b::a::R) => (Const(@{const_name "less_eq"}, 
                                                     fastype_of a --> fastype_of b --> boolT) 
                                              $ a $ b :: R) 
                    | ("CGeqOp0", b::a::R) => (Const(@{const_name "less_eq"}, 
                                                     fastype_of a --> fastype_of b --> boolT) 
                                              $ b $ a :: R)
                    | _ => (writeln ("sub_tag all " ^sub_tag^" :>> "^ @{make_string} c);c ))
     (*unary operations*)
     |"CUnary0" =>  (case (drop_dark_matter sub_tag, c) of
                    ("CNegOp0", a::R) => (mk_not (term_to_bool a) :: R)
                    |("CMinOp0", a::R) => (Const(@{const_name uminus}, fastype_of a --> intT) $ a :: R)
                    |_ => (writeln ("unknown sub_tag for CUnary0"^sub_tag); c))
     (*constants*)
(*for the constants, we can use the makers*)
     |"CConst0"   => c (* skip this wrapper *)
     |"CInteger0" =>let val C11_Ast_Lib.data_int n = hd args
                    in  (mk_number intT n)::c end
     |"CIntConst0"=> c (* skip this wrapper *)
     |"CString0"  => let val C11_Ast_Lib.data_string s = hd args
                     in  (mk_string s)::c end
     |"CStrConst0"=> c (* skip this wrapper *)
(*for the char, we actually get a 1-sized string, we just need to do a little translation*)
     |"CChar0"    => let val C11_Ast_Lib.data_string s = hd args;
                         val code = String.sub (s, 0)
                     in  (mk_char (Char.ord code))::c end
     |"CCharConst0"=> c (* skip this wrapper *)
      (*for real numbers, as we can't have inite-sized numbers, we can always translate them 
        as rationals numbers. For example, 3.1415926535 will be encoded as 314156535/100000000*)     
     |"CFloat0"    => let val C11_Ast_Lib.data_string s = (hd args)
                         val s' = implode (tl (String.tokens (fn x => x = #"\"" orelse x = #")")(drop_dark_matter s)))
                         val s'' = remove_char_from_string #"." s'
                         val SOME integer = Int.fromString s''
                      in Const (@{const_name "divide"}, realT --> realT --> realT) 
                         $ mk_number realT (integer) 
                         $  ((if (String.size s'') = 2 then  mk_number realT 10
                              else (Const (@{const_name "power"}, realT --> natT --> realT) 
                                   $ mk_number realT 10 
                                   $ mk_number natT ((String.size s'') - 1)))) 
                         ::c
                   end
     |"CIndex0" => (case c of 
                     (idx::root::R) => let fun destListT arg =
                                            case arg of (Type(@{type_name list},[t])) => t
                                           val idx_term = case fastype_of idx of
                                                            Type(@{type_name "nat"},[]) => idx
                                                          | Type(@{type_name "int"},[]) =>
                                                                 (Const (@{const_name "Int.nat"}, 
                                                                         intT --> natT) $ idx)
                                                          | _ => error "illegal index type"
                                       in   Const(@{const_name List.nth},
                                                  fastype_of root 
                                                  --> natT 
                                                  --> destListT(fastype_of root))
                                            $ root
                                            $ idx_term :: R 
                                       end
                   | _ => error("unsupported indexing formal."))
     |"CFloatConst0"=> (c) (* skip this wrapper *)
     |"CChars0" => (warning "bizarre rule in context float: CChars0"; c)
     |"CExpr0"  => c (* skip this wrapper *)
     |"CTypeSpec0" => c (* skip this wrapper *)
     |"CDeclr0" => c (* skip this wrapper *)
     |"CInitExpr0" => c (* skip this wrapper *)
     |"CDecl0" =>  error("Local declarations inside a C context are not supported in Clean")
     |"CCall0" => c (* skip this wrapper *)
     | str => error("unsupported expression with parse tag: "^str)) (* global catch all *)


fun lifted_term sigma_i term = Abs("\<sigma>", sigma_i, abstract_over (Free("\<sigma>", sigma_i), term))

fun conv_Cexpr_lifted_term  sigma_i A_env thy C_expr = 
    let val e::R = (C11_Ast_Lib.fold_cExpression (K I)
                               (convertExpr false sigma_i A_env thy) C_expr [])
    in  lifted_term sigma_i e end

(*** -------------- ***)

fun conv_cDerivedDeclarator_cSizeExpr_term (C_Ast.CArrDeclr0 (_,C_Ast.CArrSize0 (_,C_expr),_)) C_env thy = 
            SOME(hd((C11_Ast_Lib.fold_cExpression (K I)
                                 (convertExpr false dummyT C_env thy) C_expr [])))
   |conv_cDerivedDeclarator_cSizeExpr_term (C_Ast.CArrDeclr0 (_,C_Ast.CNoArrSize0 Z,_)) _ _ = NONE
   |conv_cDerivedDeclarator_cSizeExpr_term (_)  _ _ =  
            error("DeclarationSpec format not defined. [Clean restriction]")


end
end
\<close>

subsection\<open>C11 Statements to Clean Terms\<close>

ML\<open>

structure C11_Stmt_2_Clean =

struct

local open Clean_Term_interface C11_Expr_2_Clean HOLogic in

val start_term = Const("_BEGIN",dummyT)
val end_term = Const("_END",dummyT)


fun group tS = [end_term] @ tS @ [start_term] (* reverse order *)

fun regroup pre post = let val pre' = rev pre
                           val post' = rev post
                           fun chop_common_prefix([],S) = S
                              |chop_common_prefix(a::P,a'::P') = if a = a' then chop_common_prefix(P,P') 
                                                               else error"Stack regrouping error" 
                              |chop_common_prefix _ = error"Stack regrouping error"
                       in  group (rev(chop_common_prefix (pre', post'))) @ pre end 


(*fonction prenant en entrée une list de terms [t1, ..., Begin, b1, ..., bk, End, ..., tn]
et renvoie la liste [t1, ...,  un terme représentant le bloc b1; ... bk;, ..., tn]
si on a k = 0 : renvoie la term skip
*)

fun block_to_term (Const("_END",_)::Const("_BEGIN",_)::R) 
              = mk_skip_C dummyT ::R
   |block_to_term R = 
         let val _ = (writeln("block_to_term::"^ @{make_string } R))
             val (topS, restS) = chop_prefix (fn Const("_BEGIN",_) => false | _ => true) R
             val (Const("_END",_)::topS, Const("_BEGIN",_)::restS) = (topS, restS)
         in (foldl1 (uncurry mk_seq_C) (rev topS)) :: restS end


fun convertStmt verbose sigma_i nEenv thy 
           (a as { tag, sub_tag, args }:C11_Ast_Lib.node_content) 
           (b:  C_Ast.nodeInfo ) 
           (stack : term list) =
    ((if verbose then (writeln("tag:"^tag);print_node_info a b stack) else ());
    case tag of

     "CAssign0" => (case stack of
                      (rhs :: lhs ::  R) => 
                          ((let 
                               fun getLongId lhs  = (case lhs of
                                            Const(name, _) $ _ => name
                                          | _ $ _ $ Const(name, _) $ _ => name
                                          | Free (name, _) => name
                                          | Const ("List.nth", _) $ lhs_candidat $ _ => (getLongId lhs_candidat)
                                          | _ => error("(convertStmt) CAssign0 does not recognise term: "
                                                        ^(@{make_string} lhs)^"With stacK"^(@{make_string} stack)))
                               val long_id = getLongId lhs
                               val (id, lid) = extract_ids long_id sigma_i
                               fun is_id (C_AbsEnv.Identifier(id_name, _, _, _)) = id_name = id
                               val C_AbsEnv.Identifier(id, _, ty, cat) = 
                                         case List.find is_id nEenv of SOME x  => x
                                             | _ => error("id not found: "^ long_id)

                               fun get_base_type lhs ty = 
                                  case lhs of Const ("List.nth", typedef) $ lhs_part1 $ idx_term => 
                                                                       get_base_type lhs_part1 (dest_listTy ty)
                                                     | _ => ((if (is_listTy ty) then warning "Assigning list of elements to variable. This is not possible in C, however supported by Clean" else ());ty)
                               val tempvarn = "tmpvar"
                               val is_fun_assignment = (case rhs of  Const (@{const_name "Clean.call\<^sub>C"},_) $_ $_ => true
                                                                         | _ => false)
                               val rhs_old = rhs
                               val tempvart = (get_base_type lhs ty)
                               val rhs = (if is_fun_assignment then Free (tempvarn, tempvart) else rhs)
                               fun mk_list_type ty = Type(@{type_name "list"}, [ty]) (* This is from "isa_termstypes.ML" *)
                               fun mk_list_update_t ty = Const(@{const_name "List.list_update"}, (* This is from "isa_termstypes.ML" *)
                                                    mk_list_type ty --> natT -->
                                                                 ty --> mk_list_type ty)
                               fun transform_rhs_list_assignment lhs_part value ty= 
                                  case lhs_part of  Const ("List.nth", typedef) $ lhs_part1 $ idx_term => (
                                      let 
                                        
                                        val lst_update_t =  mk_list_update_t ty
                                        val updated = lst_update_t $ lhs_part1 $ idx_term $ value
                                      in
                                        transform_rhs_list_assignment lhs_part1 updated (listT ty)
                                      end
                                    )
                                  | _ => value

                               fun transform_lhs_for_rhs_transformation lhs_part final_term =
                                     case lhs_part of Const (@{const_name "nth"}, typedef) $ lhs_part1 $ idx_term => 
                                                                       Const (@{const_name "nth"}, typedef) $ (transform_lhs_for_rhs_transformation lhs_part1 final_term) $ idx_term
                                                     | _ => final_term

                               val access_term = case cat of  C_AbsEnv.Global  =>  (read_N_coerce thy id (sigma_i --> ty) $ Free("\<sigma>",sigma_i))
                                                              |_ =>  Const(@{const_name "comp"}, 
                                                                           (HOLogic.listT ty --> ty) 
                                                                           --> (sigma_i --> HOLogic.listT ty) 
                                                                           --> sigma_i --> ty) 
                                                                      $ Const(@{const_name "hd"}, HOLogic.listT ty --> ty) 
                                                                      $ read_N_coerce thy lid (sigma_i --> HOLogic.listT ty) 
                                                                      $ Free("\<sigma>",sigma_i)
                                              

                               val lhs_tmp = transform_lhs_for_rhs_transformation lhs access_term

                               val new_rhs = transform_rhs_list_assignment lhs_tmp rhs (get_base_type lhs ty)

                               val (id, lid) = (id ^ "_update", lid ^ "_update")
                               

                           in case cat of
                                C_AbsEnv.Global => (if is_fun_assignment then ( mk_seq_assign_C rhs_old (((mk_assign_global_C 
                                                            (read_N_coerce thy id 
                                                           ((ty --> ty) --> sigma_i --> sigma_i)))
                                                       (lifted_term sigma_i new_rhs))) tempvarn tempvart) 
                                                     else (
                                                        ((mk_assign_global_C 
                                                            (read_N_coerce thy id 
                                                           ((ty --> ty) --> sigma_i --> sigma_i)))
                                                       (lifted_term sigma_i new_rhs))))::R
                              | C_AbsEnv.Parameter(_) => error "assignment to parameter not allowed in Clean"
                              | C_AbsEnv.Local(_) => (if is_fun_assignment then (mk_seq_assign_C rhs_old (mk_assign_local_C 
                                                       (read_N_coerce thy lid 
                                                           ((listT ty --> listT ty) --> sigma_i --> sigma_i))
                                                       (lifted_term sigma_i new_rhs) ) tempvarn tempvart)
                                                      else ((mk_assign_local_C 
                                                       (read_N_coerce thy lid 
                                                           ((listT ty --> listT ty) --> sigma_i --> sigma_i))
                                                       (lifted_term sigma_i new_rhs) )))::R
                              | s => error("(convertStmt) CAssign0 with cat " 
                                            ^ @{make_string} s ^ " is unrecognised")
                           end))
                      |_ => raise WrongFormat("assign"))
     (*statements*)
(*for return, skip and break, we have makers except that they need types and terms that i didn't 
understand so it's unfinished here*)
     |"CReturn0" => let val _ = writeln("TRACE 1.2")
                        val rhs = hd stack
                        val res_upd = mk_result_update thy sigma_i
                    in (mk_return_C res_upd (lifted_term sigma_i rhs)) :: (tl stack) end
     |"CSkip0"  => (mk_skip_C sigma_i)::stack
     |"CBreak0" => (mk_break sigma_i)::stack
(*for statements with a body, we need to create a sequence. if statements or expressions
are in sequence, they will be in the list c between Const("begin", _) and Const("end", _).
so we use the block_to_term function which group all the terms already translate between begin and end,
and use the mk_seq_C functions to get only 1 term at the end. It delete begin and end aswell.*)
     |"CCompound0" => block_to_term stack
(*In C11, we have to types of if : if(...){...} and if(...){...} else{...}. but in
Clean, we must use if then else, so we isolate both cases, and if needed, we encode if(...){...} ans 
if ... then ... else skip*)
     | "CBlockStmt0" => stack
     | "CBlockDecl0" => stack
     | "CNestedFunDef0" =>  error"Nested Function Declarations not allowed in Clean"
     | "CIf0" =>   (case stack of  
                       (a::b::cond::R) => mk_if_C (lifted_term sigma_i cond) b a :: R
                    |  (a::cond::R) => (mk_if_C (lifted_term sigma_i cond) 
                                                (a)
                                                (mk_skip_C sigma_i)::R)
                    |  _    => raise WrongFormat("if")
                   )
     |"CWhile0" => (case stack of
                       (a::b::R) => (mk_while_C  (lifted_term sigma_i b)  a) :: R
                      |(a::R)    => (mk_while_C  (lifted_term sigma_i a)  
                                                 (mk_skip_C dummyT)) :: R  (* really dummyT *)
                      |_ => raise WrongFormat("while")
                   )
(*There is no For operator in Clean, so we have to translate it as a while :
for(ini, cond, evol){body} is translated as ini; while(cond){body; evol;}*)
     |"CFor0" =>   (case stack of
                        (body::pace::cond::init::R) => (let val C' = mk_while_C
                                                                       (lifted_term sigma_i cond)
                                                                       (mk_seq_C body pace)
                                                        in   ((mk_seq_C init C'))::R end)
                    |_ => raise WrongFormat("for"))
     | "CCall0" => (let fun extract_fun_args (t :: R) args =
                            case t of
                            (* very bad way of checking if term represents a function *)
                               Const(id, ty) => if not (firstype_of ty = sigma_i) 
                                                then (args, Const(id, ty), R) 
                                                else extract_fun_args R (Const(id, ty) :: args)
                            | arg => extract_fun_args R (arg :: args)
                        val (args, f, R) = extract_fun_args stack []
                        val fun_args_term = mk_tuple args
                       in mk_call_C f (lifted_term sigma_i fun_args_term) :: R end)
     | _ => convertExpr verbose sigma_i nEenv thy  a b stack )

end

(*** -------------- ***)

end
\<close>

subsection\<open>C11 Translation Units to Clean Terms\<close>

ML\<open>

structure C11_Unit_2_Clean =
struct 

local open HOLogic in

fun convertCUnit verbose sigma_i env thy
           (a as { tag, sub_tag, args }:C11_Ast_Lib.node_content) 
           (b:  C_Ast.nodeInfo ) 
           (c : term list) =
    ((if verbose then print_node_info a b c else ());
    case tag of

(*types et declarations*)
(*here is where I have troubles to continue due to my understanding of ISabelle/C and Isabelle/Clean*)
      "CTypeSpec0" => (case sub_tag of
                          "CIntType0" => (Const("int", intT))::c
                       |  "CVoidType0" => (Const("void", unitT))::c
                       |  "CFloatType0" => (Const("float", realT))::c
                       |  s => raise UnknownTyp(s)
                      )
     |"CFunDef0" =>   let 
                        val body = hd c
                        val args = List.take (tl c, (length c - 2))
                        val name = List.last c
                      in c end
(*others*)
     |"Begin" => (Const("Begin", dummyT))::c (* obsolete I believe. bu *)
     |"End" => (Const("End", dummyT))::c (* obsolete I believe. bu *)
     | s =>  (c)
)

end
end

\<close> 
end