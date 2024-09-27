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


(*renvoie le type du premier attribut d'une fonction, ou le type d'une constante*)
fun firstype_of (Type(_, [x])) = x | firstype_of (Type(_, x::_)) = x
   |firstype_of t = t

fun lastype_of (Type(_, [x])) = x | lastype_of (Type(_, [_ , y])) = y 

(* Creates a result_update_term for the local state *)
fun mk_result_update thy sigma_i=
  let
   val Type(ty_name,_) = sigma_i
   val s = ty_name |> String.tokens (fn x => x =  #".") |> tl |> hd
   val s' = String.substring(s, 0, size s - size "_scheme")^".result_value_update"
  in Syntax.read_term_global thy s' end;


fun read_N_coerce thy name ty = 
       (* a very dirty hack ... but reconstructs the true \<open>const_name\<close> 
          along the subtype hierarchy, but coerces it to the current sigma*)
       let val s = drop_dark_matter(Syntax.string_of_typ_global thy ty)
           val str = name ^ " :: " ^ s 
       in  Syntax.read_term_global thy str end

fun read_N_coerce_global thy name =
       (*this function is necessary, to ensure that a global variable is selected, in case
         a local variable is defined later (as later vars would get selected by default)*)
       let 
           val consts = Sign.consts_of thy
           fun filter_by_shortname (n, _) =
             (case Long_Name.explode n of
                [_, middle, base] => base = name andalso (String.substring (middle,0,6) = "global")
              | _ => false) 
           val longnames =  List.filter filter_by_shortname (#constants (Consts.dest consts))
           val longname = (fst o hd) longnames
       in  read_N_coerce thy longname end

fun get_update_fun thy name = read_N_coerce thy (name^"_update")
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

fun is_call a = case a of 
              Const (@{const_name "Clean.call\<^sub>C"},_) $_ $_ => true
              |_ => false

fun convertExpr verbose (sigma_i: typ) env thy function_name _
           (a as { tag, sub_tag, args }:C11_Ast_Lib.node_content) 
           (b:  C_Ast.nodeInfo )   
           (c : term list) =
    ((if verbose then print_node_info a b c else ());
    let fun get_most_general_type t1 t2 = 
                              if t1 = natT andalso t2=natT then natT else 
                              if (t1 = natT orelse t1 = intT) andalso (t2=natT orelse t2=intT) then intT else
                              if t1 <> natT andalso t1<>intT then t1 else t2 (*this should be the fallback for rational numbers*)
                         fun get_ring_op_type t1 t2 =
                            if get_most_general_type t1 t2 = natT then intT else get_most_general_type t1 t2
    in 
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
                                              (*dangerous. will work only for the local case *)
                    in case cat of
                        C_AbsEnv.Global => read_N_coerce_global thy id (sigma_i --> ty) $ Free("\<sigma>",sigma_i)::c
                      | C_AbsEnv.Local(_) => Const(@{const_name "comp"}, 
                                                   (HOLogic.listT ty --> ty) 
                                                   --> (sigma_i --> HOLogic.listT ty) 
                                                   --> sigma_i --> ty) 
                                              $ Const(@{const_name "hd"}, HOLogic.listT ty --> ty) 
                                              $ read_N_coerce thy id (sigma_i --> HOLogic.listT ty) 
                                              $ Free("\<sigma>",sigma_i) :: c
                      | C_AbsEnv.Parameter(_) => Free (id, ty) :: c
                      | C_AbsEnv.FunctionCategory(C_AbsEnv.MutuallyRecursive(_), _) =>
                                error("Mutual recursion is not supported in Clean")
                      | C_AbsEnv.FunctionCategory(_, _) =>
                            let fun get_call_const id = Syntax.read_term_global thy id
                                (* There is no term corresponding to the function. Hence skip the 
                                   initialization of the type and infer it from the call args (see CCall0)*)
                                fun get_rec_call_ident id= Free(id, 
                                            (TVar (("'a", 0), [])) --> sigma_i --> (Type (@{type_name "option"}, [mk_tupleT [ty, sigma_i]])))
                            in (if function_name = id then get_rec_call_ident id else get_call_const id) :: c end
                    end)
     |"Vars0" => c
     |"CVar0" => c
(*expressions*)
(*At this point, what we do for binary or unary epressions is simple thanks to the makers. *)
     (*binary operations*)
     |"CBinary0" => (case (drop_dark_matter sub_tag, c) of
                      (*arithmetic operations*) 
                      ("CAddOp0",b::a::R) => let val ty = get_most_general_type (fastype_of a) (fastype_of b) in (Const(@{const_name "plus"}, ty --> ty --> ty) $ a $ b :: R) end
                    | ("CMulOp0",b::a::R) => let val ty = get_most_general_type (fastype_of a) (fastype_of b) in (Const(@{const_name "times"}, ty --> ty --> ty) $ a $ b :: R) end
                    | ("CDivOp0",b::a::R) => let val ty = get_ring_op_type (fastype_of a) (fastype_of b) in (Const(@{const_name "divide"}, ty --> ty --> ty) $ a $ b :: R) end
                    | ("CSubOp0",b::a::R) => let val ty = get_ring_op_type (fastype_of a) (fastype_of b) in (Const(@{const_name "minus"}, ty --> ty --> ty) $ a $ b :: R) end
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
                    | ("CLeOp0", b::a::R) => let val ty =get_most_general_type (fastype_of a) (fastype_of b)
                                             in (Const(@{const_name "less"}, 
                                                    ty --> ty --> boolT) 
                                             $ a $ b :: R) end 
                    | ("CGrOp0", b::a::R) => let val ty =get_most_general_type (fastype_of a) (fastype_of b)
                                             in (Const(@{const_name "less"}, 
                                                    ty --> ty --> boolT) 
                                             $ b $ a :: R) end
                    | ("CLeqOp0", b::a::R) => let val ty =get_most_general_type (fastype_of a) (fastype_of b)
                                              in (Const(@{const_name "less_eq"}, 
                                                     ty --> ty --> boolT) 
                                              $ a $ b :: R) end
                    | ("CGeqOp0", b::a::R) => let val ty =get_most_general_type (fastype_of a) (fastype_of b)
                                              in (Const(@{const_name "less_eq"}, 
                                                     ty -->  ty --> boolT) 
                                              $ b $ a :: R)end
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
                    in  (mk_number (if n>=0 then natT else intT) n)::c end
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
      (*this is a very dirty trick: when declaring variables "int a,b=3,c,d=4;", the accesses to a and c lie
        on the stack, polluting it. All non-assignments are thus removed, up until this item is met on the stack*)
     |"CTypeSpec0" => ((Free ("--startofdeclarations--",@{typ unit}))::c)
     |"CDeclr0" => c
     |"CDecl0" =>  let  fun is_assignment ((Const (@{const_name "assign_local"},_))$_$_) = true
                           |is_assignment ((Const (@{const_name "assign_global"},_))$_$_) = true
                           |is_assignment  _ = false
                        fun remove_dead_idents [] = []
                           |remove_dead_idents (Free("--startofdeclarations--",_)::R) = R
                           |remove_dead_idents (head::R) = if is_assignment head then (head::remove_dead_idents R) 
                                      else remove_dead_idents R
                   in
                      remove_dead_idents c
                   end
     |"CCall0" => c (* skip this wrapper *)
     |"CNoArrSize0" => c
     |"CArrDeclr0" => c
     | str => error("unsupported expression with parse tag: "^str^"and subtag: "^sub_tag)
end) (* global catch all *)


fun lifted_term sigma_i term = Abs("\<sigma>", sigma_i, abstract_over (Free("\<sigma>", sigma_i), term))

fun conv_Cexpr_lifted_term  sigma_i A_env thy function_name get_loop_annotations C_expr = 
    let val e::R = (C11_Ast_Lib.fold_cExpression (K I)
                               (convertExpr false sigma_i A_env thy function_name get_loop_annotations) C_expr [])
    in  lifted_term sigma_i e end

(*** -------------- ***)

fun conv_cDerivedDeclarator_cSizeExpr_term (C_Ast.CArrDeclr0 (_,C_Ast.CArrSize0 (_,C_expr),_)) C_env thy function_name get_loop_annotations= 
            SOME(hd((C11_Ast_Lib.fold_cExpression (K I)
                                 (convertExpr false dummyT C_env thy function_name get_loop_annotations) C_expr [])))
   |conv_cDerivedDeclarator_cSizeExpr_term (C_Ast.CArrDeclr0 (_,C_Ast.CNoArrSize0 Z,_)) _ _ _ _= NONE
   |conv_cDerivedDeclarator_cSizeExpr_term (_)  _ _ _ _=  
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
         let val (topS, restS) = chop_prefix (fn Const("_BEGIN",_) => false | _ => true) R
             val (Const("_END",_)::topS, Const("_BEGIN",_)::restS) = (topS, restS)
         in (foldl1 (uncurry mk_seq_C) (rev topS)) :: restS end


fun convertStmt verbose sigma_i nEenv thy function_name get_loop_annotations
           (a as { tag, sub_tag, args }:C11_Ast_Lib.node_content) 
           (b:  C_Ast.nodeInfo ) 
           (stack : term list) =
    
    let fun handle_assign stack = (case stack of
                      (rhs :: lhs ::  R) => 
                          ((let
                               fun getLongId lhs  = (case lhs of
                                            Const(name, _) $ _ => name
                                          | _ $ _ $ Const(name, _) $ _ => name
                                          | Free (name, _) => name
                                          | Const ("List.nth", _) $ lhs_candidat $ _ => (getLongId lhs_candidat)
                                          | _ => error("(convertStmt) CAssign0 does not recognise term: "
                                                        ^(@{make_string} lhs)^"With stacK"^(@{make_string} stack)))
                               val ident_id = getLongId lhs

                               val C_AbsEnv.Identifier(_, _, ty, cat) = let
                                    fun is_id (C_AbsEnv.Identifier(id_name, _, _, _)) = id_name = Long_Name.base_name ident_id in
                                         case List.find is_id nEenv of SOME x  => x
                                             | _ => error("id not found: "^ ident_id) end
                               val (update_func_ty, mk_assign) = case cat of C_AbsEnv.Global => (((ty --> ty) --> sigma_i --> sigma_i), mk_assign_global_C)
                                                               |C_AbsEnv.Local _ => (((listT ty --> listT ty) --> sigma_i --> sigma_i), mk_assign_local_C)
                                                               | _ => error ("Assignment to "^ident_id^" not possible (is it a parameter?)")
                               val update_func = get_update_fun thy ident_id update_func_ty
                               fun get_base_type lhs ty = 
                                  case lhs of Const ("List.nth", _) $ lhs_part1 $ _ => 
                                                                       get_base_type lhs_part1 (dest_listTy ty)
                                                     | _ => ((if (is_listTy ty) then warning "Assigning list of elements to variable. This is not possible in C, however supported by Clean" else ());ty)
                               val tempvarn = "tmpvar"
                               val tempvart = (get_base_type lhs ty)
                               val is_fun_assignment = (case rhs of  Const (@{const_name "Clean.call\<^sub>C"},_) $_ $_ => true
                                                                         | _ => false)
                               (*Here comes the array part. Since only entire "rows" of arrays can be replaced,
                                 for the expression A[1][2] = b, the right hand side of the CLEAN-statement has
                                 to include parts of the LHS, which makes this transformation rather ugly, especially
                                 in combination with function calls.
                                 Based on the LHS, the function get_array_assignment provides, for the above example,
                                 a function: 
                                 \<lambda>rhs. A[1:= (A!1 [2:= rhs])
                                  *)
                               fun mk_list_update_t ty = Const(@{const_name "List.list_update"}, (* This is from "isa_termstypes.ML" *)
                                                    listT ty --> natT --> ty --> listT ty)
                               fun transform_rhs_list_assignment lhs_part ty value= 
                                  case lhs_part of  Const ("List.nth", _) $ lhs_part1 $ idx_term => (
                                      let 
                                        val lst_update_t =  mk_list_update_t ty
                                        val updated = lst_update_t $ lhs_part1 $ idx_term $ value
                                      in
                                        transform_rhs_list_assignment lhs_part1 (listT ty) updated 
                                      end
                                    )
                                  | _ => value                                              

                               val get_array_assignment = transform_rhs_list_assignment lhs (get_base_type lhs ty) 


                               val assignment =if is_fun_assignment then ( mk_seq_assign_C 
                                                            rhs 
                                                            (((mk_assign update_func) 
                                                              (lifted_term sigma_i (get_array_assignment (Free (tempvarn,tempvart)))))) 
                                                            tempvarn 
                                                            tempvart) 
                                                     else (   
                                                        ((mk_assign 
                                                            update_func)
                                                       (lifted_term sigma_i (get_array_assignment rhs))))
                                val inferred_assignment = Syntax.check_term (Proof_Context.init_global thy) assignment
                                in assignment::R
                           end))
                      |_ => raise WrongFormat("assign"))

     in ((if verbose then (writeln("tag:"^tag);print_node_info a b stack) else ());
    if tag="CBinary0" andalso
       case stack of (head::_) => is_call head |_=>false 
          then error ("Function call only allowed on RHS of assignment. Tag: "^tag)  else ();
    case tag of
     "CAssign0" => handle_assign stack
    |"CInitExpr0" => handle_assign stack
     (*statements*)
(*for return, skip and break, we have makers except that they need types and terms that i didn't 
understand so it's unfinished here*)
     |"CReturn0" => let
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
     | "CIf0" =>   (case stack of (*checking based on how many elements are on the stack is wrong.
                                    instead check the type of the condition. It must be a value (i.e. no function)*)
                    (a::b::c::R) => (case fastype_of b of Type ("fun",_)=> mk_if_C (lifted_term sigma_i c) b a :: R (*b is not the condition*)
                                                          | _ => (mk_if_C (lifted_term sigma_i b) (*b is the cond no else*)
                                                                 (a)
                                                                 (mk_skip_C sigma_i)::R))
                    |  (a::cond::R) => (mk_if_C (lifted_term sigma_i cond) 
                                                (a)
                                                (mk_skip_C sigma_i)::R)
                    |  _    => raise WrongFormat("if")
                   )
     |"CWhile0" => let val pos = (case b of C_Ast.OnlyPos0 (pos,_) => pos
                              |C_Ast.NodeInfo0 (pos,_,_) => pos)
                       val (get_inv, get_measure) = get_loop_annotations pos
                       val invariant_lifted =get_inv 
                                  |> Option.map 
                                      (fn get_inv=>(Syntax.check_term (Proof_Context.init_global thy) ((lifted_term sigma_i) (get_inv (Context.Theory thy)))))
                       val measure_lifted =get_measure 
                                  |> Option.map 
                                      (fn get_measure => Syntax.check_term (Proof_Context.init_global thy) ((lifted_term sigma_i) ( get_measure (Context.Theory thy))))
                       val mk_while_func = case (invariant_lifted,measure_lifted) 
                            of (NONE,NONE) => mk_while_C
                              |(SOME inv, SOME measure)=>mk_while_anno_C inv  measure (*Note the coercion to nat!*)
                              |(SOME inv, NONE)=>mk_while_anno_C inv (lifted_term sigma_i @{term "1::nat"})
                              |(NONE, SOME measure)=>mk_while_anno_C (lifted_term sigma_i @{term "True::bool"})  measure
                                                                 
                      in (case stack of
                       (a::b::R) => (mk_while_func  (lifted_term sigma_i b)  a) :: R
                      |(a::R)    => (mk_while_func  (lifted_term sigma_i a)  
                                                 (mk_skip_C dummyT)) :: R  (* really dummyT *)
                      |_ => raise WrongFormat("while")
                   ) end
(*There is no For operator in Clean, so we have to translate it as a while :
for(ini, cond, evol){body} is translated as ini; while(cond){body; evol;}*)
     |"CFor0" =>   let val pos = (case b of C_Ast.OnlyPos0 (pos,_) => pos
                              |C_Ast.NodeInfo0 (pos,_,_) => pos)
                       (*duplicate code from while*)
                       val (get_inv, get_measure) = get_loop_annotations pos
                       val invariant_lifted =get_inv |> Option.map (fn get_inv=> (lifted_term sigma_i) (get_inv (Context.Theory thy)))
                       val measure_lifted =get_measure |> Option.map (fn get_measure => (lifted_term sigma_i) ( get_measure (Context.Theory thy)))
                       val mk_while_func = case (invariant_lifted,measure_lifted) 
                            of (NONE,NONE) => mk_while_C
                              |(SOME inv, SOME measure)=>mk_while_anno_C inv measure
                              |(SOME inv, NONE)=>mk_while_anno_C inv (lifted_term sigma_i @{term "1::nat"})
                              |(NONE, SOME measure)=>mk_while_anno_C (lifted_term sigma_i @{term "True::bool"}) measure
                      in (case stack of
                        (body::pace::cond::init::R) => (let val C' = mk_while_func
                                                                       (lifted_term sigma_i cond)
                                                                       (mk_seq_C body pace)
                                                        in   ((mk_seq_C init C'))::R end)
                        |_ => raise WrongFormat("for")) end
     | "CCall0" => (let fun extract_fun_args (t :: R) args =
                            (case t of
                            (* very bad way of checking if term represents a function *)
                               Const(id, ty) => if not (firstype_of ty = sigma_i) 
                                                then (args, Const(id, ty), R) 
                                                else extract_fun_args R (Const(id, ty) :: args)
                             |  Free(id, ty) => if id = function_name (*recursive call*)
                                                then (args, Free(id, ty), R) 
                                                else extract_fun_args R (Free(id, ty) :: args)
                             | arg => extract_fun_args R (arg :: args))
                            |extract_fun_args [] _ = error ("\"CCall0\": couldnt find function in stack: "^(@{make_string} stack))
                        val (args, f, R) = extract_fun_args stack []
                        val ret_ty = case fastype_of f of Type (_, [_, (*args \<rightarrow>*)
                                                          Type (_, [_, (*sigma \<rightarrow>*)
                                                          Type (_, [ (*'a option*)
                                                          Type(_, [ret_ty, _])])])]) => ret_ty (* (ret_type, sigma)*)
                                                          | _ => error ("function type has wrong format: "^(@{make_string} (fastype_of f)))

                        val new_args_ty = mk_tupleT (List.map fastype_of args)
                        val new_ty = new_args_ty --> sigma_i --> (Type (@{type_name "option"},[Type (@{type_name "prod"}, [ret_ty,sigma_i])]))

                        fun swap_ty (Const (name, _)) n_ty = Const (name, n_ty)
                           |swap_ty (Free (name, _)) n_ty = Free (name, n_ty)
                           |swap_ty _ _ = error "unexpected term at swap_ty"

                        val f_new = swap_ty f new_ty
                        val fun_args_term = mk_tuple args
                       in mk_call_C f_new (lifted_term sigma_i fun_args_term) :: R end)
     | _ => convertExpr verbose sigma_i nEenv thy function_name get_loop_annotations a b stack )

end

(*** -------------- ***)

end
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

fun get_loop_positions (a as { tag, sub_tag, args }:C11_Ast_Lib.node_content) 
           (b:  C_Ast.nodeInfo )   
           (c : C_Ast.positiona list) =
      case tag of
        "CWhile0" => (case b of C_Ast.OnlyPos0 (pos,_) => pos::c
                              |C_Ast.NodeInfo0 (pos,_,_) => pos::c)
        |"CFor0" => (case b of C_Ast.OnlyPos0 (pos,_) => pos::c
                              |C_Ast.NodeInfo0 (pos,_,_) => pos::c)
        | _ => c

end
end

\<close> 
end