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
          "HOL.Real"
          "Clean.Clean"
          "CleanCoder2"
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

fun mk_glob_upd_raw name ty sigma_i = 
  Const(name^"_update", (ty --> ty) --> sigma_i --> sigma_i)

(*créé un term upd global*)
fun mk_glob_upd name rhs = 
  let val ty   = fastype_of rhs
      val ty'  = lastype_of ty (* ty' should be for example HOLogic.intT *)
      val sigma_i = firstype_of ty (* sigma_i should be 'a global_state_scheme *)
  in mk_glob_upd_raw name ty' sigma_i
  end

fun mk_loc_upd_ident name ty sigma_i = 
  mk_glob_upd_raw name (HOLogic.listT ty) sigma_i

(*créé un term upd local*)
fun mk_loc_upd name rhs = 
  let val ty   = fastype_of rhs
      val ty'  = lastype_of ty (* ty' should be for example HOLogic.intT *)
      val sigma_i = firstype_of ty (* sigma_i should be 'a local_state_scheme *)
  in mk_loc_upd_ident name ty' sigma_i
  end

fun mk_namespace thy =
  let val Type(str_local_state_scheme, _) = StateMgt_core.get_state_type_global thy;
      val str_local_state = String.substring (str_local_state_scheme, 0, 
                             String.size str_local_state_scheme - (String.size "_scheme"))
  in Path.explode str_local_state end

(* Creates a result_update_term for the local state *)
fun mk_result_update thy ctxt =
  let val namespace = mk_namespace thy
      val path_local_state_result_value = Path.ext StateMgt.result_name namespace;
      val str_local_state_result_value = Path.implode path_local_state_result_value;
      val str_local_state_result_value_update = str_local_state_result_value ^ "_update";
  in Syntax.read_term ctxt str_local_state_result_value_update end;

fun extract_identifier_from_id thy identifiers id =
  let  val ns = mk_namespace thy |> Path.implode
       val id = if String.isPrefix ns id then String.extract (id, (String.size ns) + 1, NONE) else id
       val SOME(identifier) = List.find (fn C_AbsEnv.Identifier(id_name, _, _, _) => id_name = id) identifiers
  in identifier end

(*fonction de traduction principale :*)

(*
verbose : boolean (to do some printing and help to debug)
sigma_i : typ (actual type)
env : context (unuse right now but will probably be usefull)
thy : theory (the actual theory)
a, b, c : those values are from the parser
*)

open HOLogic;

fun convertCType2HOLType X = ()

(*** Duplicate code ***)

fun convertExpr_raw verbose sigma_i env thy
           (a as { tag, sub_tag, args }:C11_Ast_Lib.node_content) 
           (b:  C_Ast.nodeInfo ) 
           (c : term list) =
    ((if verbose then print_node_info a b c else ());
    case tag of
(*variables*)
(*here, we get the full name of the variable, then we return the term well named and typed.
Bound 0 is usefull for the statements, and can easily be deleted if necessary*)
      "Ident0" =>  (let val Free(id,_) = (node_content_2_free a)
                        val (long_id, ty) =  case Syntax.read_term_global thy id of
                                               Const(long_id, Type("fun", [_,ty])) => (long_id, ty)
                                             | Const(txt,_) => error("constant out of context:"^txt)
                                             | expr => error("illformed expression: " ^ @{make_string} expr)
                    in  (Const(long_id,sigma_i --> ty) $ Bound 0)::c
                    end)
                    (* Consider 3 cases: local, param, global *)
                    (* name = get_var_string0
                       case ident_lookup() of
                         local(typ) \<Rightarrow> Const(Func.comp, dummyT) $ Const(List.hd, typ) $ Const(selector_func name)
                         global(typ) \<Rightarrow> Const(name, typ)
                         param(typ) \<Rightarrow> Free(name, typ)
      

                       Term.abstract_over: term (c $ Free(y, ty)) \<Rightarrow> (c $ Bound 1)
                    *)
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
                                   $ mk_number realT ((String.size s'') - 1)))) 
                         ::c
                   end
     |"CFloatConst0"=> (c) (* skip this wrapper *)
     |"CChars0" => (warning "bizarre rule in context float: CChars0"; c)
     |"CExpr0"  => c (* skip this wrapper *)

     | str => error("unsupported expression with parse tag: "^str)) (* global catch all *)

(* Copied from CleanCoder2... *)
fun node_content_parser (x : C11_Ast_Lib.node_content) =
  let fun drop_dark_matter x =(XML.content_of o YXML.parse_body) x 
      val  C11_Ast_Lib.data_string a_markup = hd(#args(x))
      val id = hd(tl(String.tokens (fn x => x = #"\"")(drop_dark_matter a_markup)))
    in id end  (* no type inference *);

fun convertExpr_raw_ident verbose (sigma_i: typ) env thy ctxt identifiers
           (a as { tag, sub_tag, args }:C11_Ast_Lib.node_content) 
           (b:  C_Ast.nodeInfo )   
           (c : term list) =
    ((if verbose then print_node_info a b c else ());
    case tag of
(*variables*)
(*here, we get the full name of the variable, then we return the term well named and typed.
Bound 0 is usefull for the statements, and can easily be deleted if necessary*)
      "Ident0" =>  (let val id = node_content_parser a
                        val identifier = case List.find (fn C_AbsEnv.Identifier(id_name, _, _, _) => id_name = id) identifiers of
                                                SOME(identifier) => identifier
                                              | NONE => error("(convertExpr_raw_ident) identifier " ^ id ^ " not recognised")
                                                        (* This is another way to parse the list of identifiers...
                                                          case Syntax.read_term_global thy id of
                                                          Const(_, long_ty) => (case firstype_of long_ty of
                                                                                 sigma_i => C_Scanner.Identifier(id, Position.none, firstype_of long_ty, C_Scanner.Global)
                                                                               | _ =>  C_Scanner.Identifier(id, Position.none, @{typ "unit"}, C_Scanner.FunctionCategory(C_Scanner.Final, NONE)))
                                                        | Free(long_id, _) => error("(convertExpr_raw_ident) identifier " ^ long_id ^ " not recognised")
                                                        *)
                        val C_AbsEnv.Identifier(_, _, ty, cat) = identifier
                        val long_id = Path.ext id (mk_namespace thy) |> Path.implode
                    in case cat of
                        C_AbsEnv.Global => Const(long_id, sigma_i --> ty) $ Bound 0 :: c
                      | C_AbsEnv.Local(_) => Const(@{const_name "comp"}, (HOLogic.listT ty --> ty) --> (sigma_i --> HOLogic.listT ty) --> sigma_i --> ty) $ Const(@{const_name "hd"}, HOLogic.listT ty --> ty) $ Const(long_id, sigma_i --> HOLogic.listT ty) $ Bound 0 :: c
                      | C_AbsEnv.Parameter(_) => Free (id, ty) :: c
                      | C_AbsEnv.FunctionCategory(C_AbsEnv.MutuallyRecursive(_), _) =>
                        error("Mutual recursion is not supported in Clean")
                      | C_AbsEnv.FunctionCategory(C_AbsEnv.Final, _) => 
                            let val Const(id, ty) = Syntax.read_term_global thy id
                                val args = firstype_of ty
                                val mty = StateMgt_core.MON_SE_T @{typ "unit"} sigma_i
                            in Const(id, args --> mty) :: c end
                              
                      | c => error("(convertExpr_raw_ident) unrecognised category : " ^ @{make_string} c)
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
                                   $ mk_number realT ((String.size s'') - 1)))) 
                         ::c
                   end
     |"CFloatConst0"=> (c) (* skip this wrapper *)
     |"CChars0" => (warning "bizarre rule in context float: CChars0"; c)
     |"CExpr0"  => c (* skip this wrapper *)
     |"CTypeSpec0" => c (* skip this wrapper *)
     |"CDeclr0" => c (* skip this wrapper *)
     |"CInitExpr0" => c (* skip this wrapper *)
     |"CDecl0" =>  error("Local declarations inside a C context are not supported in Clean")
     |"CCall0" => c (* skip this wrapper *)
     | str => error("unsupported expression with parse tag: "^str)) (* global catch all *)

(*** -------------- ***)

fun conv_Cexpr_term C_env sigma_i thy C_expr = 
    Abs("\<sigma>", sigma_i, hd((C11_Ast_Lib.fold_cExpression (K I)
                               (convertExpr_raw false sigma_i C_env thy) C_expr [])))
    (* Better: abstract_over (Free(\<sigma>, sigma_i)) ??? *)
\<close>
ML\<open>
local open Clean_Term_interface in

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

(*
fun block_to_term l =
  let
    val _ = (writeln("block_to_term::"^ @{make_string } l))
    fun aux1 l acc = case l of    (*créé la list [b1, ..., bk, End, ..., tn]*)
          [] => ([mk_skip_C dummyT],[]) (* ??? *)
          |x::s => if x = Const("Begin", dummyT) then (acc, s) else aux1 s (x::acc)

    val (pre, rest) = aux1 l []

    fun aux2 l n acc = case (l, n) of (*créé la liste [bk, ..., b1]*)
          ([], _) => raise EmptyList
          |(Const("End", _)::s, 0) => (acc, s)
          |(Const("End", _)::s, n) => aux2 s (n - 1) (Const("End", dummyT)::acc)
          |(Const("Begin", _)::s, n) => aux2 s (n + 1) (Const("Begin", dummyT)::acc) 
          |(x::s, n) => aux2 s n (x::acc)

    val (core, suff) = aux2 rest 0 []
  
    fun aux3 l = case l of (*créé le term Block $ b1 $ ... $ bk si k \<ge> 1, Skip sinon*)
            [] => mk_skip_C dummyT
          | [x] => x
          | x::s => (let  val C' = aux3 s
                     in  (mk_seq_C x C') $ x $ C' end)
  in (List.rev pre) @ (aux3 (List.rev core)) :: suff
  end
*)

(*** Duplicate code ***)

fun convertStmt_raw verbose sigma_i env thy
           (a as { tag, sub_tag, args }:C11_Ast_Lib.node_content) 
           (b:  C_Ast.nodeInfo ) 
           (stack : term list) =
    ((if verbose then (writeln("tag:"^tag);print_node_info a b stack) else ());
    case tag of

(*for the assignations, we only consider global variables for now, and we use the maker*)
     "CAssign0" => (case stack of
                      (a::b::R) => (let val Const(name, t) $ _ = b
                                        val state_scheme_typ = firstype_of t
                                    in  (mk_assign_global_C 
                                            (mk_glob_upd name (Const(name, t))) 
                                            (Abs("\<sigma>", state_scheme_typ, a)) )::R 
                                    end)
                      |_ => raise WrongFormat("assign"))
     (*statements*)
(*for return, skip and break, we have makers except that they need types and terms that i didn't 
understand so it's unfinished here*)
     |"CReturn0" => (let  val rhs = hd stack
                     in   (mk_return_C (Const("temp", dummyT))  (Abs("\<sigma>", dummyT, rhs)))
                          ::(tl stack)
                     end)
     |"CSkip0" => (mk_skip_C sigma_i)::stack
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
     | "CBlockDecl0" => error"Nested Blocks not allowed in Clean"
     | "CNestedFunDef0" =>  error"Nested Function Declarations not allowed in Clean"
     | "CIf0" =>   (case stack of  
                       (a::b::cond::R) => mk_if_C  (Abs("\<sigma>", sigma_i --> boolT, cond)) b  a::R
                    |  (a::cond::R) => (mk_if_C (Abs("\<sigma>", sigma_i --> boolT, cond)) 
                                                (a)
                                                (mk_skip_C sigma_i)::R)
                    |_ => raise WrongFormat("if")
                   )
     |"CWhile0" => (case stack of
                       (a::b::R) => (mk_while_C  (Abs("\<sigma>", sigma_i, b))  a)::R
                      |(a::R)    => (mk_while_C  (Abs("\<sigma>", sigma_i, a))  
                                                 (mk_skip_C dummyT))
                                    ::R
                      |_ => raise WrongFormat("while")
                   )
(*There is no For operator in Clean, so we have to translate it as a while :
for(ini, cond, evol){body} is translated as ini; while(cond){body; evol;}*)
     |"CFor0" =>   (case stack of
                        (body::pace::cond::init::R) => (let val C' = mk_while_C
                                                                       (Abs("\<sigma>", sigma_i,cond))
                                                                       (mk_seq_C body pace)
                                                        in   ((mk_seq_C init C'))::R end)
                    |_ => raise WrongFormat("for"))
     | _ => convertExpr_raw verbose sigma_i env thy a b stack )

fun convertStmt_raw_ident verbose sigma_i env thy ctxt identifiers
           (a as { tag, sub_tag, args }:C11_Ast_Lib.node_content) 
           (b:  C_Ast.nodeInfo ) 
           (stack : term list) =
    ((if verbose then (writeln("tag:"^tag);print_node_info a b stack) else ());
    case tag of

     "CAssign0" => (case stack of
                      (first :: second ::  R) => 
                          (let val id = (case second of
                                            Const(name, _) $ _ => name
                                          | _ $ _ $ Const(name, _) $ _ => name
                                          | Free (name, _) => name
                                          | _ => error("(convertStmt_raw_ident) CAssign0 does not recognise term: "^(@{make_string} second)))
                               val C_AbsEnv.Identifier(id, _, ty, cat) = extract_identifier_from_id thy identifiers id
                               val long_id = Path.ext id (mk_namespace thy) |> Path.implode
                           in case cat of
                                C_AbsEnv.Global => (mk_assign_global_C 
                                            (mk_glob_upd_raw long_id ty sigma_i)
                                            (Abs("\<sigma>", sigma_i, first)) )::R
                              | C_AbsEnv.Parameter(_) => (mk_assign_local_C
                                            (mk_loc_upd_ident long_id ty sigma_i)
                                            (Abs("\<sigma>", sigma_i, first)) )::R
                              | C_AbsEnv.Local(_) => (mk_assign_local_C 
                                            (mk_loc_upd_ident long_id ty sigma_i)
                                            (Abs("\<sigma>", sigma_i, first)) )::R
                              | s => error("(convertStmt_raw_ident) CAssign0 with cat " ^ @{make_string} s ^ " is unrecognised")
                           end)
                      |_ => raise WrongFormat("assign"))
     (*statements*)
(*for return, skip and break, we have makers except that they need types and terms that i didn't 
understand so it's unfinished here*)
     |"CReturn0" => let val rhs = hd stack
                        val res_upd = mk_result_update thy ctxt
                    in (mk_return_C res_upd (Abs("\<sigma>", sigma_i, rhs))) :: (tl stack) end
     |"CSkip0" => (mk_skip_C sigma_i)::stack
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
                       (a::b::cond::R) => mk_if_C  (Abs("\<sigma>", sigma_i --> boolT, cond)) b  a::R
                    |  (a::cond::R) => (mk_if_C (Abs("\<sigma>", sigma_i --> boolT, cond)) 
                                                (a)
                                                (mk_skip_C sigma_i)::R)
                    |_ => raise WrongFormat("if")
                   )
     |"CWhile0" => (case stack of
                       (a::b::R) => (mk_while_C  (Abs("\<sigma>", sigma_i, b))  a)::R
                      |(a::R)    => (mk_while_C  (Abs("\<sigma>", sigma_i, a))  
                                                 (mk_skip_C dummyT))
                                    ::R
                      |_ => raise WrongFormat("while")
                   )
(*There is no For operator in Clean, so we have to translate it as a while :
for(ini, cond, evol){body} is translated as ini; while(cond){body; evol;}*)
     |"CFor0" =>   (case stack of
                        (body::pace::cond::init::R) => (let val C' = mk_while_C
                                                                       (Abs("\<sigma>", sigma_i,cond))
                                                                       (mk_seq_C body pace)
                                                        in   ((mk_seq_C init C'))::R end)
                    |_ => raise WrongFormat("for"))
     | "CCall0" => (let fun extract_fun_args (t :: R) args =
                            case t of
                            (* very bad way of checking if term represents a function *)
                               Const(id, ty) => if not (firstype_of ty = sigma_i) then (args, Const(id, ty), R) else extract_fun_args R (Const(id, ty) :: args)
                            | arg => extract_fun_args R (arg :: args)
                        fun extract_type_list (arg :: args) =
                            (case arg of
                              (* should be expanded for the 3 term representations of variables... *)
                              Free(_, ty) => ty :: extract_type_list args)
                          | extract_type_list [] = []
                        (* should be expanded for variable number of args... *)
                        fun mk_cross_prod_args [a, b] = Const (@{const_name "Pair"}, a --> b --> mk_prodT (a, b))
                        val (args, f, R) = extract_fun_args stack []
                        val cross_prod_args = mk_cross_prod_args (extract_type_list args)
                        val fun_args_term = list_comb (cross_prod_args, args)
                       in mk_call_C f (Abs("\<sigma>", sigma_i, fun_args_term)) :: R end)
     | _ => convertExpr_raw_ident verbose sigma_i env thy ctxt identifiers a b stack )

end

(*** -------------- ***)
\<close>

ML\<open>
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



\<close> 
end