

theory "CleanCoder"
  imports "Isabelle_C.C_Main" 
          "HOL.Real"
          "Clean.Clean"
begin




section\<open>A small compiler to Isabelle term's.\<close>

text \<open>
The goal of this project is to develop a translation function from the language C11 to
Clean. In particular, the function take as an argument the result of the parser, and create 
a typed \<lambda>-term which encoded the semanticaly equivalent program in Clean.\<close>


text \<open>We will use different auxiliary functions to do operations on the terms, and to help
to understand what kind of types and objects we do manipulate. \<close>


ML\<open>

(*------toStrings et affichages-------*)

(*renvoie un string représentant un objet data*)
fun toString_data data = case data of
      C11_Ast_Lib.data_bool e => "Bool : "^Bool.toString e
     |C11_Ast_Lib.data_int e => "Int : "^Int.toString e
     |C11_Ast_Lib.data_string e => "String : "^e
     |C11_Ast_Lib.data_absstring e => "AbsString : "^e
 
fun toString_args args = "["^(String.concatWith ", "(List.map (toString_data) args))^ "]"


fun to_String_positiona (C_Ast.Position0 (i,S, k,l)) = "POS "^ @{make_string} S
  | to_String_positiona C_Ast.NoPosition0 = ""
  | to_String_positiona C_Ast.BuiltinPosition0 = ""
  | to_String_positiona C_Ast.InternalPosition0 = ""

fun toString_nodeInfo (C_Ast.OnlyPos0(p, (_, _))) = to_String_positiona p
   |toString_nodeInfo (C_Ast.NodeInfo0(p, (_, _), C_Ast.Name0 name))  
                                                  = to_String_positiona p ^ Int.toString name


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

(*créé un term upd global*)
fun mk_glob_upd name rhs = 
  let 
    val ty   = fastype_of rhs
    val ty'  = lastype_of ty
    val ty'' = firstype_of ty
  in  Const(name^"_update", (ty' --> ty') --> ty'' --> ty'')
  end

(*créé un term upd local*)
fun mk_loc_upd name rhs = 
  let 
    val ty   = fastype_of rhs
    val ty'  = lastype_of ty
    val ty'' = firstype_of ty
  in  Const(name^"_update", (HOLogic.listT ty' --> HOLogic.listT ty') --> ty'' --> ty'')
  end

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
                                             | _ => error("illformed expression:")
                    in  (Const(long_id,sigma_i --> ty) $ Bound 0)::c
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

     | str => error("unsupported expression with parse tag: "^str)) (* global catch all *)

fun conv_Cexpr_term C_env sigma_i thy C_expr = 
    Abs("\<sigma>", sigma_i, hd((C11_Ast_Lib.fold_cExpression (K I)
                               (convertExpr_raw false sigma_i C_env thy) C_expr [])))
    (* Better: abstract_over (Free(\<sigma>, sigma_i)) ??? *)
\<close>
ML\<open>\<close>
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
             val _ = mk_seq_C
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

end
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
     |"Begin" => (Const("Begin", dummyT))::c
     |"End" => (Const("End", dummyT))::c
     | s =>  (c)
)



\<close> 
end