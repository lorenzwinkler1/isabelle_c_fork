(******************************************************************************
 * Isabelle/C
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
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

section \<open>Core Language: Parsing Support (C Language without Annotations)\<close>

theory C_Parser_Language
  imports C_Environment
begin

text \<open> As mentioned in \<^theory>\<open>Isabelle_C_Advanced.C_Ast\<close>, Isabelle/C depends
on certain external parsing libraries, such as \<^dir>\<open>../../src_ext/mlton\<close>, and more
specifically \<^dir>\<open>../../src_ext/mlton/lib/mlyacc-lib\<close>. Actually, the sole theory
making use of the files in \<^dir>\<open>../../src_ext/mlton/lib/mlyacc-lib\<close> is the present
\<^file>\<open>C_Parser_Language.thy\<close>. (Any other remaining files in
\<^dir>\<open>../../src_ext/mlton\<close> are not used by Isabelle/C, they come from the original
repository of MLton: \<^url>\<open>https://github.com/MLton/mlton\<close>.) \<close>

subsection \<open>Parsing Library (Including Semantic Functions)\<close>

ML \<comment> \<open>\<^file>\<open>../generated/c_grammar_fun.grm.sml\<close>\<close>
(*
 * Modified by Frédéric Tuong, Université Paris-Saclay
 *
 *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *
 *
 * https://github.com/jhjourdan/C11parser
 *
 * Jacques-Henri Jourdan, Inria Paris
 * François Pottier, Inria Paris
 *
 * Copyright (c) 2016-2017, Inria
 *
 *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *
 *
 * Language.C
 * https://hackage.haskell.org/package/language-c
 *
 * Copyright (c) 1999-2017 Manuel M T Chakravarty
 *                         Duncan Coutts
 *                         Benedikt Huber
 * Portions Copyright (c) 1989,1990 James A. Roskind
 *
 *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *
 *
 * Language.C.Comments
 * https://hackage.haskell.org/package/language-c-comments
 *
 * Copyright (c) 2010-2014 Geoff Hulette
 *)
\<open>
signature C_GRAMMAR_RULE_LIB =
sig
  type arg = (C_Antiquote.antiq * C_Env.antiq_language list) C_Env.T
  type 'a monad = arg -> 'a * arg

  (* type aliases *)
  type reports_text0' = { markup : Markup.T, markup_body : string }
  type reports_text0 = reports_text0' list -> reports_text0' list
  type ('a, 'b) reports_base = ('a C_Env.markup_store * Position.T list,
                                Position.T list * 'a C_Env.markup_store option) C_Ast.either ->
                               Position.T list ->
                               string ->
                               'b ->
                               'b

  (* monadic operations *)
  val return : 'a -> 'a monad
  val bind : 'a monad -> ('a -> 'b monad) -> 'b monad
  val bind' : 'b monad -> ('b -> unit monad) -> 'b monad
  val >> : unit monad * 'a monad -> 'a monad

  (* position reports *)
  val markup_make : ('a -> reports_text0' option) ->
                    ('a -> 'b) ->
                    ('b option -> string) ->
                    ((Markup.T -> reports_text0) ->
                     bool ->
                     ('b, 'b option * string * reports_text0) C_Ast.either ->
                     reports_text0) ->
                    ('a, C_Position.reports_text) reports_base
  val markup_tvar : (C_Env.markup_global, C_Position.reports_text) reports_base
  val markup_var_enum : (C_Env.markup_global, C_Position.reports_text) reports_base
  val markup_var : (C_Env.markup_ident, C_Position.reports_text) reports_base
  val markup_var_bound : (C_Env.markup_ident, C_Position.reports_text) reports_base
  val markup_var_improper : (C_Env.markup_ident, C_Position.reports_text) reports_base

  (* context.mli *)
  val declare_typedefname: string -> unit monad
  val declare_varname0: string -> C_Env.env_lang -> C_Env.env_lang
  val declare_varname: string -> unit monad
  val is_typedefname: string -> arg -> bool
  type c_context
  val save_context: unit -> c_context monad
  val restore_context: c_context -> unit monad

  (* declarator.mli *)
  type c_declarator
  val identifier: c_declarator -> string
  val identifier_declarator: string -> c_declarator monad
  val function_declarator: c_declarator -> c_context -> c_declarator monad
  val other_declarator: c_declarator -> c_declarator monad
  val reinstall_function_context: c_declarator -> unit monad
end

structure C_Grammar_Rule_Lib : C_GRAMMAR_RULE_LIB =
struct
  open C_Ast
  type arg = (C_Antiquote.antiq * C_Env.antiq_language list) C_Env.T
  type 'a monad = arg -> 'a * arg

  (**)
  type reports_text0' = { markup : Markup.T, markup_body : string }
  type reports_text0 = reports_text0' list -> reports_text0' list
  type 'a reports_store = Position.T list * serial * 'a
  type ('a, 'b) reports_base = ('a C_Env.markup_store * Position.T list,
                                Position.T list * 'a C_Env.markup_store option) C_Ast.either ->
                               Position.T list ->
                               string ->
                               'b ->
                               'b
  fun markup_init markup = { markup = markup, markup_body = "" }
  val look_idents = C_Env_Ext.list_lookup o C_Env_Ext.get_idents
  val look_idents' = C_Env_Ext.list_lookup o C_Env_Ext.get_idents'
  val look_tyidents_typedef = C_Env_Ext.list_lookup o C_Env_Ext.get_tyidents_typedef
  val look_tyidents'_typedef = C_Env_Ext.list_lookup o C_Env_Ext.get_tyidents'_typedef
  val To_string0 = meta_of_logic
  val ident_encode =
    Word8Vector.foldl (fn (w, acc) => Word8.toInt w + acc * 256) 0 o Byte.stringToBytes
  fun ident_decode nb = radixpand (256, nb) |> map chr |> implode
  fun reverse l = rev l

  fun report _ [] _ = I
    | report markup ps x =
        let val ms = markup x
        in fold (fn p => fold (fn {markup, markup_body} => cons ((p, markup), markup_body)) ms) ps
        end

  fun markup_make typing get_global desc report' data =
   report
   (fn name =>
    let 
      val (def, ps, id, global, typing) =
        case data of
          Left ((ps, id, param), ps' as _ :: _) =>
            ( true
            , ps
            , id
            , Right ( SOME (get_global param)
                    , "Redefinition of " ^ quote name ^ Position.here_list ps
                 \<comment> \<open>Any positions provided here will be explicitly reported, which might not be the
                     desired effect. So we explicitly refer the reader to a separate tooltip.\<close>
                                         ^ " (more details in the command modifier tooltip)"
                    , cons { markup = Markup.class_parameter
                           , markup_body = "redefining this" ^ Position.here_list ps' })
            , typing param)
        | Left ((ps, id, param), _) => (true, ps, id, Left (get_global param), typing param)
        | Right (_, SOME (ps, id, param)) => (false, ps, id, Left (get_global param), typing param)
        | Right (ps, _) => ( true
                           , ps
                           , serial ()
                           , Right (NONE, "Undeclared " ^ quote name ^ Position.here_list ps, I)
                           , NONE)
      fun markup_elem name = (name, (name, []): Markup.T)
      val (varN, var) = markup_elem (desc (case global of Left b => SOME b
                                                        | Right (SOME b, _, _) => SOME b
                                                        | _ => NONE));
      val cons' = cons o markup_init
    in
     (cons' var
      #> report' cons' def global
      #> (case typing of NONE => I | SOME x => cons x))
       (map (markup_init o Position.make_entity_markup {def = def} id varN o pair name) ps)
    end)

  fun markup_make' typing get_global desc report =
    markup_make
      typing
      get_global
      (fn global =>
        "C " ^ (case global of SOME true => "global "
                             | SOME false => "local "
                             | NONE => "")
             ^ desc)
      (fn cons' => fn def =>
       fn Left b => report cons' def b
        | Right (b, msg, f) => tap (fn _ => Output.information msg)
                            #> f
                            #> (case b of NONE => cons' Markup.free | SOME b => report cons' def b))

  fun markup_tvar0 desc =
    markup_make'
      (K NONE)
      I
      desc
      (fn cons' => fn def =>
       fn true => cons' (if def then Markup.free else Markup.ML_keyword3)
        | false => cons' Markup.skolem)

  val markup_tvar = markup_tvar0 "type variable"
  val markup_var_enum = markup_tvar0 "enum tag"

  fun string_of_list f =
    (fn [] => NONE | [s] => SOME s | s => SOME ("[" ^ String.concatWith ", " s ^ "]"))
    o map f

  val string_of_cDeclarationSpecifier =
    fn C_Ast.CStorageSpec0 _ => "storage"
     | C_Ast.CTypeSpec0 t => (case t of 
                                 CVoidType0 _ => "void"
                               | CCharType0 _ => "char"
                               | CShortType0 _ => "short"
                               | CIntType0 _ => "int"
                               | CLongType0 _ => "long"
                               | CFloatType0 _ => "float"
                               | CDoubleType0 _ => "double"
                               | CSignedType0 _ => "signed"
                               | CUnsigType0 _ => "unsig"
                               | CBoolType0 _ => "bool"
                               | CComplexType0 _ => "complex"
                               | CInt128Type0 _ => "int128"
                               | CSUType0 _ => "SU"
                               | CEnumType0 _ => "enum"
                               | CTypeDef0 _ => "typedef"
                               | CTypeOfExpr0 _ => "type_of_expr"
                               | CTypeOfType0 _ => "type_of_type"
                               | CAtomicType0 _ => "atomic")
     | C_Ast.CTypeQual0 _ => "type_qual"
     | C_Ast.CFunSpec0 _ => "fun"
     | C_Ast.CAlignSpec0 _ => "align"

  fun typing {params, ret, ...} =
    SOME
    { markup = Markup.typing
    , markup_body =
       case
        ( string_of_list
           (fn C_Ast.CPtrDeclr0 _ => "pointer"
             | C_Ast.CArrDeclr0 _ => "array"
             | C_Ast.CFunDeclr0 (C_Ast.Left _, _, _) => "function [...] ->"
             | C_Ast.CFunDeclr0 (C_Ast.Right (l_decl, _), _, _) =>
                "function "
                ^ (String.concatWith
                    " -> "
                    (map (fn CDecl0 ([decl], _, _) => string_of_cDeclarationSpecifier decl
                           | CDecl0 (l, _, _) => "(" ^ String.concatWith
                                                         " "
                                                         (map string_of_cDeclarationSpecifier l)
                                                     ^ ")"
                           | CStaticAssert0 _ => "static_assert")
                         l_decl))
                ^ " ->")
           params
        , case ret of C_Env.Previous_in_stack => SOME "..."
                    | C_Env.Parsed ret => string_of_list string_of_cDeclarationSpecifier ret)
       of (NONE, NONE) => let val _ = warning "markup_var: Not yet implemented" in "" end
        | (SOME params, NONE) => params
        | (NONE, SOME ret) => ret
        | (SOME params, SOME ret) => params ^ " " ^ ret }

  val markup_var =
    markup_make'
      typing
      #global
      "variable"
      (fn cons' => fn def =>
       fn true => if def then cons' Markup.free else cons' Markup.delimiter (*explicit black color,
                                                     otherwise the default color of constants might
                                                     be automatically chosen (especially in term
                                                     cartouches)*)
        | false => cons' Markup.bound)

  val markup_var_bound =
    markup_make' typing #global "variable" (fn cons' => K (K (cons' Markup.bound)))

  val markup_var_improper =
    markup_make' typing #global "variable" (fn cons' => K (K (cons' Markup.improper)))

  (**)
  val return = pair
  fun bind f g = f #-> g
  fun bind' f g = bind f (fn r => bind (g r) (fn () => return r))
  fun a >> b = a #> b o #2
  fun sequence_ f = fn [] => return ()
                     | x :: xs => f x >> sequence_ f xs

  (* Language.C.Data.RList *)
  val empty = []
  fun singleton x = [x]
  fun snoc xs x = x :: xs
  fun rappend xs ys = rev ys @ xs
  fun rappendr xs ys = ys @ xs
  val rmap = map
  val viewr = fn [] => error "viewr: empty RList"
               | x :: xs => (xs, x)

  (* Language.C.Data.Position *)
  val nopos = NoPosition
  fun posOf _ = NoPosition
  fun posOf' mk_range =
    (if mk_range then Position.range else I)
    #> (fn (pos1, pos2) =>
          let val {offset = offset, end_offset = end_offset, ...} = Position.dest pos1
          in ( Position offset (From_string (C_Env.encode_positions [pos1, pos2])) 0 0
             , end_offset - offset)
          end)
  fun posOf'' node env =
    let val (stack, len) = #rule_input env
        val (mk_range, (pos1a, pos1b)) = case node of Left i => (true, nth stack (len - i - 1))
                                                    | Right range => (false, range)
        val (pos2a, pos2b) = nth stack 0
    in ( (posOf' mk_range (pos1a, pos1b) |> #1, posOf' true (pos2a, pos2b))
       , env |> C_Env_Ext.map_output_pos (K (SOME (pos1a, pos2b)))
             |> C_Env_Ext.map_output_vacuous (K false)) end
  val posOf''' = posOf'' o Left
  val internalPos = InternalPosition
  fun make_comment body_begin body body_end range =
    Commenta ( posOf' false range |> #1
             , From_string (Symbol_Pos.implode (body_begin @ body @ body_end))
             , case body_end of [] => SingleLine | _ => MultiLine)

  (* Language.C.Data.Node *)
  val undefNode = OnlyPos nopos (nopos, ~1)
  fun mkNodeInfoOnlyPos pos = OnlyPos pos (nopos, ~1)
  fun mkNodeInfo pos name = NodeInfo pos (nopos, ~1) name
  val mkNodeInfo' = NodeInfo
  val decode =
   (fn OnlyPos0 range => range
     | NodeInfo0 (pos1, (pos2, len2), _) => (pos1, (pos2, len2)))
   #> (fn (Position0 (_, s1, _, _), (Position0 (_, s2, _, _), _)) =>
            (case (C_Env.decode_positions (To_string0 s1), C_Env.decode_positions (To_string0 s2))
             of ([pos1, _], [_, pos2]) => Left (Position.range (pos1, pos2))
              | _ => Right "Expecting 2 elements")
        | _ => Right "Invalid position")
  fun decode_error' x = case decode x of Left x => x | Right msg => error msg
  fun decode_error x = Right (decode_error' x)
  val nameOfNode = fn OnlyPos0 _ => NONE
                    | NodeInfo0 (_, _, name) => SOME name

  (* Language.C.Data.Ident *)
  local
    val bits7 = Integer.pow 7 2
    val bits14 = Integer.pow 14 2
    val bits21 = Integer.pow 21 2
    val bits28 = Integer.pow 28 2
  in
  fun quad s = case s of
    [] => 0
  | c1 :: [] => SML90.ord c1
  | c1 :: c2 :: [] => SML90.ord c2 * bits7 + SML90.ord c1
  | c1 :: c2 :: c3 :: [] => SML90.ord c3 * bits14 + SML90.ord c2 * bits7 + SML90.ord c1
  | c1 :: c2 :: c3 :: c4 :: s => ((SML90.ord c4 * bits21
                                   + SML90.ord c3 * bits14
                                   + SML90.ord c2 * bits7
                                   + SML90.ord c1)
                                  mod bits28)
                                 + (quad s mod bits28)
  end

  local
    fun internalIdent0 pos s = Ident (From_string s, ident_encode s, pos)
  in
  fun mkIdent (pos, len) s name = internalIdent0 (mkNodeInfo' pos (pos, len) name) s
  val internalIdent = internalIdent0 (mkNodeInfoOnlyPos internalPos)
  end

  (* Language.C.Syntax.AST *)
  fun liftStrLit (CStrLit0 (str, at)) = CStrConst str at

  (* Language.C.Syntax.Constants *)
  fun concatCStrings cs =
        CString0 (flattena (map (fn CString0 (s,_) => s) cs), exists (fn CString0 (_, b) => b) cs)

  (* Language.C.Parser.ParserMonad *)
  fun getNewName env =
    (Namea (C_Env_Ext.get_namesupply env), C_Env_Ext.map_namesupply (fn x => x + 1) env)

  fun addTypedef (Ident0 (_, i, node)) env =
    let val name = ident_decode i
        val pos1 = [decode_error' node |> #1]
        val data = (pos1, serial (), null (C_Env_Ext.get_scopes env))
    in ((), env |> C_Env_Ext.map_idents (Symtab.delete_safe name)
                |> C_Env_Ext.map_tyidents_typedef (Symtab.update (name, data))
                |> C_Env_Ext.map_reports_text
                     (markup_tvar
                       (Left (data, flat [ look_idents env name, look_tyidents_typedef env name ]))
                       pos1
                       name))
    end
  fun shadowTypedef0''' name pos data0 env_lang env_tree =
    let val data = (pos, serial (), data0)
        val update_id = Symtab.update (name, data)
    in ( env_lang |> C_Env_Ext.map_tyidents'_typedef (Symtab.delete_safe name)
                  |> C_Env_Ext.map_idents' update_id
       , update_id
       , env_tree
          |> C_Env.map_reports_text
               (markup_var (Left (data, flat [ look_idents' env_lang name
                                             , look_tyidents'_typedef env_lang name ]))
                           pos
                           name))
    end
  fun shadowTypedef0'''' name pos data0 env_lang env_tree =
    let val (env_lang, _, env_tree) = shadowTypedef0''' name pos data0 env_lang env_tree
    in ( env_lang, env_tree) end
  fun shadowTypedef0'' ret global (Ident0 (_, i, node), params) =
    shadowTypedef0''' (ident_decode i)
                      [decode_error' node |> #1]
                      {global = global, params = params, ret = ret}
  fun shadowTypedef0' ret global ident env_lang env_tree =
    let val (env_lang, _, env_tree) = shadowTypedef0'' ret global ident env_lang env_tree 
    in (env_lang, env_tree) end
  fun shadowTypedef0 ret global f ident env =
    let val (update_id, env) =
          C_Env.map_env_lang_tree'
            (fn env_lang => fn env_tree => 
              let val (env_lang, update_id, env_tree) =
                        shadowTypedef0'' ret global ident env_lang env_tree 
              in (update_id, (env_lang, env_tree)) end)
            env
    in ((), f update_id env) end
  fun shadowTypedef_fun ident env =
    shadowTypedef0 C_Env.Previous_in_stack
                   (case C_Env_Ext.get_scopes env of _ :: [] => true | _ => false)
                   (fn update_id =>
                    C_Env_Ext.map_scopes
                     (fn (NONE, x) :: xs => (SOME (fst ident), C_Env.map_idents update_id x) :: xs
                       | (SOME _, _) :: _ => error "Not yet implemented"
                       | [] => error "Not expecting an empty scope"))
                   ident
                   env
  fun shadowTypedef (i, params, ret) env =
    shadowTypedef0 (C_Env.Parsed ret) (List.null (C_Env_Ext.get_scopes env)) (K I) (i, params) env
  fun isTypeIdent s0 = Symtab.exists (fn (s1, _) => s0 = s1) o C_Env_Ext.get_tyidents_typedef
  fun enterScope env =
    ((), C_Env_Ext.map_scopes (cons (NONE, C_Env_Ext.get_var_table env)) env)
  fun leaveScope env = 
    case C_Env_Ext.get_scopes env of
      [] => error "leaveScope: already in global scope"
    | (_, var_table) :: scopes => ((), env |> C_Env_Ext.map_scopes (K scopes)
                                           |> C_Env_Ext.map_var_table (K var_table))
  val getCurrentPosition = return NoPosition

  (* Language.C.Parser.Tokens *)
  fun CTokCLit x f = x |> f
  fun CTokILit x f = x |> f
  fun CTokFLit x f = x |> f
  fun CTokSLit x f = x |> f

  (* Language.C.Parser.Parser *)
  fun reverseList x = rev x
  fun L a i = posOf''' i #>> curry Located a
  fun unL (Located (a, _)) = a
  fun withNodeInfo00 (pos1, (pos2, len2)) mkAttrNode name =
    return (mkAttrNode (NodeInfo pos1 (pos2, len2) name))
  fun withNodeInfo0 x = x |> bind getNewName oo withNodeInfo00
  fun withNodeInfo0' node mkAttrNode env = let val (range, env) = posOf'' node env
                                           in withNodeInfo0 range mkAttrNode env end
  fun withNodeInfo x = x |> withNodeInfo0' o Left
  fun withNodeInfo' x = x |> withNodeInfo0' o decode_error
  fun withNodeInfo_CExtDecl x = x |>
    withNodeInfo' o (fn CDeclExt0 (CDecl0 (_, _, node)) => node
                      | CDeclExt0 (CStaticAssert0 (_, _, node)) => node
                      | CFDefExt0 (CFunDef0 (_, _, _, _, node)) => node
                      | CAsmExt0 (_, node) => node)
  val get_node_CExpr =
    fn CComma0 (_, a) => a | CAssign0 (_, _, _, a) => a | CCond0 (_, _, _, a) => a |
    CBinary0 (_, _, _, a) => a | CCast0 (_, _, a) => a | CUnary0 (_, _, a) => a |
    CSizeofExpr0 (_, a) => a | CSizeofType0 (_, a) => a | CAlignofExpr0 (_, a) => a |
    CAlignofType0 (_, a) => a | CComplexReal0 (_, a) => a | CComplexImag0 (_, a) => a |
    CIndex0 (_, _, a) => a |
    CCall0 (_, _, a) => a | CMember0 (_, _, _, a) => a | CVar0 (_, a) => a | CConst0 c => (case c of
    CIntConst0 (_, a) => a | CCharConst0 (_, a) => a | CFloatConst0 (_, a) => a |
    CStrConst0 (_, a) => a) |
    CCompoundLit0 (_, _, a) => a | CGenericSelection0 (_, _, a) => a | CStatExpr0 (_, a) => a |
    CLabAddrExpr0 (_, a) => a | CBuiltinExpr0 cBuiltinThing => (case cBuiltinThing
     of CBuiltinVaArg0 (_, _, a) => a
     | CBuiltinOffsetOf0 (_, _, a) => a
     | CBuiltinTypesCompatible0 (_, _, a) => a)
  fun withNodeInfo_CExpr x = x |> withNodeInfo' o get_node_CExpr o hd
  fun withLength node mkAttrNode =
    bind (posOf'' (decode_error node)) (fn range => 
      withNodeInfo00 range mkAttrNode (case nameOfNode node of NONE => error "nameOfNode"
                                                             | SOME name => name))
  fun reverseDeclr (CDeclrR0 (ide, reversedDDs, asmname, cattrs, at)) =
                    CDeclr ide (rev reversedDDs) asmname cattrs at
  fun appendDeclrAttrs newAttrs (CDeclrR0 (ident, l, asmname, cattrs, at)) =
    case l of
      [] => CDeclrR ident empty asmname (cattrs @ newAttrs) at
    | x :: xs =>
      let
        val appendAttrs =
          fn CPtrDeclr0 (typeQuals, at) => CPtrDeclr (typeQuals @ map CAttrQual newAttrs) at
           | CArrDeclr0 (typeQuals, arraySize, at) => CArrDeclr (typeQuals @ map CAttrQual newAttrs)
                                                                arraySize
                                                                at
           | CFunDeclr0 (parameters, cattrs, at) => CFunDeclr parameters (cattrs @ newAttrs) at
      in CDeclrR ident (appendAttrs x :: xs) asmname cattrs at end
  fun withAttribute node cattrs mkDeclrNode =
    bind (posOf''' node) (fn (pos, _) =>
    bind getNewName (fn name =>
        let val attrs = mkNodeInfo pos name
            val newDeclr = appendDeclrAttrs cattrs (mkDeclrNode attrs)
        in return newDeclr end))
  fun withAttributePF node cattrs mkDeclrCtor =
    bind (posOf''' node) (fn (pos, _) =>
    bind getNewName (fn name =>
        let val attrs = mkNodeInfo pos name
            val newDeclr = appendDeclrAttrs cattrs o mkDeclrCtor attrs
        in return newDeclr end))
  fun appendObjAttrs newAttrs (CDeclr0 (ident, indirections, asmname, cAttrs, at)) =
    CDeclr ident indirections asmname (cAttrs @ newAttrs) at
  fun appendObjAttrsR newAttrs (CDeclrR0 (ident, indirections, asmname, cAttrs, at)) =
    CDeclrR ident indirections asmname (cAttrs @ newAttrs) at
  fun setAsmName mAsmName (CDeclrR0 (ident, indirections, oldName, cattrs, at)) =
    case (case (mAsmName, oldName)
          of (None, None) => Right None
           | (None, oldname as Some _) => Right oldname
           | (newname as Some _, None) => Right newname
           | (Some n1, Some n2) => Left (n1, n2))
    of
      Left (n1, n2) => let fun showName (CStrLit0 (CString0 (s, _), _)) = To_string0 s
                       in error ("Duplicate assembler name: " ^ showName n1 ^ " " ^ showName n2) end
    | Right newName => return (CDeclrR ident indirections newName cattrs at)
  fun withAsmNameAttrs (mAsmName, newAttrs) declr =
        setAsmName mAsmName (appendObjAttrsR newAttrs declr)
  fun ptrDeclr (CDeclrR0 (ident, derivedDeclrs, asmname, cattrs, dat)) tyquals at =
    CDeclrR ident (snoc derivedDeclrs (CPtrDeclr tyquals at)) asmname cattrs dat
  fun funDeclr (CDeclrR0 (ident, derivedDeclrs, asmname, dcattrs, dat)) params cattrs at =
    CDeclrR ident (snoc derivedDeclrs (CFunDeclr params cattrs at)) asmname dcattrs dat
  fun arrDeclr (CDeclrR0 (ident, derivedDeclrs, asmname, cattrs, dat))
               tyquals
               var_sized
               static_size
               size_expr_opt
               at =
    CDeclrR ident
            (snoc
               derivedDeclrs
               (CArrDeclr tyquals (case size_expr_opt of
                                     Some e => CArrSize static_size e
                                   | None => CNoArrSize var_sized) at))
            asmname
            cattrs
            dat
  val liftTypeQuals = map CTypeQual o reverse
  val liftCAttrs = map (CTypeQual o CAttrQual)
  fun addTrailingAttrs declspecs new_attrs =
    case viewr declspecs of
      (specs_init, CTypeSpec0 (CSUType0 (CStruct0 (tag, name, Some def, def_attrs, su_node), node)))
      =>
        snoc
          specs_init
          (CTypeSpec (CSUType (CStruct tag name (Just def) (def_attrs @ new_attrs) su_node) node))
    | (specs_init, CTypeSpec0 (CEnumType0 (CEnum0 (name, Some def, def_attrs, e_node), node))) => 
        snoc
          specs_init
          (CTypeSpec (CEnumType (CEnum name (Just def) (def_attrs @ new_attrs) e_node) node))
    | _ => rappend declspecs (liftCAttrs new_attrs)
  val emptyDeclr = CDeclrR Nothing empty Nothing [] undefNode
  fun mkVarDeclr ident = CDeclrR (Some ident) empty Nothing []
  fun doDeclIdent declspecs (decl as CDeclrR0 (mIdent, _, _, _, _)) =
    case mIdent of
      None => return ()
    | Some ident =>
       if exists (fn CStorageSpec0 (CTypedef0 _) => true | _ => false) declspecs
       then addTypedef ident
       else shadowTypedef ( ident
                          , case reverseDeclr decl of CDeclr0 (_, params, _, _, _) => params
                          , declspecs)

  val ident_of_decl =
    fn Left params => map (fn i => (i, [], [])) params
     | Right (params, _) =>
        maps (fn CDecl0 (ret, l, _) =>
                   maps (fn ((Some (CDeclr0 (Some mIdent, params, _, _, _)),_),_) =>
                              [(mIdent, params, ret)]
                          | _ => [])
                        l
               | _ => [])
             params

  local
  fun sequence_' f = sequence_ f o ident_of_decl
  val is_fun = fn CFunDeclr0 _ => true | _ => false
  in
  fun doFuncParamDeclIdent (CDeclr0 (mIdent0, param0, _, _, node0)) =
    let
      val (param_not_fun, param0') = chop_prefix (not o is_fun) param0
      val () =
        if null param_not_fun then ()
        else
          Output.information
            ("Not a function"
             ^ Position.here
                 (decode_error' (case mIdent0 of None => node0
                                               | Some (Ident0 (_, _, node)) => node) |> #1))
      val (param_fun, param0') = chop_prefix is_fun param0'
    in
      (case mIdent0 of None => return ()
                     | Some mIdent0 => shadowTypedef_fun (mIdent0, param0))
      >>
      sequence_ shadowTypedef
                (maps (fn CFunDeclr0 (params, _, _) => ident_of_decl params | _ => []) param_fun)
      >>
      sequence_
        (fn CFunDeclr0 (params, _, _) =>
            C_Env.map_env_tree
              (pair Symtab.empty
               #> sequence_'
                  (fn (Ident0 (_, i, node), params, ret) => fn (env_lang, env_tree) => pair ()
                    let
                      val name = ident_decode i
                      val pos = [decode_error' node |> #1]
                      val data = ( pos
                                 , serial ()
                                 , {global = false, params = params, ret = C_Env.Parsed ret})
                    in
                      ( env_lang |> Symtab.update (name, data)
                      , env_tree
                          |> C_Env.map_reports_text
                               (markup_var_improper
                                 (Left (data, C_Env_Ext.list_lookup env_lang name))
                                 pos
                                 name))
                    end)
                  params
               #> #2 o #2)
            #> pair ()
          | _ => return ())
        param0'
    end
  end

  (**)
  structure List = struct val reverse = rev end

  (* context.mli *)
  fun declare_typedefname id arg =
    ((), C_Env_Ext.map_tyidents_typedef (Symtab.update (id, ([], 0, true))) arg)
  fun declare_varname0 id =
    C_Env_Ext.map_tyidents'_typedef (Symtab.delete_safe id)
  fun declare_varname id arg =
    ((), C_Env.map_env_lang (declare_varname0 id) arg)
  fun is_typedefname id arg =
    Symtab.defined (C_Env_Ext.get_tyidents_typedef arg) id
  datatype c_context = C_context of bool C_Env.markup_store Symtab.table
  fun save_context () arg =
    return (C_context (C_Env_Ext.get_tyidents_typedef arg)) arg
  fun restore_context (C_context tab) arg =
    ((), C_Env_Ext.map_tyidents_typedef (K tab) arg)

  (* declarator.mli *)
  datatype declarator_kind = DeclaratorIdentifier
                           | DeclaratorFunction of c_context
                           | DeclaratorOther
  type c_declarator = {identifier: string, kind: declarator_kind}
  fun identifier {identifier, ...} = identifier
  fun identifier_declarator identifier =
    return {identifier = identifier, kind = DeclaratorIdentifier}
  fun function_declarator (d as {identifier, kind}) ctx =
    return
      (case kind of
         DeclaratorIdentifier => {identifier = identifier, kind = DeclaratorFunction ctx}
       | _ => d)
  fun other_declarator (d as {identifier, kind}) =
    return
      (case kind of
         DeclaratorIdentifier => {identifier = identifier, kind = DeclaratorOther}
       | _ => d)
  fun reinstall_function_context {identifier, kind} =
    case kind of
      DeclaratorFunction ctx =>
        bind
          (restore_context ctx)
          (fn _ => declare_varname identifier)
    | _ => return ()
end
\<close>

subsection \<open>Miscellaneous\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Thy/document_antiquotations.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay
    Analogous to:
(*  Title:      Pure/Thy/document_antiquotations.ML
    Author:     Makarius

Miscellaneous document antiquotations.
*)*)
\<open>
structure ML_Document_Antiquotations =
struct

(* ML text *)

local

fun ml_text name ml =
  Document_Output.antiquotation_raw_embedded name (Scan.lift Args.text_input \<comment> \<open>TODO: enable reporting with \<^ML_type>\<open>Token.file\<close> as in \<^ML>\<open>Resources.parse_files\<close>\<close>)
    (fn ctxt => fn text =>
      let val file_content =
            Token.file_source
              (Command.read_file (Resources.master_directory (Proof_Context.theory_of ctxt))
                                 Position.none
                                 false
                                 (Path.explode (#1 (Input.source_content text))))
          val _ = (*TODO: avoid multiple file scanning*)
            ML_Context.eval_in (SOME ctxt) ML_Compiler.flags Position.none (* \<leftarrow> (optionally)
                                                                              disabling a potential
                                                                              double report*)
                                                                           (ml file_content)
      in file_content
         |> Input.source_explode
         |> Source.of_list
         |> Source.source
              Symbol_Pos.stopper
                (Scan.bulk (Symbol_Pos.scan_comment "" >> (C_Scan.Left o pair true)
                            || Scan.many1 (Symbol.is_ascii_blank o Symbol_Pos.symbol)
                                 >> (C_Scan.Left o pair false)
                            || Scan.one (not o Symbol_Pos.is_eof) >> C_Scan.Right))
         |> Source.exhaust
         |> drop_prefix (fn C_Scan.Left _ => true | _ => false)
         |> drop_suffix (fn C_Scan.Left (false, _) => true | _ => false)
         |> maps (fn C_Scan.Left (_, x) => x | C_Scan.Right x => [x])
         |> Symbol_Pos.implode
         |> enclose "\n" "\n"
         |> cartouche
         |> Document_Output.output_source ctxt
         |> Document_Output.isabelle ctxt
      end);

fun ml_enclose bg en source =
  ML_Lex.read bg @ ML_Lex.read_source source @ ML_Lex.read en;

in

val _ = Theory.setup (ml_text \<^binding>\<open>ML_file\<close> (ml_enclose "" ""));

end;

end;
\<close>

subsection \<open>Loading the Grammar Simulator\<close>

text \<open> The parser consists of a generic module
\<^file>\<open>../../src_ext/mlton/lib/mlyacc-lib/base.sig\<close>, which interprets an
automata-like format generated from ML-Yacc. \<close>

ML_file "../../src_ext/mlton/lib/mlyacc-lib/base.sig" \<comment>
\<open>\<^ML_file>\<open>../../src_ext/mlton/lib/mlyacc-lib/base.sig\<close>\<close>
ML_file "../../src_ext/mlton/lib/mlyacc-lib/join.sml" \<comment>
\<open>\<^ML_file>\<open>../../src_ext/mlton/lib/mlyacc-lib/join.sml\<close>\<close>
ML_file "../../src_ext/mlton/lib/mlyacc-lib/lrtable.sml" \<comment>
\<open>\<^ML_file>\<open>../../src_ext/mlton/lib/mlyacc-lib/lrtable.sml\<close>\<close>
ML_file "../../src_ext/mlton/lib/mlyacc-lib/stream.sml" \<comment>
\<open>\<^ML_file>\<open>../../src_ext/mlton/lib/mlyacc-lib/stream.sml\<close>\<close>
ML_file "../../src_ext/mlton/lib/mlyacc-lib/parser1.sml" \<comment>
\<open>\<^ML_file>\<open>../../src_ext/mlton/lib/mlyacc-lib/parser1.sml\<close>\<close>

subsection \<open>Loading the Generated Grammar (SML signature)\<close>

ML_file "../generated/c_grammar_fun.grm.sig"

ML \<comment> \<open>\<^file>\<open>../generated/c_grammar_fun.grm.sig\<close>\<close>
(*TODO: the whole part should be maximally generated and integrated in the signature file*)
\<open>
structure C_Grammar_Rule = struct
open C_Grammar_Rule

(* ast_generic is an untyped universe of (some) ast's with the specific lenses put ... get ... *)

type ast_generic = start_happy

val get_CExpr = start_happy4
val get_CStat = start_happy3
val get_CExtDecl = start_happy2
val get_CTranslUnit = start_happy1

fun put_CExpr x       = Right (Right (Right (Left x))) : ast_generic
fun put_CStat x       = Right (Right (Left x))         : ast_generic
fun put_CExtDecl x    = Right (Left x)                 : ast_generic
fun put_CTranslUnit x = Left x                         : ast_generic

end
\<close>

subsection \<open>Overloading Grammar Rules (Optional Part)\<close>

ML \<comment> \<open>\<^file>\<open>../generated/c_grammar_fun.grm.sml\<close>\<close> \<open>
structure C_Grammar_Rule_Wrap_Overloading = struct

fun update_env_bottom_up f x arg = ((), C_Env.map_env_lang_tree (f x) arg)
fun update_env_top_down f x =
  pair () ##> (fn arg => C_Env_Ext.map_output_env (K (SOME (f x (#env_lang arg)))) arg)

end
\<close>

ML \<comment> \<open>\<^file>\<open>../generated/c_grammar_fun.grm.sml\<close>\<close> \<open>
structure C_Grammar_Rule_Wrap = struct
  open C_Grammar_Rule_Wrap
  open C_Grammar_Rule_Wrap_Overloading
end
\<close>

subsection \<open>Loading the Generated Grammar (SML structure)\<close>

ML_file "../generated/c_grammar_fun.grm.sml"

subsection \<open>Grammar Initialization\<close>

subsubsection \<open>Functor Application\<close>

ML \<comment> \<open>\<^file>\<open>../generated/c_grammar_fun.grm.sml\<close>\<close> \<open>
structure C_Grammar = C_Grammar_Fun (structure Token = LALR_Parser_Eval.Token)
\<close>

subsubsection \<open>Mapping Strings to Structured Tokens\<close>

ML \<comment> \<open>\<^file>\<open>../generated/c_grammar_fun.grm.sml\<close>\<close> \<open>
structure C_Grammar_Tokens =
struct
local open C_Grammar.Tokens in
  fun token_of_string error ty_string a1 a2 = fn
      "!" => BANG (ty_string, a1, a2)
    | "!=" => NEQ (ty_string, a1, a2)
    | "%" => PERCENT (ty_string, a1, a2)
    | "%=" => MOD_ASSIGN (ty_string, a1, a2)
    | "&" => AND (ty_string, a1, a2)
    | "&&" => ANDAND (ty_string, a1, a2)
    | "&=" => AND_ASSIGN (ty_string, a1, a2)
    | "(" => LPAREN (ty_string, a1, a2)
    | ")" => RPAREN (ty_string, a1, a2)
    | "*" => STAR (ty_string, a1, a2)
    | "*=" => MUL_ASSIGN (ty_string, a1, a2)
    | "+" => PLUS (ty_string, a1, a2)
    | "++" => INC (ty_string, a1, a2)
    | "+=" => ADD_ASSIGN (ty_string, a1, a2)
    | "," => COMMA (ty_string, a1, a2)
    | "-" => MINUS (ty_string, a1, a2)
    | "--" => DEC (ty_string, a1, a2)
    | "-=" => SUB_ASSIGN (ty_string, a1, a2)
    | "->" => PTR (ty_string, a1, a2)
    | "." => DOT (ty_string, a1, a2)
    | "..." => ELLIPSIS (ty_string, a1, a2)
    | "/" => SLASH (ty_string, a1, a2)
    | "/=" => DIV_ASSIGN (ty_string, a1, a2)
    | ":" => COLON (ty_string, a1, a2)
    | ";" => SEMICOLON (ty_string, a1, a2)
    | "<" => LT (ty_string, a1, a2)
    | "<<" => LEFT (ty_string, a1, a2)
    | "<<=" => LEFT_ASSIGN (ty_string, a1, a2)
    | "<=" => LEQ (ty_string, a1, a2)
    | "=" => EQ (ty_string, a1, a2)
    | "==" => EQEQ (ty_string, a1, a2)
    | ">" => GT (ty_string, a1, a2)
    | ">=" => GEQ (ty_string, a1, a2)
    | ">>" => RIGHT (ty_string, a1, a2)
    | ">>=" => RIGHT_ASSIGN (ty_string, a1, a2)
    | "?" => QUESTION (ty_string, a1, a2)
    | "[" => LBRACK (ty_string, a1, a2)
    | "]" => RBRACK (ty_string, a1, a2)
    | "^" => HAT (ty_string, a1, a2)
    | "^=" => XOR_ASSIGN (ty_string, a1, a2)
    | "_Alignas" => ALIGNAS (ty_string, a1, a2)
    | "_Alignof" => ALIGNOF (ty_string, a1, a2)
    | "_Atomic" => ATOMIC (ty_string, a1, a2)
    | "_Bool" => BOOL (ty_string, a1, a2)
    | "_Complex" => COMPLEX (ty_string, a1, a2)
    | "_Generic" => GENERIC (ty_string, a1, a2)
    | "_Imaginary" => IMAGINARY (ty_string, a1, a2)
    | "_Noreturn" => NORETURN (ty_string, a1, a2)
    | "_Static_assert" => STATIC_ASSERT (ty_string, a1, a2)
    | "_Thread_local" => THREAD_LOCAL (ty_string, a1, a2)
    | "auto" => AUTO (ty_string, a1, a2)
    | "break" => BREAK (ty_string, a1, a2)
    | "case" => CASE (ty_string, a1, a2)
    | "char" => CHAR (ty_string, a1, a2)
    | "const" => CONST (ty_string, a1, a2)
    | "continue" => CONTINUE (ty_string, a1, a2)
    | "default" => DEFAULT (ty_string, a1, a2)
    | "do" => DO (ty_string, a1, a2)
    | "double" => DOUBLE (ty_string, a1, a2)
    | "else" => ELSE (ty_string, a1, a2)
    | "enum" => ENUM (ty_string, a1, a2)
    | "extern" => EXTERN (ty_string, a1, a2)
    | "float" => FLOAT (ty_string, a1, a2)
    | "for" => FOR (ty_string, a1, a2)
    | "goto" => GOTO (ty_string, a1, a2)
    | "if" => IF (ty_string, a1, a2)
    | "inline" => INLINE (ty_string, a1, a2)
    | "int" => INT (ty_string, a1, a2)
    | "long" => LONG (ty_string, a1, a2)
    | "register" => REGISTER (ty_string, a1, a2)
    | "restrict" => RESTRICT (ty_string, a1, a2)
    | "return" => RETURN (ty_string, a1, a2)
    | "short" => SHORT (ty_string, a1, a2)
    | "signed" => SIGNED (ty_string, a1, a2)
    | "sizeof" => SIZEOF (ty_string, a1, a2)
    | "static" => STATIC (ty_string, a1, a2)
    | "struct" => STRUCT (ty_string, a1, a2)
    | "switch" => SWITCH (ty_string, a1, a2)
    | "typedef" => TYPEDEF (ty_string, a1, a2)
    | "union" => UNION (ty_string, a1, a2)
    | "unsigned" => UNSIGNED (ty_string, a1, a2)
    | "void" => VOID (ty_string, a1, a2)
    | "volatile" => VOLATILE (ty_string, a1, a2)
    | "while" => WHILE (ty_string, a1, a2)
    | "{" => LBRACE (ty_string, a1, a2)
    | "|" => BAR (ty_string, a1, a2)
    | "|=" => OR_ASSIGN (ty_string, a1, a2)
    | "||" => BARBAR (ty_string, a1, a2)
    | "}" => RBRACE (ty_string, a1, a2)
    | "~" => TILDE (ty_string, a1, a2)
    | _ => error
end
end
\<close>

end
