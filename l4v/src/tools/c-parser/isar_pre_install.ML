(*
 * Portions Copyright 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 * Portions Copyright 2017-2018 Virginia Tech, USA
 * Portions Copyright 2016-2017 Nanyang Technological University, Singapore
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature ISAR_PRE_INSTALL =
sig
  val of_c_ast : C_Ast.ext_decl list -> StmtDecl.ext_decl list
  val mk_thy_relative' : (theory -> Token.file) -> theory -> Token.file * string
  val parse_files' : string -> theory -> Token.file
end

structure IsarPreInstall : ISAR_PRE_INSTALL =
struct
  structure M = C_Ast
  val To_string0 = String.implode o M.to_list
  val of_StringCvt_radix = M.rec_StringCvt_radix StringCvt.BIN StringCvt.OCT StringCvt.DEC StringCvt.HEX
  fun of_Unsynchronized_ref f x = Unsynchronized.ref (M.rec_Unsynchronized_ref f x)
  val of_SourcePos = M.rec_SourcePos (fn c => fn f => fn l => SourcePos.make {column = c, file = To_string0 f, line = l})
  val of_Region = M.rec_Region Region.bogus (fn left => fn right => Region.make {left = of_SourcePos left, right = of_SourcePos right})
  fun of_Region_Wrap f = M.rec_Region_Wrap (fn node => fn region => Region.Wrap.makeRegion (f node, of_Region region))
  val of_base_intttype = M.rec_base_inttype BaseCTypes.Char BaseCTypes.Short BaseCTypes.Int BaseCTypes.Long BaseCTypes.LongLong (* FIXME -> *) BaseCTypes.Char BaseCTypes.Char
  fun of_ctype f = M.rec_ctype (CType.Signed o of_base_intttype) (CType.Unsigned o of_base_intttype) CType.Bool CType.PlainChar (CType.StructTy o To_string0) (* FIXME -> *) (CType.StructTy o To_string0)
                                                                                                                                               (CType.EnumTy o Option.map To_string0) (K (CType.Ptr o I)) (K (fn opt => fn r => CType.Array (r, Option.map f opt))) (fn b => fn c => CType.Bitfield (b, f c)) (CType.Ident o To_string0) (K (fn l => fn c => CType.Function (c, map snd l))) CType.Void
  val of_more_info = M.rec_more_info (fn s => fn opt => MungedVar {munge = MString.mk (To_string0 s), owned_by = Option.map To_string0 opt}) EnumC FunctionName
  val of_literalconstant_node = M.rec_literalconstant_node (fn i => fn s => fn b => ExprDatatype.NUMCONST {value = i, suffix = To_string0 s, base = of_StringCvt_radix b}) (ExprDatatype.STRING_LIT o To_string0)
  val of_literalconstant = of_Region_Wrap of_literalconstant_node
  val of_binoptype =
    let open ExprDatatype in 
    M.rec_binoptype LogOr LogAnd Equals NotEquals BitwiseAnd BitwiseOr
                   BitwiseXOr
                   Lt Gt Leq Geq Plus Minus Times Divides Modulus
                   RShift LShift
    end
  val of_unoptype = 
    let open ExprDatatype in 
    M.rec_unoptype Negate Not Addr BitNegate
    end
  val of_var_info = of_Unsynchronized_ref (Option.map (fn (c, m) => (of_ctype I c, of_more_info m)))
  local
    open ExprDatatype
    val f0 = fn b => fn _ => fn _ => fn e1 => fn e2 => BinOp (of_binoptype b, e1, e2)
    val f1 = fn u => fn _ => fn e => UnOp (of_unoptype u, e)
    val f2 = fn _ => fn _ => fn _ => fn e1 => fn e2 => fn e3 => CondExp (e1, e2, e3)
    val f3 = Constant o of_literalconstant
    val f4 = fn s => fn v => Var (To_string0 s, of_var_info v)
    val f5 = fn _ => fn s => fn e => StructDot (e, To_string0 s)
    val f6 = fn _ => fn _ => fn e1 => fn e2 => ArrayDeref (e1, e2)
    val f7 = K Deref
    val f8 = fn w => fn _ => fn e => TypeCast (of_Region_Wrap (of_ctype snd) w, e)
    val f9 = K Sizeof
    val f10 = fn w => SizeofTy (of_Region_Wrap (of_ctype snd) w)
    val f11 = fn _ => fn l => fn e => EFnCall (e, map snd l)
    val f12 = fn c => fn l => CompLiteral (of_ctype snd c, map (M.map_prod (map snd) snd) l)
    val f13 = fn c => Arbitrary (of_ctype snd c)
    val f14 = K MKBOOL
    (* *)
    val f15 = fn w => E (of_Region_Wrap snd w)
    (* *)
    val f16 = K InitE
    val f17 = fn l => InitList (map (M.map_prod (map snd) snd) l)
    (* *)
    val f18 = K DesignE
    val f19 = DesignFld o To_string0
  in
    val of_expr = M.rec_expr
          f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
    val of_initializer = M.rec_initializer
          f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19
  end
  val of_gcc_attribute =
    let open StmtDecl in
      M.rec_gcc_attribute (GCC_AttribID o To_string0) (fn s => fn l => GCC_AttribFn (To_string0 s, map of_expr l)) (OWNED_BY o To_string0)
    end
  val of_fnspec =
    let open StmtDecl in
      M.rec_fnspec (fnspec o (of_Region_Wrap To_string0)) (relspec o (of_Region_Wrap To_string0)) (fn_modifies o map To_string0) didnt_translate (gcc_attribs o map of_gcc_attribute)
    end
  val of_storage_class = let open StmtDecl in M.rec_storage_class SC_EXTERN SC_STATIC SC_AUTO SC_REGISTER SC_THRD_LOCAL end
  val of_declaration = 
    let open StmtDecl in
      M.rec_declaration
        (fn (c,(w,(l1,(opt,l2)))) => VarDecl (of_ctype of_expr c, of_Region_Wrap To_string0 w, map of_storage_class l1, Option.map of_initializer opt, map of_gcc_attribute l2))
        (fn w => fn l => StructDecl (of_Region_Wrap To_string0 w, map (M.map_prod (of_ctype of_expr) (of_Region_Wrap To_string0)) l))
        (TypeDecl o map (M.map_prod (of_ctype of_expr) (of_Region_Wrap To_string0)))
        (fn r => fn n => fn p => fn s =>
          ExtFnDecl {rettype = of_ctype of_expr r, name = of_Region_Wrap To_string0 n, params = map (M.map_prod (of_ctype of_expr) (Option.map To_string0)) p, specs = map of_fnspec s})
        (fn w => fn l => EnumDecl (of_Region_Wrap (Option.map To_string0) w, map (M.map_prod (of_Region_Wrap To_string0) (Option.map of_expr)) l))
    end
  fun of_namedstringexp (opt, (s, e)) = (Option.map To_string0 opt, To_string0 s, of_expr e)
  fun of_asmblock e = {head = To_string0 (M.head e), mod1 = map of_namedstringexp (M.mod1 e), mod2 = map of_namedstringexp (M.mod2 e), mod3 = map To_string0 (M.mod3 e)}
  val of_trappable = let open StmtDecl in M.rec_trappable BreakT ContinueT end
  val of_block_item =   
    let open StmtDecl in
      M.rec_block_item 
        (fn e1 => fn e2 => Assign (of_expr e1, of_expr e2))
        (fn opt => fn e => fn l => AssignFnCall (Option.map of_expr opt, of_expr e, map of_expr l) )
        (Chaos o of_expr)
        (fn e1 => fn e2 => fn l => EmbFnCall (of_expr e1, of_expr e2, map of_expr l))
        (Block o map snd)
        (fn e => fn opt => fn _ => fn s => While (of_expr e, Option.map (of_Region_Wrap To_string0) opt, s))
        (fn t => fn _ => fn s => Trap (of_trappable t, s))
        (Return o Option.map of_expr)
        (fn e => fn l => ReturnFnCall (of_expr e, map of_expr l))
        Break
        Continue
        (fn e => fn _ => fn _ => fn s1 => fn s2 => IfStmt (of_expr e, s1, s2))
        (fn e => fn l => Switch (of_expr e, map (M.map_prod (map (Option.map of_expr)) (map snd)) l))
        EmptyStmt
        (Auxupd o To_string0)
        (Ghostupd o To_string0)
        (fn (ss, (l, s)) => Spec (M.map_prod To_string0 To_string0 ss, map snd l, To_string0 s))
        (fn b => fn a => AsmStmt {volatilep = b, asmblock = of_asmblock a})
        (LocalInit o of_expr)
        (* *)
        (StmtDeclDatatype.Stmt o of_Region_Wrap snd)
        (* *)
        (K BI_Stmt)
        (BI_Decl o of_Region_Wrap of_declaration)
    end
  val of_body = of_Region_Wrap (map of_block_item)
  val of_ext_decl = 
    let open StmtDecl in
      M.rec_ext_decl
        (fn (c,w) => fn l1 => fn l2 => fn b => FnDefn ((of_ctype of_expr c, of_Region_Wrap To_string0 w), map (M.map_prod (of_ctype of_expr) (of_Region_Wrap To_string0)) l1, map of_fnspec l2, of_body b))
        (Decl o of_Region_Wrap of_declaration)
    end
  val of_c_ast = map of_ext_decl

  fun mk_thy_relative' files thy =
    let
      val file as {src_path, lines, digest, pos}: Token.file = files thy
    in (file, Position.file_of pos |> the |> Path.explode |> File.full_path Path.current |> Path.implode) end

  fun parse_files' name thy =
    let
      val keywords = Thy_Header.get_keywords thy;
      val master_dir = Resources.master_directory thy;
      val pos = Position.none;
      val src_paths = Keyword.command_files keywords "install_C_file" (Path.explode name);
    in map (Command.read_file master_dir pos) src_paths |> hd end
end
