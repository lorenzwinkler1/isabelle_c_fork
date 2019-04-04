(* Generated from Run.thy; DO NOT EDIT! *)

structure C_ast : sig
  datatype inta = Int_of_integer of int
  datatype num = One | Bit0 of num | Bit1 of num
  val one_inta : inta
  type 'a one
  val one : 'a one -> 'a
  val one_int : inta one
  val integer_of_int : inta -> int
  val times_inta : inta -> inta -> inta
  type 'a times
  val times : 'a times -> 'a -> 'a -> 'a
  type 'a power
  val one_power : 'a power -> 'a one
  val times_power : 'a power -> 'a times
  val times_int : inta times
  val power_int : inta power
  type 'a equal
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
  val equal_lista : 'a equal -> 'a list -> 'a list -> bool
  val equal_list : 'a equal -> ('a list) equal
  val equal_char : char equal
  datatype nat = Nat of int
  val shows_prec_char : nat -> char -> char list -> char list
  val shows_string : char list -> char list -> char list
  val shows_list_char : char list -> char list -> char list
  type 'a show
  val shows_prec : 'a show -> nat -> 'a -> char list -> char list
  val shows_list : 'a show -> 'a list -> char list -> char list
  val show_char : char show
  datatype string_b_a_s_e = ST of string | STa of char list
  val equal_string_b_a_s_e : string_b_a_s_e -> string_b_a_s_e -> bool
  datatype abr_string = SS_base of string_b_a_s_e | String_concatWith of abr_string * abr_string list
  val equal_abr_stringa : abr_string -> abr_string -> bool
  val equal_abr_string : abr_string equal
  datatype sourcePos = Ta of int * abr_string * int
  val equal_SourcePos : sourcePos -> sourcePos -> bool
  datatype region = Bogus | T of sourcePos * sourcePos
  val equal_Region : region -> region -> bool
  datatype 'a region_Wrap = Tb of 'a * region
  val equal_Region_Wrap : 'a equal -> 'a region_Wrap -> 'a region_Wrap -> bool
  datatype stringCvt_radix = BIN | OCT | DEC | HEX
  datatype literalconstant_node = NUMCONST of int * abr_string * stringCvt_radix | STRING_LIT of abr_string
  datatype 'a unsynchronized_ref = Unsynchronized_ref of 'a
  datatype more_info = MungedVar of abr_string * abr_string option | EnumC | FunctionName
  datatype binoptype = LogOr | LogAnd | Equals | NotEquals | BitwiseAnd | BitwiseOr | BitwiseXOr | Lt | Gt | Leq | Geq | Plus | Minus | Times | Divides | Modulus | RShift | LShift
  datatype unoptype = Negate | Not | Addr | BitNegate
  datatype base_inttype = Char | Short | Int | Long | LongLong | Double | Float
  datatype 'a ctype = Signed of base_inttype | Unsigned of base_inttype | Bool | PlainChar | StructTy of abr_string | UnionTy of abr_string | EnumTy of abr_string option | Ptr of 'a ctype | Array of 'a ctype * 'a option |
    Bitfield of bool * 'a | Identa of abr_string | Function of 'a ctype * 'a ctype list | Void
  datatype expr = E of expr_node region_Wrap
  and designator = DesignE of expr | DesignFld of abr_string
  and initializer = InitE of expr | InitList of (designator list * initializer) list
  and expr_node = BinOp of binoptype * expr * expr | UnOp of unoptype * expr | CondExp of expr * expr * expr | Constant of literalconstant_node region_Wrap | Var of abr_string * ((int ctype * more_info) option) unsynchronized_ref |
    StructDot of expr * abr_string | ArrayDeref of expr * expr | Deref of expr | TypeCast of expr ctype region_Wrap * expr | Sizeof of expr | SizeofTy of expr ctype region_Wrap | EFnCall of expr * expr list |
    CompLiteral of expr ctype * (designator list * initializer) list | Arbitrary of expr ctype | MKBOOL of expr
  val equal_Unsynchronized_ref : 'a equal -> 'a unsynchronized_ref -> 'a unsynchronized_ref -> bool
  val equal_binoptype : binoptype -> binoptype -> bool
  val equal_unoptype : unoptype -> unoptype -> bool
  val equal_base_inttype : base_inttype -> base_inttype -> bool
  val equal_bool : bool -> bool -> bool
  val equal_optiona : 'a equal -> 'a option -> 'a option -> bool
  val equal_ctypea : 'a equal -> 'a ctype -> 'a ctype -> bool
  val equal_ctype : 'a equal -> 'a ctype equal
  val equal_StringCvt_radix : stringCvt_radix -> stringCvt_radix -> bool
  val equal_literalconstant_nodea : literalconstant_node -> literalconstant_node -> bool
  val equal_literalconstant_node : literalconstant_node equal
  val equal_integer : int equal
  val equal_proda : 'a equal -> 'b equal -> 'a * 'b -> 'a * 'b -> bool
  val equal_prod : 'a equal -> 'b equal -> ('a * 'b) equal
  val equal_more_infoa : more_info -> more_info -> bool
  val equal_more_info : more_info equal
  val equal_option : 'a equal -> ('a option) equal
  val equal_expr : expr equal
  val equal_expr_nodea : expr_node -> expr_node -> bool
  val equal_expr_node : expr_node equal
  val equal_expra : expr -> expr -> bool
  val equal_designatora : designator -> designator -> bool
  val equal_designator : designator equal
  val equal_initializera : initializer -> initializer -> bool
  val equal_initializer : initializer equal
  datatype 'a itself = Type
  type 'a len0
  val len_of : 'a len0 -> 'a itself -> nat
  val integer_of_nat : nat -> int
  val times_nat : nat -> nat -> nat
  type 'a ord
  val less_eq : 'a ord -> 'a -> 'a -> bool
  val less : 'a ord -> 'a -> 'a -> bool
  val max : 'a ord -> 'a -> 'a -> 'a
  val ord_integer : int ord
  val nat_of_integer : int -> nat
  type 'a finite
  datatype 'a bit0 = Abs_bit0 of inta
  val len_of_bit0 : 'a len0 -> 'a bit0 itself -> nat
  val len0_bit0 : 'a len0 -> 'a bit0 len0
  val one_nat : nat
  datatype num1 = One_num1
  val len_of_num1 : num1 itself -> nat
  val len0_num1 : num1 len0
  type 'a plus
  val plus : 'a plus -> 'a -> 'a -> 'a
  val plus_integer : int plus
  datatype gcc_attribute = GCC_AttribID of abr_string | GCC_AttribFn of abr_string * expr list | OWNED_BY of abr_string
  val equal_gcc_attributea : gcc_attribute -> gcc_attribute -> bool
  val equal_gcc_attribute : gcc_attribute equal
  datatype 'a word = Word of inta
  datatype ('b, 'a) alist = Alist of ('b * 'a) list
  datatype ('a, 'b) sum = Inl of 'a | Inr of 'b
  datatype fnspec = Fnspec of abr_string region_Wrap | Relspec of abr_string region_Wrap | Fn_modifies of abr_string list | Didnt_translate | Gcc_attribs of gcc_attribute list
  datatype asmblock = Asmblock of abr_string * (abr_string option * (abr_string * expr)) list * (abr_string option * (abr_string * expr)) list * abr_string list
  datatype storage_class = SC_EXTERN | SC_STATIC | SC_AUTO | SC_REGISTER | SC_THRD_LOCAL
  datatype declaration = VarDecl of (expr ctype * (abr_string region_Wrap * (storage_class list * (initializer option * gcc_attribute list)))) | StructDecl of abr_string region_Wrap * (expr ctype * abr_string region_Wrap) list |
    TypeDecl of (expr ctype * abr_string region_Wrap) list | ExtFnDecl of expr ctype * abr_string region_Wrap * (expr ctype * abr_string option) list * fnspec list |
    EnumDecl of (abr_string option) region_Wrap * (abr_string region_Wrap * expr option) list
  datatype trappable = BreakT | ContinueT
  datatype block_item = BI_Stmt of statement | BI_Decl of declaration region_Wrap
  and statement_node = Assign of expr * expr | AssignFnCall of expr option * expr * expr list | Chaos of expr | EmbFnCall of expr * expr * expr list | Block of block_item list | While of expr * abr_string region_Wrap option * statement
    | Trap of trappable * statement | Return of expr option | ReturnFnCall of expr * expr list | Break | Continue | IfStmt of expr * statement * statement | Switch of expr * ((expr option) list * block_item list) list | EmptyStmt |
    Auxupd of abr_string | Ghostupd of abr_string | Spec of ((abr_string * abr_string) * (statement list * abr_string)) | AsmStmt of bool * asmblock | LocalInit of expr
  and statement = Stmt of statement_node region_Wrap
  datatype ext_decl = FnDefn of (expr ctype * abr_string region_Wrap) * (expr ctype * abr_string region_Wrap) list * fnspec list * (block_item list) region_Wrap | Decl of declaration region_Wrap
  datatype name = Name0 of int
  datatype cChar = CChar0 of char * bool | CChars0 of char list * bool
  datatype 'a flags = Flags0 of int
  datatype position = Position0 of int * abr_string * int * int | NoPosition0 | BuiltinPosition0 | InternalPosition0
  datatype nodeInfo = OnlyPos0 of position * (position * int) | NodeInfo0 of position * (position * int) * name
  datatype ident = Ident0 of abr_string * int * nodeInfo
  datatype cFloat = CFloat0 of abr_string
  datatype sUERef = AnonymousRef0 of name | NamedRef0 of ident
  datatype ('a, 'b) either = Left of 'a | Right of 'b
  datatype 'a optiona = None | Some of 'a
  datatype ('a, 'b, 'c, 'd) struct_flat = Struct_root of 'a * 'b * (('a * 'c), 'd) sum list | Struct_leaf of (('a * 'b), 'd) sum
  datatype ('a, 'b, 'c, 'd) struct_tree = Struct_tree of 'a option * 'b * ((('a, 'b, 'c, 'd) struct_tree * 'c), 'd) sum list
  datatype cString = CString0 of abr_string * bool
  datatype commentFormat = SingleLine | MultiLine
  datatype comment = Comment of position * abr_string * commentFormat
  datatype ('a, 'b, 'c, 'd, 'e, 'f) declaration0 = VarDecl0 of 'a | StructDecl0_root of 'b | StructDecl0_child of 'c | TypeDecl0 of 'd | ExtFnDecl0 of 'e | EnumDecl0 of 'f
  datatype cIntFlag = FlagUnsigned0 | FlagLong0 | FlagLongLong0 | FlagImag0
  datatype cIntRepr = DecRepr0 | HexRepr0 | OctalRepr0
  datatype cInteger = CInteger0 of int * cIntRepr * cIntFlag flags
  datatype cUnaryOp = CPreIncOp0 | CPreDecOp0 | CPostIncOp0 | CPostDecOp0 | CAdrOp0 | CIndOp0 | CPlusOp0 | CMinOp0 | CCompOp0 | CNegOp0
  datatype parsing_style = Style_Haskell | Style_ML
  datatype cAssignOp = CAssignOp0 | CMulAssOp0 | CDivAssOp0 | CRmdAssOp0 | CAddAssOp0 | CSubAssOp0 | CShlAssOp0 | CShrAssOp0 | CAndAssOp0 | CXorAssOp0 | COrAssOp0
  datatype cBinaryOp = CMulOp0 | CDivOp0 | CRmdOp0 | CAddOp0 | CSubOp0 | CShlOp0 | CShrOp0 | CLeOp0 | CGrOp0 | CLeqOp0 | CGeqOp0 | CEqOp0 | CNeqOp0 | CAndOp0 | CXorOp0 | COrOp0 | CLndOp0 | CLorOp0
  datatype 'a cConstant = CIntConst0 of cInteger * 'a | CCharConst0 of cChar * 'a | CFloatConst0 of cFloat * 'a | CStrConst0 of cString * 'a
  datatype 'a cFunctionSpecifier = CInlineQual0 of 'a | CNoreturnQual0 of 'a
  datatype 'a cStorageSpecifier = CAuto0 of 'a | CRegister0 of 'a | CStatic0 of 'a | CExtern0 of 'a | CTypedef0 of 'a | CThread0 of 'a
  datatype cStructTag = CStructTag0 | CUnionTag0
  datatype 'a cStringLiteral = CStrLit0 of cString * 'a
  datatype 'a cArraySize = CNoArrSize0 of bool | CArrSize0 of bool * 'a cExpression
  and 'a cDerivedDeclarator = CPtrDeclr0 of 'a cTypeQualifier list * 'a | CArrDeclr0 of 'a cTypeQualifier list * 'a cArraySize * 'a | CFunDeclr0 of ((ident list), ('a cDeclaration list * bool)) either * 'a cAttribute list * 'a
  and 'a cDeclarator = CDeclr0 of ident optiona * 'a cDerivedDeclarator list * 'a cStringLiteral optiona * 'a cAttribute list * 'a
  and 'a cFunctionDef = CFunDef0 of 'a cDeclarationSpecifier list * 'a cDeclarator * 'a cDeclaration list * 'a cStatement * 'a
  and 'a cCompoundBlockItem = CBlockStmt0 of 'a cStatement | CBlockDecl0 of 'a cDeclaration | CNestedFunDef0 of 'a cFunctionDef
  and 'a cStatement = CLabel0 of ident * 'a cStatement * 'a cAttribute list * 'a | CCase0 of 'a cExpression * 'a cStatement * 'a | CCases0 of 'a cExpression * 'a cExpression * 'a cStatement * 'a | CDefault0 of 'a cStatement * 'a |
    CExpr0 of 'a cExpression optiona * 'a | CCompound0 of ident list * 'a cCompoundBlockItem list * 'a | CIf0 of 'a cExpression * 'a cStatement * 'a cStatement optiona * 'a | CSwitch0 of 'a cExpression * 'a cStatement * 'a |
    CWhile0 of 'a cExpression * 'a cStatement * bool * 'a | CFor0 of ('a cExpression optiona, 'a cDeclaration) either * 'a cExpression optiona * 'a cExpression optiona * 'a cStatement * 'a | CGoto0 of ident * 'a |
    CGotoPtr0 of 'a cExpression * 'a | CCont0 of 'a | CBreak0 of 'a | CReturn0 of 'a cExpression optiona * 'a | CAsm0 of 'a cAssemblyStatement * 'a
  and 'a cExpression = CComma0 of 'a cExpression list * 'a | CAssign0 of cAssignOp * 'a cExpression * 'a cExpression * 'a | CCond0 of 'a cExpression * 'a cExpression optiona * 'a cExpression * 'a |
    CBinary0 of cBinaryOp * 'a cExpression * 'a cExpression * 'a | CCast0 of 'a cDeclaration * 'a cExpression * 'a | CUnary0 of cUnaryOp * 'a cExpression * 'a | CSizeofExpr0 of 'a cExpression * 'a | CSizeofType0 of 'a cDeclaration * 'a
    | CAlignofExpr0 of 'a cExpression * 'a | CAlignofType0 of 'a cDeclaration * 'a | CComplexReal0 of 'a cExpression * 'a | CComplexImag0 of 'a cExpression * 'a | CIndex0 of 'a cExpression * 'a cExpression * 'a |
    CCall0 of 'a cExpression * 'a cExpression list * 'a | CMember0 of 'a cExpression * ident * bool * 'a | CVar0 of ident * 'a | CConst0 of 'a cConstant |
    CCompoundLit0 of 'a cDeclaration * ('a cPartDesignator list * 'a cInitializer) list * 'a | CGenericSelection0 of 'a cExpression * ('a cDeclaration optiona * 'a cExpression) list * 'a | CStatExpr0 of 'a cStatement * 'a |
    CLabAddrExpr0 of ident * 'a | CBuiltinExpr0 of 'a cBuiltinThing
  and 'a cAttribute = CAttr0 of ident * 'a cExpression list * 'a
  and 'a cTypeQualifier = CConstQual0 of 'a | CVolatQual0 of 'a | CRestrQual0 of 'a | CAtomicQual0 of 'a | CAttrQual0 of 'a cAttribute | CNullableQual0 of 'a | CNonnullQual0 of 'a
  and 'a cEnumeration = CEnum0 of ident optiona * ((ident * 'a cExpression optiona) list) optiona * 'a cAttribute list * 'a
  and 'a cPartDesignator = CArrDesig0 of 'a cExpression * 'a | CMemberDesig0 of ident * 'a | CRangeDesig0 of 'a cExpression * 'a cExpression * 'a
  and 'a cInitializer = CInitExpr0 of 'a cExpression * 'a | CInitList0 of ('a cPartDesignator list * 'a cInitializer) list * 'a
  and 'a cAssemblyOperand = CAsmOperand0 of ident optiona * 'a cStringLiteral * 'a cExpression * 'a
  and 'a cAssemblyStatement = CAsmStmt0 of 'a cTypeQualifier optiona * 'a cStringLiteral * 'a cAssemblyOperand list * 'a cAssemblyOperand list * 'a cStringLiteral list * 'a
  and 'a cAlignmentSpecifier = CAlignAsType0 of 'a cDeclaration * 'a | CAlignAsExpr0 of 'a cExpression * 'a
  and 'a cDeclarationSpecifier = CStorageSpec0 of 'a cStorageSpecifier | CTypeSpec0 of 'a cTypeSpecifier | CTypeQual0 of 'a cTypeQualifier | CFunSpec0 of 'a cFunctionSpecifier | CAlignSpec0 of 'a cAlignmentSpecifier
  and 'a cDeclaration = CDecl0 of 'a cDeclarationSpecifier list * (('a cDeclarator optiona * 'a cInitializer optiona) * 'a cExpression optiona) list * 'a | CStaticAssert0 of 'a cExpression * 'a cStringLiteral * 'a
  and 'a cBuiltinThing = CBuiltinVaArg0 of 'a cExpression * 'a cDeclaration * 'a | CBuiltinOffsetOf0 of 'a cDeclaration * 'a cPartDesignator list * 'a | CBuiltinTypesCompatible0 of 'a cDeclaration * 'a cDeclaration * 'a
  and 'a cStructureUnion = CStruct0 of cStructTag * ident optiona * ('a cDeclaration list) optiona * 'a cAttribute list * 'a
  and 'a cTypeSpecifier = CVoidType0 of 'a | CCharType0 of 'a | CShortType0 of 'a | CIntType0 of 'a | CLongType0 of 'a | CFloatType0 of 'a | CDoubleType0 of 'a | CSignedType0 of 'a | CUnsigType0 of 'a | CBoolType0 of 'a |
    CComplexType0 of 'a | CInt128Type0 of 'a | CSUType0 of 'a cStructureUnion * 'a | CEnumType0 of 'a cEnumeration * 'a | CTypeDef0 of ident * 'a | CTypeOfExpr0 of 'a cExpression * 'a | CTypeOfType0 of 'a cDeclaration * 'a |
    CAtomicType0 of 'a cDeclaration * 'a
  datatype clangCVersion = ClangCVersion0 of abr_string
  datatype 'a cExternalDeclaration = CDeclExt0 of 'a cDeclaration | CFDefExt0 of 'a cFunctionDef | CAsmExt0 of 'a cStringLiteral * 'a
  datatype 'a cTranslationUnit = CTranslUnit0 of 'a cExternalDeclaration list * 'a
  datatype 'a comment_type = Invariant of char list | Fnspeca of (char list * char list) list | Relspeca of char list | Modifies of ((char list) option) list | Dont_translate | Auxupda of char list | Ghostupda of char list |
    Speca of (char list * char list) | End_spec of char list | Calls of ((char list) option) list | Owned_by of char list | OTHER of 'a
  val id : 'a -> 'a
  val plus_nat : nat -> nat -> nat
  val suc : nat -> nat
  val minus_nat : nat -> nat -> nat
  val equal_nat : nat -> nat -> bool
  val zero_nat : nat
  val nth : 'a list -> nat -> 'a
  val fold : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev : 'a list -> 'a list
  val zip : 'a list -> 'b list -> ('a * 'b) list
  val app_rev : 'a -> ('a -> 'b) -> 'b
  val current_parsing_style : parsing_style
  val mapa : ('a -> 'b) -> 'a list -> 'b list
  val function_definition_params0 : ('a cDeclaration -> 'b) -> 'a cDeclaration list -> 'b list
  val flatten : abr_string list -> abr_string
  val ident_struct_type0 : abr_string -> abr_string
  val less_eq_nat : nat -> nat -> bool
  val foldl : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
  val foldl_one : ('a -> char -> 'a) -> 'a -> string -> 'a
  val foldlb : ('a -> char -> 'a) -> 'a -> string_b_a_s_e -> 'a
  val foldla : ('a -> char -> 'a) -> 'a -> abr_string -> 'a
  val to_list : abr_string -> char list
  val length : abr_string -> nat
  val pref_ident : abr_string -> abr_string
  val ident_struct_type : ident -> abr_string
  val decl_spec_ty_tag : cStructTag -> abr_string -> 'a ctype
  val map_option : ('a -> 'b) -> 'a optiona -> 'b option
  val ident : ident -> abr_string
  val ident_option : ident optiona -> abr_string option
  val map_filter : ('a -> 'b option) -> 'a list -> 'b list
  val identb : ident -> 'a ctype
  val takeWhile : ('a -> bool) -> 'a list -> 'a list
  val dropWhile : ('a -> bool) -> 'a list -> 'a list
  val groupBy : ('a -> 'a -> bool) -> 'a list -> ('a list) list
  val tl : 'a list -> 'a list
  val hd : 'a list -> 'a
  val decl_spec_ty : 'a cDeclarationSpecifier list -> 'b ctype
  val ident_struct_const : ident -> abr_string
  val not_yet_supported : abr_string -> unit
  val map_prod : ('a -> 'b) -> ('c -> 'd) -> 'a * 'c -> 'b * 'd
  val bogus : sourcePos
  val comp2 : ('a -> 'b) -> ('c -> 'd -> 'a) -> 'c -> 'd -> 'b
  val wrap : 'a -> sourcePos -> sourcePos -> 'a region_Wrap
  val bogwrap : 'a -> 'a region_Wrap
  val ebogwrap : expr_node -> expr
  val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val show_intFlag : cIntFlag -> abr_string
  val sgn_integer : int -> int
  val apsnd : ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val divmod_integer : int -> int -> int * int
  val snd : 'a * 'b -> 'b
  val modulo_integer : int -> int -> int
  val modulo_int : inta -> inta -> inta
  val power : 'a power -> 'a -> nat -> 'a
  val word_of_int : 'a len0 -> inta -> 'a word
  val foldr : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val concat : ('a list) list -> 'a list
  val fst : 'a * 'b -> 'a
  val divide_integer : int -> int -> int
  val divide_int : inta -> inta -> inta
  val bin_rest : inta -> inta
  val equal_int : inta -> inta -> bool
  val bin_last : inta -> bool
  val bin_to_bl_aux : nat -> inta -> bool list -> bool list
  val bin_to_bl : nat -> inta -> bool list
  val uint : 'a len0 -> 'a word -> inta
  val to_bl : 'a len0 -> 'a word -> bool list
  val constant : 'a cConstant -> literalconstant_node region_Wrap
  val binaryOp : cBinaryOp -> binoptype
  val unaryOp : cUnaryOp -> unoptype
  val deriv_decl_spec : 'a cDerivedDeclarator list -> 'a cDeclarationSpecifier list -> expr ctype
  val expression0 : 'a cExpression -> expr_node
  val expression : 'a cExpression -> expr
  val partDesignator : 'a cPartDesignator -> designator
  val initializerList : ('a cPartDesignator list * 'a cInitializer) list -> (designator list * initializer) list
  val initializer0 : ('a cExpression -> 'a cExpression) -> 'a cInitializer -> initializer
  val initializer : 'a cInitializer -> initializer
  val deriv_decl_spec0 : 'a cDerivedDeclarator list -> expr ctype -> expr ctype
  val function_definition_params : (abr_string -> 'a) -> 'b cDeclaration list -> (expr ctype * 'a) list
  val p_first_of_NodeInfo : nodeInfo -> position * int
  val p_last_of_NodeInfo : nodeInfo -> position * int
  val pos_of_CFunDef : 'a cFunctionDef -> 'a
  val pos_of_CStat : 'a cStatement -> 'a
  val pos_of_CDecl : 'a cDeclaration -> 'a
  val pos_of_CBlockItem : 'a cCompoundBlockItem -> 'a
  val map_comment_type : ('a -> 'b) -> 'a comment_type -> 'b comment_type
  val catch_error : ('a, 'b) sum -> ('a -> ('c, 'b) sum) -> ('c, 'b) sum
  val or : ('a -> ('b, 'c) sum) -> ('a -> ('d, 'c) sum) -> 'a -> ('d, 'c) sum
  val returna : 'a -> 'b list -> ((char list), ('a * 'b list)) sum
  val binda : ('a, 'b) sum -> ('b -> ('a, 'c) sum) -> ('a, 'c) sum
  val bindb : ('a list -> ((char list), ('b * 'a list)) sum) -> ('b -> 'a list -> ((char list), ('c * 'a list)) sum) -> 'a list -> ((char list), ('c * 'a list)) sum
  val many_c_a_t_c_h_a_l_l_aux : 'a list -> ('b list -> ((char list), ('a * 'b list)) sum) -> 'b list -> ((char list), ('a list * 'b list)) sum
  val many_c_a_t_c_h_a_l_l : ('a list -> ((char list), ('b * 'a list)) sum) -> 'a list -> ((char list), ('b list * 'a list)) sum
  val map_sum : ('a -> 'b) -> ('c -> 'd) -> ('a, 'c) sum -> ('b, 'd) sum
  val bind2 : ('a, ('b * 'c)) sum -> ('b -> 'd) -> ('a, ('d * 'c)) sum
  val bind3 : ('a -> ('b, ('c * 'd)) sum) -> ('c -> 'e) -> 'a -> ('b, ('e * 'd)) sum
  val scan_upto_b_i_n_d : ('a list -> ('b, ('c * 'a list)) sum) -> 'a list -> ((char list), (('a list * 'c) * 'a list)) sum
  val errorb : char list -> 'a list -> ((char list), ('b * 'a list)) sum
  val oneof_b_i_n_d : ('a list -> ((char list), ('b * 'a list)) sum) list -> 'a list -> ((char list), ('b * 'a list)) sum
  val bind_k : ('a -> ('b, ('c * 'd)) sum) -> 'e -> 'a -> ('b, ('e * 'd)) sum
  val shows_prec_list : 'a show -> nat -> 'a list -> char list -> char list
  val shows_quote : (char list -> char list) -> char list -> char list
  val take : nat -> 'a list -> 'a list
  val err_expecting : 'a show -> char list -> 'a list -> ((char list), ('b * 'a list)) sum
  val exactly_aux : 'a equal * 'a show -> char list -> 'a list -> 'a list -> 'a list -> ((char list), (char list * 'a list)) sum
  val exactly : char list -> char list -> ((char list), (char list * char list)) sum
  val many : (char -> bool) -> char list -> ((char list), (char list * char list)) sum
  val many1 : (char -> bool) -> char list -> ((char list), (char list * char list)) sum
  val member : 'a equal -> 'a list -> 'a -> bool
  val manyof1 : char list -> char list -> ((char list), (char list * char list)) sum
  val stars1 : char list -> ((char list), (char list * char list)) sum
  val end_comment : char list -> ((char list), (char list * char list)) sum
  val parse_id_m_a_y_b_e : (char list) list -> char list -> ((char list), ((char list * (char list) option) * char list)) sum
  val parse_id_o_n_e : (char list) list -> char list -> ((char list), (char list * char list)) sum
  val many_m_a_x_aux : 'a list -> ('b list -> ((char list), ('a * 'b list)) sum) -> 'b list -> ((char list), ('a list * 'b list)) sum
  val many_m_a_x : ('a list -> ((char list), ('b * 'a list)) sum) -> 'a list -> ((char list), ('b list * 'a list)) sum
  val parse_id_list : (char list) list -> char list -> ((char list), (((char list) option) list * char list)) sum
  val in_safe_monad : ('a -> ('b, 'c) sum) -> 'a -> 'c
  val parse_str_aux : (char list) list -> char list -> ((char list), (char list * char list)) sum
  val parse_str : char list -> ((char list), (char list * char list)) sum
  val shows_sep : ('a -> char list -> char list) -> (char list -> char list) -> 'a list -> char list -> char list
  val null : 'a list -> bool
  val shows_list_gen : ('a -> char list -> char list) -> char list -> char list -> char list -> char list -> 'a list -> char list -> char list
  val showsp_list : (nat -> 'a -> char list -> char list) -> nat -> 'a list -> char list -> char list
  val shows_list_list : 'a show -> ('a list) list -> char list -> char list
  val gen_length : nat -> 'a list -> nat
  val size_list : 'a list -> nat
  val trim : char list -> char list
  val drop : nat -> 'a list -> 'a list
  val oneof_aux : (char list) list -> (char list) list -> char list -> ((char list), (char list * char list)) sum
  val oneof : (char list) list -> char list -> ((char list), (char list * char list)) sum
  val eoi : 'a show -> 'a list -> ((char list), (unit * 'a list)) sum
  val parse_commenta : char list -> ((char list), ((char list) comment_type list * char list)) sum
  val string_implode : char list -> abr_string
  val errora : abr_string -> 'a
  val parse_comment : comment -> abr_string comment_type list
  val sbogwrap : statement_node -> statement
  val filter_statement : comment list -> (block_item, ((abr_string * abr_string), abr_string) sum) sum list
  val impl_of : ('b, 'a) alist -> ('b * 'a) list
  val map_of : 'a equal -> ('a * 'b) list -> 'a -> 'b option
  val lookup : 'a equal -> ('a, 'b) alist -> 'a -> 'b option
  val lookupa : 'a equal -> ('a, 'b) alist -> 'a -> 'b option
  val get_column : 'a equal -> 'b plus * 'b ord -> ('a, (('b * 'b) list)) alist -> 'a -> 'b -> 'b
  val pos_in_interval_haskell : ((abr_string * int), ((int * int) list)) alist -> (position * int) * (position * int) -> position -> bool
  val pos_in_interval_ml : 'a -> (position * int) * (position * int) -> position -> bool
  val pos_in_interval : ((abr_string * int), ((int * int) list)) alist -> (position * int) * (position * int) -> position -> bool
  val partition : ('a -> bool) -> 'a list -> 'a list * 'a list
  val comment_interval : comment list * ((abr_string * int), ((int * int) list)) alist -> (position * int) * (position * int) -> comment list
  val return : 'a -> 'b -> 'b * 'a
  val bind : ('a -> 'b * 'c) -> ('c -> 'b -> 'd) -> 'a -> 'd
  val foldM_o : ('a -> 'b -> 'b * 'c) -> 'a optiona -> 'b -> 'b * 'c optiona
  val unsupported : abr_string -> 'a -> 'a * nodeInfo cExpression
  val foldM : ('a -> 'b -> 'b * 'c) -> 'a list -> 'b -> 'b * 'c list
  val stmt_out_of_expr : nodeInfo cExpression -> 'a -> 'a * nodeInfo cExpression
  val stmt_out_of_expra : nodeInfo cExpression -> nodeInfo cExpression
  val map_optiona : ('a -> 'b) -> 'a option -> 'b option
  val maps : ('a -> 'b list) -> 'a list -> 'b list
  val filter_gen : (abr_string comment_type -> (char list) option) -> (abr_string -> 'a) -> comment list -> 'a option
  val filter_owned_by : comment list -> gcc_attribute option
  val tree_of_decl_spec :
    'a cStructureUnion ->
      (abr_string, (cStructTag * ('a cDeclaration list * ('a cAttribute list * 'a))), (cStructTag * (('a cDeclarator optiona * 'a cInitializer optiona) * 'a cExpression optiona) list),
        ('a cDeclarationSpecifier list * (('a cDeclarator optiona * 'a cInitializer optiona) * 'a cExpression optiona) list))
        struct_tree
  val fresh_ident : unit -> abr_string
  val concat_map : ('a -> 'b list) -> 'a list -> 'b list
  val struct_conv : (abr_string, 'a, 'b, 'c) struct_tree -> abr_string * (abr_string, 'a, 'b, 'c) struct_flat list
  val list_ex : ('a -> bool) -> 'a list -> bool
  val extract : ('a -> bool) -> 'a list -> ('a list * ('a * 'a list)) option
  val decl_spec0 :
    'a cDeclarationSpecifier list ->
      ((nodeInfo cDeclarator optiona * 'b) * 'c) list * (position * int) ->
        ((ident optiona * ('d ctype option * (nodeInfo cDerivedDeclarator list * ('b * ((position * int) * ((position * int) * nodeInfo cAttribute list)))))),
          (abr_string *
            ((cStructTag * ('a cDeclaration list * ('a cAttribute list * 'a))) *
              ((abr_string * (cStructTag * (('a cDeclarator optiona * 'a cInitializer optiona) * 'a cExpression optiona) list)),
                ('a cDeclarationSpecifier list * (('a cDeclarator optiona * 'a cInitializer optiona) * 'a cExpression optiona) list))
                sum list)),
          (abr_string * (cStructTag * ('a cDeclaration list * ('a cAttribute list * 'a)))), (ident optiona * ('d ctype option * nodeInfo cDerivedDeclarator list)),
          (ident optiona * (nodeInfo cDerivedDeclarator list * ((((ident list), (nodeInfo cDeclaration list * bool)) either * (nodeInfo cAttribute list * nodeInfo)) * (nodeInfo cDerivedDeclarator list * nodeInfo cAttribute list)))),
          ((abr_string option) region_Wrap * (abr_string * expr option) list))
          declaration0 list
  val identa : ident -> abr_string
  val attrs0 : nodeInfo cAttribute -> gcc_attribute
  val empty : ('a, 'b) alist
  val emptya : ('a, 'b) alist
  val update : 'a equal -> 'a -> 'b -> ('a * 'b) list -> ('a * 'b) list
  val updatea : 'a equal -> 'a -> 'b -> ('a, 'b) alist -> ('a, 'b) alist
  val insert : 'a equal -> 'a -> 'b -> ('a, 'b) alist -> ('a, 'b) alist
  val union_loada : 'a equal -> 'a list -> bool * ('a list * ('a, unit) alist) -> bool * ('a list * ('a, unit) alist)
  val entries : ('a, 'b) alist -> ('a * 'b) list
  val is_empty : ('a, 'b) alist -> bool
  val keys_emptya : ('a list -> 'b) -> bool * ('a list * ('c, 'd) alist) -> 'b list
  val bulkload : 'a equal -> ('a * 'b) list -> ('a, 'b) alist
  val folda : ('a -> 'b -> 'c -> 'c) -> ('a, 'b) alist -> 'c -> 'c
  val union : 'a equal -> ('a, 'b) alist -> ('a, 'b) alist -> ('a, 'b) alist
  val union_load : 'a equal -> 'a list -> 'b * ('a, unit) alist -> bool * ('a, unit) alist
  val keys : ('a, 'b) alist -> 'a list
  val keys_empty : ('a list -> 'b) -> bool * ('a, 'c) alist -> 'b list
  val collapse_mod_attribs : fnspec list -> fnspec list
  val filter_fnspec : comment list -> fnspec list
  val attrs : nodeInfo cDeclarationSpecifier list ->
                nodeInfo cDerivedDeclarator list -> nodeInfo cAttribute list -> ((comment list * ((abr_string * int), ((int * int) list)) alist) * (position * int) option) * (position * int) -> fnspec list
  val decl_spec :
    nodeInfo cDeclarationSpecifier list ->
      ((nodeInfo cDeclarator optiona * nodeInfo cInitializer optiona) * 'a) list * (position * int) -> ((comment list * ((abr_string * int), ((int * int) list)) alist) * (position * int) option) * (position * int) -> declaration list
  val declaration : (comment list * ((abr_string * int), ((int * int) list)) alist) * (position * int) option -> (declaration region_Wrap -> 'a) -> nodeInfo cDeclaration -> 'a list
  val equal_CAssignOp : cAssignOp -> cAssignOp -> bool
  val statement_of_expression_CAssign_fun : 'a cExpression -> bool
  val binoptype_of_CAssignOp : cAssignOp -> binoptype option
  val statement_of_expression_CAssign : cAssignOp -> nodeInfo cExpression -> nodeInfo cExpression -> statement_node
  val list_all : ('a -> bool) -> 'a list -> bool
  val expr_int : int -> expr
  val statement_node_of_expression : nodeInfo cExpression -> statement_node
  val filter_auxupd : comment list -> statement_node option
  val pos_of_CBuiltin : 'a cBuiltinThing -> 'a
  val pos_of_CConst : 'a cConstant -> 'a
  val pos_of_CExpr : 'a cExpression -> 'a
  val statement_node_of_expressiona : nodeInfo cExpression optiona -> (nodeInfo * (comment list * ((abr_string * int), ((int * int) list)) alist)) option -> statement_node
  val remove_last_break : 'a cStatement -> 'a cStatement option
  val statement0_case : 'a cExpression list -> 'a cStatement -> bool * ('a cExpression list * 'a cStatement)
  val statement_Switch : 'a -> (nodeInfo cCompoundBlockItem list -> (position * int) * (position * int) -> block_item list) -> 'b cExpression -> nodeInfo cCompoundBlockItem list -> nodeInfo -> statement_node
  val filter_invariant : comment list -> abr_string region_Wrap option
  val statement_While : nodeInfo cExpression -> statement * nodeInfo -> bool -> nodeInfo * (comment list * ((abr_string * int), ((int * int) list)) alist) -> statement_node
  val flattena : abr_string -> abr_string -> abr_string
  val map : ('a -> 'b) -> 'a list -> 'b list
  val replace_chars : (char -> abr_string) -> abr_string -> string option -> abr_string -> abr_string
  val map_gena : (abr_string -> string option -> abr_string -> abr_string) -> (char -> abr_string) -> string_b_a_s_e -> abr_string
  val map_gen : (abr_string -> string option -> abr_string -> abr_string) -> (char -> abr_string) -> abr_string -> abr_string
  val replace_charsa : (char -> abr_string) -> abr_string -> abr_string
  val stringLiteral : 'a cStringLiteral -> abr_string
  val assemblyOperand : 'a cAssemblyOperand list -> (abr_string option * (abr_string * expr)) list
  val statement_For :
    (nodeInfo cExpression optiona, nodeInfo cDeclaration) either ->
      nodeInfo cExpression optiona -> nodeInfo cExpression optiona -> statement * nodeInfo -> nodeInfo * (comment list * ((abr_string * int), ((int * int) list)) alist) -> statement_node
  val statement_If : ('a -> statement) -> 'b cExpression -> 'a -> 'a optiona -> statement_node
  val group_spec_aux1 : (block_item list) list -> ((block_item list), (((abr_string * abr_string), abr_string) sum list)) sum list -> block_item list
  val group_spec_aux2 : (block_item list) list -> abr_string * abr_string -> block_item list -> abr_string -> ((block_item list), (((abr_string * abr_string), abr_string) sum list)) sum list -> block_item list
  val group_spec : (block_item, ((abr_string * abr_string), abr_string) sum) sum list -> block_item list
  val block_item_list0a : comment list * ((abr_string * int), ((int * int) list)) alist -> nodeInfo cCompoundBlockItem list -> nodeInfo -> block_item list
  val statement0 : comment list * ((abr_string * int), ((int * int) list)) alist -> nodeInfo cStatement -> statement
  val block_item_list0 : comment list * ((abr_string * int), ((int * int) list)) alist -> nodeInfo cCompoundBlockItem list -> (position * int) * (position * int) -> block_item list
  val comp3 : ('a -> 'b) -> ('c -> 'd -> 'e -> 'a) -> 'c -> 'd -> 'e -> 'b
  val block_item_list : comment list * ((abr_string * int), ((int * int) list)) alist -> nodeInfo cCompoundBlockItem list -> nodeInfo -> (block_item list) region_Wrap
  val function_definition : (comment list * ((abr_string * int), ((int * int) list)) alist) * (position * int) option -> nodeInfo cFunctionDef -> ext_decl
  val external_declaration : (comment list * ((abr_string * int), ((int * int) list)) alist) * (position * int) option -> nodeInfo cExternalDeclaration -> ext_decl list
  val pos_of_CExtDecl : 'a cExternalDeclaration -> 'a
  val mapb : 'a equal -> ('a -> 'b -> 'c) -> ('a, 'b) alist -> ('a, 'c) alist
  val translation_unit : nodeInfo cTranslationUnit * (comment list * int list) -> ext_decl list
  val main : nodeInfo cTranslationUnit * (comment list * int list) -> ext_decl list
  val cIf : 'a cExpression -> 'a cStatement -> 'a cStatement optiona -> 'a -> 'a cStatement
  val cAsm : 'a cAssemblyStatement -> 'a -> 'a cStatement
  val cFor : ('a cExpression optiona, 'a cDeclaration) either -> 'a cExpression optiona -> 'a cExpression optiona -> 'a cStatement -> 'a -> 'a cStatement
  val cVar : ident -> 'a -> 'a cExpression
  val name : int -> name
  val cAttr : ident -> 'a cExpression list -> 'a -> 'a cAttribute
  val cAuto : 'a -> 'a cStorageSpecifier
  val cCall : 'a cExpression -> 'a cExpression list -> 'a -> 'a cExpression
  val cCase : 'a cExpression -> 'a cStatement -> 'a -> 'a cStatement
  val cCast : 'a cDeclaration -> 'a cExpression -> 'a -> 'a cExpression
  val cChar : char -> bool -> cChar
  val cCond : 'a cExpression -> 'a cExpression optiona -> 'a cExpression -> 'a -> 'a cExpression
  val cCont : 'a -> 'a cStatement
  val cDecl : 'a cDeclarationSpecifier list -> (('a cDeclarator optiona * 'a cInitializer optiona) * 'a cExpression optiona) list -> 'a -> 'a cDeclaration
  val cEnum : ident optiona -> ((ident * 'a cExpression optiona) list) optiona -> 'a cAttribute list -> 'a -> 'a cEnumeration
  val cEqOp : cBinaryOp
  val cExpr : 'a cExpression optiona -> 'a -> 'a cStatement
  val cGoto : ident -> 'a -> 'a cStatement
  val cGrOp : cBinaryOp
  val cLeOp : cBinaryOp
  val cOrOp : cBinaryOp
  val flags : int -> 'a flags
  val identc : abr_string -> int -> nodeInfo -> ident
  val cAddOp : cBinaryOp
  val cAdrOp : cUnaryOp
  val cAndOp : cBinaryOp
  val cBreak : 'a -> 'a cStatement
  val cCases : 'a cExpression -> 'a cExpression -> 'a cStatement -> 'a -> 'a cStatement
  val cChars : char list -> bool -> cChar
  val cComma : 'a cExpression list -> 'a -> 'a cExpression
  val cConst : 'a cConstant -> 'a cExpression
  val cDeclr : ident optiona -> 'a cDerivedDeclarator list -> 'a cStringLiteral optiona -> 'a cAttribute list -> 'a -> 'a cDeclarator
  val cDivOp : cBinaryOp
  val cFloat : abr_string -> cFloat
  val cGeqOp : cBinaryOp
  val cIndOp : cUnaryOp
  val cIndex : 'a cExpression -> 'a cExpression -> 'a -> 'a cExpression
  val cLabel : ident -> 'a cStatement -> 'a cAttribute list -> 'a -> 'a cStatement
  val cLeqOp : cBinaryOp
  val cLndOp : cBinaryOp
  val cLorOp : cBinaryOp
  val cMinOp : cUnaryOp
  val cMulOp : cBinaryOp
  val cNegOp : cUnaryOp
  val cNeqOp : cBinaryOp
  val cRmdOp : cBinaryOp
  val cShlOp : cBinaryOp
  val cShrOp : cBinaryOp
  val cSubOp : cBinaryOp
  val cUnary : cUnaryOp -> 'a cExpression -> 'a -> 'a cExpression
  val cWhile : 'a cExpression -> 'a cStatement -> bool -> 'a -> 'a cStatement
  val cXorOp : cBinaryOp
  val cAsmExt : 'a cStringLiteral -> 'a -> 'a cExternalDeclaration
  val cAssign : cAssignOp -> 'a cExpression -> 'a cExpression -> 'a -> 'a cExpression
  val cBinary : cBinaryOp -> 'a cExpression -> 'a cExpression -> 'a -> 'a cExpression
  val cCompOp : cUnaryOp
  val cExtern : 'a -> 'a cStorageSpecifier
  val cFunDef : 'a cDeclarationSpecifier list -> 'a cDeclarator -> 'a cDeclaration list -> 'a cStatement -> 'a -> 'a cFunctionDef
  val cMember : 'a cExpression -> ident -> bool -> 'a -> 'a cExpression
  val cPlusOp : cUnaryOp
  val cReturn : 'a cExpression optiona -> 'a -> 'a cStatement
  val cSUType : 'a cStructureUnion -> 'a -> 'a cTypeSpecifier
  val cStatic : 'a -> 'a cStorageSpecifier
  val cStrLit : cString -> 'a -> 'a cStringLiteral
  val cString : abr_string -> bool -> cString
  val cStruct : cStructTag -> ident optiona -> ('a cDeclaration list) optiona -> 'a cAttribute list -> 'a -> 'a cStructureUnion
  val cSwitch : 'a cExpression -> 'a cStatement -> 'a -> 'a cStatement
  val cThread : 'a -> 'a cStorageSpecifier
  val decRepr : cIntRepr
  val hexRepr : cIntRepr
  val onlyPos : position -> position * int -> nodeInfo
  val head : asmblock -> abr_string
  val mod1 : asmblock -> (abr_string option * (abr_string * expr)) list
  val mod2 : asmblock -> (abr_string option * (abr_string * expr)) list
  val mod3 : asmblock -> abr_string list
  val map_Region_Wrap : ('a -> 'b) -> 'a region_Wrap -> 'b region_Wrap
  val map_ctype : ('a -> 'b) -> 'a ctype -> 'b ctype
  val rec_expr :
    (binoptype -> expr -> expr -> 'a -> 'a -> 'b) ->
      (unoptype -> expr -> 'a -> 'b) ->
        (expr -> expr -> expr -> 'a -> 'a -> 'a -> 'b) ->
          (literalconstant_node region_Wrap -> 'b) ->
            (abr_string -> ((int ctype * more_info) option) unsynchronized_ref -> 'b) ->
              (expr -> abr_string -> 'a -> 'b) ->
                (expr -> expr -> 'a -> 'a -> 'b) ->
                  (expr -> 'a -> 'b) ->
                    ((expr * 'a) ctype region_Wrap -> expr -> 'a -> 'b) ->
                      (expr -> 'a -> 'b) ->
                        ((expr * 'a) ctype region_Wrap -> 'b) ->
                          (expr -> (expr * 'a) list -> 'a -> 'b) ->
                            ((expr * 'a) ctype -> ((designator * 'c) list * (initializer * 'd)) list -> 'b) ->
                              ((expr * 'a) ctype -> 'b) ->
                                (expr -> 'a -> 'b) -> ((expr_node * 'b) region_Wrap -> 'a) -> (expr -> 'a -> 'd) -> (((designator * 'c) list * (initializer * 'd)) list -> 'd) -> (expr -> 'a -> 'c) -> (abr_string -> 'c) -> expr -> 'a
  val rec_designator :
    (binoptype -> expr -> expr -> 'a -> 'a -> 'b) ->
      (unoptype -> expr -> 'a -> 'b) ->
        (expr -> expr -> expr -> 'a -> 'a -> 'a -> 'b) ->
          (literalconstant_node region_Wrap -> 'b) ->
            (abr_string -> ((int ctype * more_info) option) unsynchronized_ref -> 'b) ->
              (expr -> abr_string -> 'a -> 'b) ->
                (expr -> expr -> 'a -> 'a -> 'b) ->
                  (expr -> 'a -> 'b) ->
                    ((expr * 'a) ctype region_Wrap -> expr -> 'a -> 'b) ->
                      (expr -> 'a -> 'b) ->
                        ((expr * 'a) ctype region_Wrap -> 'b) ->
                          (expr -> (expr * 'a) list -> 'a -> 'b) ->
                            ((expr * 'a) ctype -> ((designator * 'c) list * (initializer * 'd)) list -> 'b) ->
                              ((expr * 'a) ctype -> 'b) ->
                                (expr -> 'a -> 'b) ->
                                  ((expr_node * 'b) region_Wrap -> 'a) -> (expr -> 'a -> 'd) -> (((designator * 'c) list * (initializer * 'd)) list -> 'd) -> (expr -> 'a -> 'c) -> (abr_string -> 'c) -> designator -> 'c
  val rec_initializer :
    (binoptype -> expr -> expr -> 'a -> 'a -> 'b) ->
      (unoptype -> expr -> 'a -> 'b) ->
        (expr -> expr -> expr -> 'a -> 'a -> 'a -> 'b) ->
          (literalconstant_node region_Wrap -> 'b) ->
            (abr_string -> ((int ctype * more_info) option) unsynchronized_ref -> 'b) ->
              (expr -> abr_string -> 'a -> 'b) ->
                (expr -> expr -> 'a -> 'a -> 'b) ->
                  (expr -> 'a -> 'b) ->
                    ((expr * 'a) ctype region_Wrap -> expr -> 'a -> 'b) ->
                      (expr -> 'a -> 'b) ->
                        ((expr * 'a) ctype region_Wrap -> 'b) ->
                          (expr -> (expr * 'a) list -> 'a -> 'b) ->
                            ((expr * 'a) ctype -> ((designator * 'c) list * (initializer * 'd)) list -> 'b) ->
                              ((expr * 'a) ctype -> 'b) ->
                                (expr -> 'a -> 'b) ->
                                  ((expr_node * 'b) region_Wrap -> 'a) -> (expr -> 'a -> 'd) -> (((designator * 'c) list * (initializer * 'd)) list -> 'd) -> (expr -> 'a -> 'c) -> (abr_string -> 'c) -> initializer -> 'd
  val rec_expr_node :
    (binoptype -> expr -> expr -> 'a -> 'a -> 'b) ->
      (unoptype -> expr -> 'a -> 'b) ->
        (expr -> expr -> expr -> 'a -> 'a -> 'a -> 'b) ->
          (literalconstant_node region_Wrap -> 'b) ->
            (abr_string -> ((int ctype * more_info) option) unsynchronized_ref -> 'b) ->
              (expr -> abr_string -> 'a -> 'b) ->
                (expr -> expr -> 'a -> 'a -> 'b) ->
                  (expr -> 'a -> 'b) ->
                    ((expr * 'a) ctype region_Wrap -> expr -> 'a -> 'b) ->
                      (expr -> 'a -> 'b) ->
                        ((expr * 'a) ctype region_Wrap -> 'b) ->
                          (expr -> (expr * 'a) list -> 'a -> 'b) ->
                            ((expr * 'a) ctype -> ((designator * 'c) list * (initializer * 'd)) list -> 'b) ->
                              ((expr * 'a) ctype -> 'b) ->
                                (expr -> 'a -> 'b) ->
                                  ((expr_node * 'b) region_Wrap -> 'a) -> (expr -> 'a -> 'd) -> (((designator * 'c) list * (initializer * 'd)) list -> 'd) -> (expr -> 'a -> 'c) -> (abr_string -> 'c) -> expr_node -> 'b
  val cArrSize : bool -> 'a cExpression -> 'a cArraySize
  val cAsmStmt : 'a cTypeQualifier optiona -> 'a cStringLiteral -> 'a cAssemblyOperand list -> 'a cAssemblyOperand list -> 'a cStringLiteral list -> 'a -> 'a cAssemblyStatement
  val cDeclExt : 'a cDeclaration -> 'a cExternalDeclaration
  val cDefault : 'a cStatement -> 'a -> 'a cStatement
  val cFDefExt : 'a cFunctionDef -> 'a cExternalDeclaration
  val cFunSpec : 'a cFunctionSpecifier -> 'a cDeclarationSpecifier
  val cGotoPtr : 'a cExpression -> 'a -> 'a cStatement
  val cIntType : 'a -> 'a cTypeSpecifier
  val cInteger : int -> cIntRepr -> cIntFlag flags -> cInteger
  val cOrAssOp : cAssignOp
  val cTypeDef : ident -> 'a -> 'a cTypeSpecifier
  val cTypedef : 'a -> 'a cStorageSpecifier
  val flagImag : cIntFlag
  val flagLong : cIntFlag
  val namedRef : ident -> sUERef
  val nodeInfo : position -> position * int -> name -> nodeInfo
  val position : int -> abr_string -> int -> int -> position
  val cAddAssOp : cAssignOp
  val cAndAssOp : cAssignOp
  val cArrDeclr : 'a cTypeQualifier list -> 'a cArraySize -> 'a -> 'a cDerivedDeclarator
  val cArrDesig : 'a cExpression -> 'a -> 'a cPartDesignator
  val cAssignOp : cAssignOp
  val cAttrQual : 'a cAttribute -> 'a cTypeQualifier
  val cBoolType : 'a -> 'a cTypeSpecifier
  val cCharType : 'a -> 'a cTypeSpecifier
  val cCompound : ident list -> 'a cCompoundBlockItem list -> 'a -> 'a cStatement
  val cDivAssOp : cAssignOp
  val cEnumType : 'a cEnumeration -> 'a -> 'a cTypeSpecifier
  val cFunDeclr : ((ident list), ('a cDeclaration list * bool)) either -> 'a cAttribute list -> 'a -> 'a cDerivedDeclarator
  val cInitExpr : 'a cExpression -> 'a -> 'a cInitializer
  val cInitList : ('a cPartDesignator list * 'a cInitializer) list -> 'a -> 'a cInitializer
  val cIntConst : cInteger -> 'a -> 'a cConstant
  val cLongType : 'a -> 'a cTypeSpecifier
  val cMulAssOp : cAssignOp
  val cPreDecOp : cUnaryOp
  val cPreIncOp : cUnaryOp
  val cPtrDeclr : 'a cTypeQualifier list -> 'a -> 'a cDerivedDeclarator
  val cRegister : 'a -> 'a cStorageSpecifier
  val cRmdAssOp : cAssignOp
  val cShlAssOp : cAssignOp
  val cShrAssOp : cAssignOp
  val cStatExpr : 'a cStatement -> 'a -> 'a cExpression
  val cStrConst : cString -> 'a -> 'a cConstant
  val cSubAssOp : cAssignOp
  val cTypeQual : 'a cTypeQualifier -> 'a cDeclarationSpecifier
  val cTypeSpec : 'a cTypeSpecifier -> 'a cDeclarationSpecifier
  val cUnionTag : cStructTag
  val cVoidType : 'a -> 'a cTypeSpecifier
  val cXorAssOp : cAssignOp
  val octalRepr : cIntRepr
  val rec_ctype :
    (base_inttype -> 'a) ->
      (base_inttype -> 'a) ->
        'a -> 'a -> (abr_string -> 'a) ->
                      (abr_string -> 'a) ->
                        (abr_string option -> 'a) -> ('b ctype -> 'a -> 'a) -> ('b ctype -> 'b option -> 'a -> 'a) -> (bool -> 'b -> 'a) -> (abr_string -> 'a) -> ('b ctype -> ('b ctype * 'a) list -> 'a -> 'a) -> 'a -> 'b ctype -> 'a
  val cAlignSpec : 'a cAlignmentSpecifier -> 'a cDeclarationSpecifier
  val cBlockDecl : 'a cDeclaration -> 'a cCompoundBlockItem
  val cBlockStmt : 'a cStatement -> 'a cCompoundBlockItem
  val cCharConst : cChar -> 'a -> 'a cConstant
  val cConstQual : 'a -> 'a cTypeQualifier
  val cFloatType : 'a -> 'a cTypeSpecifier
  val cNoArrSize : bool -> 'a cArraySize
  val cPostDecOp : cUnaryOp
  val cPostIncOp : cUnaryOp
  val cRestrQual : 'a -> 'a cTypeQualifier
  val cShortType : 'a -> 'a cTypeSpecifier
  val cStructTag : cStructTag
  val cUnsigType : 'a -> 'a cTypeSpecifier
  val cVolatQual : 'a -> 'a cTypeQualifier
  val noPosition : position
  val cAsmOperand : ident optiona -> 'a cStringLiteral -> 'a cExpression -> 'a -> 'a cAssemblyOperand
  val cAtomicQual : 'a -> 'a cTypeQualifier
  val cAtomicType : 'a cDeclaration -> 'a -> 'a cTypeSpecifier
  val cDoubleType : 'a -> 'a cTypeSpecifier
  val cFloatConst : cFloat -> 'a -> 'a cConstant
  val cInlineQual : 'a -> 'a cFunctionSpecifier
  val cInt128Type : 'a -> 'a cTypeSpecifier
  val cRangeDesig : 'a cExpression -> 'a cExpression -> 'a -> 'a cPartDesignator
  val cSignedType : 'a -> 'a cTypeSpecifier
  val cSizeofExpr : 'a cExpression -> 'a -> 'a cExpression
  val cSizeofType : 'a cDeclaration -> 'a -> 'a cExpression
  val cTranslUnit : 'a cExternalDeclaration list -> 'a -> 'a cTranslationUnit
  val cTypeOfExpr : 'a cExpression -> 'a -> 'a cTypeSpecifier
  val cTypeOfType : 'a cDeclaration -> 'a -> 'a cTypeSpecifier
  val rec_Region : 'a -> (sourcePos -> sourcePos -> 'a) -> region -> 'a
  val rec_fnspec : (abr_string region_Wrap -> 'a) -> (abr_string region_Wrap -> 'a) -> (abr_string list -> 'a) -> 'a -> (gcc_attribute list -> 'a) -> fnspec -> 'a
  val anonymousRef : name -> sUERef
  val cAlignAsExpr : 'a cExpression -> 'a -> 'a cAlignmentSpecifier
  val cAlignAsType : 'a cDeclaration -> 'a -> 'a cAlignmentSpecifier
  val cAlignofExpr : 'a cExpression -> 'a -> 'a cExpression
  val cAlignofType : 'a cDeclaration -> 'a -> 'a cExpression
  val cBuiltinExpr : 'a cBuiltinThing -> 'a cExpression
  val cComplexImag : 'a cExpression -> 'a -> 'a cExpression
  val cComplexReal : 'a cExpression -> 'a -> 'a cExpression
  val cComplexType : 'a -> 'a cTypeSpecifier
  val cCompoundLit : 'a cDeclaration -> ('a cPartDesignator list * 'a cInitializer) list -> 'a -> 'a cExpression
  val cLabAddrExpr : ident -> 'a -> 'a cExpression
  val cMemberDesig : ident -> 'a -> 'a cPartDesignator
  val cNonnullQual : 'a -> 'a cTypeQualifier
  val cStorageSpec : 'a cStorageSpecifier -> 'a cDeclarationSpecifier
  val flagLongLong : cIntFlag
  val flagUnsigned : cIntFlag
  val cBuiltinVaArg : 'a cExpression -> 'a cDeclaration -> 'a -> 'a cBuiltinThing
  val cNestedFunDef : 'a cFunctionDef -> 'a cCompoundBlockItem
  val cNoreturnQual : 'a -> 'a cFunctionSpecifier
  val cNullableQual : 'a -> 'a cTypeQualifier
  val cStaticAssert : 'a cExpression -> 'a cStringLiteral -> 'a -> 'a cDeclaration
  val clangCVersion : abr_string -> clangCVersion
  val builtinPosition : position
  val rec_ext_decl : (expr ctype * abr_string region_Wrap -> (expr ctype * abr_string region_Wrap) list -> fnspec list -> (block_item list) region_Wrap -> 'a) -> (declaration region_Wrap -> 'a) -> ext_decl -> 'a
  val rec_unoptype : 'a -> 'a -> 'a -> 'a -> unoptype -> 'a
  val cBuiltinOffsetOf : 'a cDeclaration -> 'a cPartDesignator list -> 'a -> 'a cBuiltinThing
  val internalPosition : position
  val cGenericSelection : 'a cExpression -> ('a cDeclaration optiona * 'a cExpression) list -> 'a -> 'a cExpression
  val rec_SourcePos : (int -> abr_string -> int -> 'a) -> sourcePos -> 'a
  val rec_binoptype : 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> binoptype -> 'a
  val rec_more_info : (abr_string -> abr_string option -> 'a) -> 'a -> 'a -> more_info -> 'a
  val rec_statement :
    (expr -> expr -> 'a) ->
      (expr option -> expr -> expr list -> 'a) ->
        (expr -> 'a) ->
          (expr -> expr -> expr list -> 'a) ->
            ((block_item * 'b) list -> 'a) ->
              (expr -> abr_string region_Wrap option -> statement -> 'c -> 'a) ->
                (trappable -> statement -> 'c -> 'a) ->
                  (expr option -> 'a) ->
                    (expr -> expr list -> 'a) ->
                      'a -> 'a -> (expr -> statement -> statement -> 'c -> 'c -> 'a) ->
                                    (expr -> ((expr option) list * (block_item * 'b) list) list -> 'a) ->
                                      'a -> (abr_string -> 'a) ->
                                              (abr_string -> 'a) ->
                                                ((abr_string * abr_string) * ((statement * 'c) list * abr_string) -> 'a) ->
                                                  (bool -> asmblock -> 'a) -> (expr -> 'a) -> ((statement_node * 'a) region_Wrap -> 'c) -> (statement -> 'c -> 'b) -> (declaration region_Wrap -> 'b) -> statement -> 'c
  val rec_block_item :
    (expr -> expr -> 'a) ->
      (expr option -> expr -> expr list -> 'a) ->
        (expr -> 'a) ->
          (expr -> expr -> expr list -> 'a) ->
            ((block_item * 'b) list -> 'a) ->
              (expr -> abr_string region_Wrap option -> statement -> 'c -> 'a) ->
                (trappable -> statement -> 'c -> 'a) ->
                  (expr option -> 'a) ->
                    (expr -> expr list -> 'a) ->
                      'a -> 'a -> (expr -> statement -> statement -> 'c -> 'c -> 'a) ->
                                    (expr -> ((expr option) list * (block_item * 'b) list) list -> 'a) ->
                                      'a -> (abr_string -> 'a) ->
                                              (abr_string -> 'a) ->
                                                ((abr_string * abr_string) * ((statement * 'c) list * abr_string) -> 'a) ->
                                                  (bool -> asmblock -> 'a) -> (expr -> 'a) -> ((statement_node * 'a) region_Wrap -> 'c) -> (statement -> 'c -> 'b) -> (declaration region_Wrap -> 'b) -> block_item -> 'b
  val rec_statement_node :
    (expr -> expr -> 'a) ->
      (expr option -> expr -> expr list -> 'a) ->
        (expr -> 'a) ->
          (expr -> expr -> expr list -> 'a) ->
            ((block_item * 'b) list -> 'a) ->
              (expr -> abr_string region_Wrap option -> statement -> 'c -> 'a) ->
                (trappable -> statement -> 'c -> 'a) ->
                  (expr option -> 'a) ->
                    (expr -> expr list -> 'a) ->
                      'a -> 'a -> (expr -> statement -> statement -> 'c -> 'c -> 'a) ->
                                    (expr -> ((expr option) list * (block_item * 'b) list) list -> 'a) ->
                                      'a -> (abr_string -> 'a) ->
                                              (abr_string -> 'a) ->
                                                ((abr_string * abr_string) * ((statement * 'c) list * abr_string) -> 'a) ->
                                                  (bool -> asmblock -> 'a) -> (expr -> 'a) -> ((statement_node * 'a) region_Wrap -> 'c) -> (statement -> 'c -> 'b) -> (declaration region_Wrap -> 'b) -> statement_node -> 'a
  val rec_trappable : 'a -> 'a -> trappable -> 'a
  val rec_Region_Wrap : ('a -> region -> 'b) -> 'a region_Wrap -> 'b
  val rec_declaration :
    (expr ctype * (abr_string region_Wrap * (storage_class list * (initializer option * gcc_attribute list))) -> 'a) ->
      (abr_string region_Wrap -> (expr ctype * abr_string region_Wrap) list -> 'a) ->
        ((expr ctype * abr_string region_Wrap) list -> 'a) ->
          (expr ctype -> abr_string region_Wrap -> (expr ctype * abr_string option) list -> fnspec list -> 'a) -> ((abr_string option) region_Wrap -> (abr_string region_Wrap * expr option) list -> 'a) -> declaration -> 'a
  val cBuiltinTypesCompatible : 'a cDeclaration -> 'a cDeclaration -> 'a -> 'a cBuiltinThing
  val rec_base_inttype : 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> 'a -> base_inttype -> 'a
  val rec_gcc_attribute : (abr_string -> 'a) -> (abr_string -> expr list -> 'a) -> (abr_string -> 'a) -> gcc_attribute -> 'a
  val rec_storage_class : 'a -> 'a -> 'a -> 'a -> 'a -> storage_class -> 'a
  val rec_StringCvt_radix : 'a -> 'a -> 'a -> 'a -> stringCvt_radix -> 'a
  val rec_Unsynchronized_ref : ('a -> 'b) -> 'a unsynchronized_ref -> 'b
  val rec_literalconstant_node : (int -> abr_string -> stringCvt_radix -> 'a) -> (abr_string -> 'a) -> literalconstant_node -> 'a
end = struct

datatype inta = Int_of_integer of int;

datatype num = One | Bit0 of num | Bit1 of num;

val one_inta : inta = Int_of_integer (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = one_inta} : inta one;

fun integer_of_int (Int_of_integer k) = k;

fun times_inta k l = Int_of_integer (integer_of_int k * integer_of_int l);

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val times_int = {times = times_inta} : inta times;

val power_int = {one_power = one_int, times_power = times_int} : inta power;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) = eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

val equal_char = {equal = (fn a => fn b => ((a : char) = b))} : char equal;

datatype nat = Nat of int;

fun shows_prec_char p c = (fn a => c :: a);

fun shows_string x = (fn a => x @ a);

fun shows_list_char cs = shows_string cs;

type 'a show = {shows_prec : nat -> 'a -> char list -> char list, shows_list : 'a list -> char list -> char list};
val shows_prec = #shows_prec : 'a show -> nat -> 'a -> char list -> char list;
val shows_list = #shows_list : 'a show -> 'a list -> char list -> char list;

val show_char = {shows_prec = shows_prec_char, shows_list = shows_list_char} : char show;

datatype string_b_a_s_e = ST of string | STa of char list;

fun equal_string_b_a_s_e (ST x1) (STa x2) = false
  | equal_string_b_a_s_e (STa x2) (ST x1) = false
  | equal_string_b_a_s_e (STa x2) (STa y2) = equal_lista equal_char x2 y2
  | equal_string_b_a_s_e (ST x1) (ST y1) = ((x1 : string) = y1);

datatype abr_string = SS_base of string_b_a_s_e | String_concatWith of abr_string * abr_string list;

fun equal_abr_stringa (SS_base x1) (String_concatWith (x21, x22)) = false
  | equal_abr_stringa (String_concatWith (x21, x22)) (SS_base x1) = false
  | equal_abr_stringa (String_concatWith (x21, x22)) (String_concatWith (y21, y22)) = equal_abr_stringa x21 y21 andalso equal_lista (equal_abr_string ()) x22 y22
  | equal_abr_stringa (SS_base x1) (SS_base y1) = equal_string_b_a_s_e x1 y1
and equal_abr_string () = {equal = equal_abr_stringa} : abr_string equal;
val equal_abr_string = equal_abr_string ();

datatype sourcePos = Ta of int * abr_string * int;

fun equal_SourcePos (Ta (x1, x2, x3)) (Ta (y1, y2, y3)) = x1 = y1 andalso (equal_abr_stringa x2 y2 andalso x3 = y3);

datatype region = Bogus | T of sourcePos * sourcePos;

fun equal_Region Bogus (T (x21, x22)) = false
  | equal_Region (T (x21, x22)) Bogus = false
  | equal_Region (T (x21, x22)) (T (y21, y22)) = equal_SourcePos x21 y21 andalso equal_SourcePos x22 y22
  | equal_Region Bogus Bogus = true;

datatype 'a region_Wrap = Tb of 'a * region;

fun equal_Region_Wrap A_ (Tb (x1, x2)) (Tb (y1, y2)) = eq A_ x1 y1 andalso equal_Region x2 y2;

datatype stringCvt_radix = BIN | OCT | DEC | HEX;

datatype literalconstant_node = NUMCONST of int * abr_string * stringCvt_radix | STRING_LIT of abr_string;

datatype 'a unsynchronized_ref = Unsynchronized_ref of 'a;

datatype more_info = MungedVar of abr_string * abr_string option | EnumC | FunctionName;

datatype binoptype = LogOr | LogAnd | Equals | NotEquals | BitwiseAnd | BitwiseOr | BitwiseXOr | Lt | Gt | Leq | Geq | Plus | Minus | Times | Divides | Modulus | RShift | LShift;

datatype unoptype = Negate | Not | Addr | BitNegate;

datatype base_inttype = Char | Short | Int | Long | LongLong | Double | Float;

datatype 'a ctype = Signed of base_inttype | Unsigned of base_inttype | Bool | PlainChar | StructTy of abr_string | UnionTy of abr_string | EnumTy of abr_string option | Ptr of 'a ctype | Array of 'a ctype * 'a option |
  Bitfield of bool * 'a | Identa of abr_string | Function of 'a ctype * 'a ctype list | Void;

datatype expr = E of expr_node region_Wrap
and designator = DesignE of expr | DesignFld of abr_string
and initializer = InitE of expr | InitList of (designator list * initializer) list
and expr_node = BinOp of binoptype * expr * expr | UnOp of unoptype * expr | CondExp of expr * expr * expr | Constant of literalconstant_node region_Wrap | Var of abr_string * ((int ctype * more_info) option) unsynchronized_ref |
  StructDot of expr * abr_string | ArrayDeref of expr * expr | Deref of expr | TypeCast of expr ctype region_Wrap * expr | Sizeof of expr | SizeofTy of expr ctype region_Wrap | EFnCall of expr * expr list |
  CompLiteral of expr ctype * (designator list * initializer) list | Arbitrary of expr ctype | MKBOOL of expr;

fun equal_Unsynchronized_ref A_ (Unsynchronized_ref x) (Unsynchronized_ref ya) = eq A_ x ya;

fun equal_binoptype RShift LShift = false
  | equal_binoptype LShift RShift = false
  | equal_binoptype Modulus LShift = false
  | equal_binoptype LShift Modulus = false
  | equal_binoptype Modulus RShift = false
  | equal_binoptype RShift Modulus = false
  | equal_binoptype Divides LShift = false
  | equal_binoptype LShift Divides = false
  | equal_binoptype Divides RShift = false
  | equal_binoptype RShift Divides = false
  | equal_binoptype Divides Modulus = false
  | equal_binoptype Modulus Divides = false
  | equal_binoptype Times LShift = false
  | equal_binoptype LShift Times = false
  | equal_binoptype Times RShift = false
  | equal_binoptype RShift Times = false
  | equal_binoptype Times Modulus = false
  | equal_binoptype Modulus Times = false
  | equal_binoptype Times Divides = false
  | equal_binoptype Divides Times = false
  | equal_binoptype Minus LShift = false
  | equal_binoptype LShift Minus = false
  | equal_binoptype Minus RShift = false
  | equal_binoptype RShift Minus = false
  | equal_binoptype Minus Modulus = false
  | equal_binoptype Modulus Minus = false
  | equal_binoptype Minus Divides = false
  | equal_binoptype Divides Minus = false
  | equal_binoptype Minus Times = false
  | equal_binoptype Times Minus = false
  | equal_binoptype Plus LShift = false
  | equal_binoptype LShift Plus = false
  | equal_binoptype Plus RShift = false
  | equal_binoptype RShift Plus = false
  | equal_binoptype Plus Modulus = false
  | equal_binoptype Modulus Plus = false
  | equal_binoptype Plus Divides = false
  | equal_binoptype Divides Plus = false
  | equal_binoptype Plus Times = false
  | equal_binoptype Times Plus = false
  | equal_binoptype Plus Minus = false
  | equal_binoptype Minus Plus = false
  | equal_binoptype Geq LShift = false
  | equal_binoptype LShift Geq = false
  | equal_binoptype Geq RShift = false
  | equal_binoptype RShift Geq = false
  | equal_binoptype Geq Modulus = false
  | equal_binoptype Modulus Geq = false
  | equal_binoptype Geq Divides = false
  | equal_binoptype Divides Geq = false
  | equal_binoptype Geq Times = false
  | equal_binoptype Times Geq = false
  | equal_binoptype Geq Minus = false
  | equal_binoptype Minus Geq = false
  | equal_binoptype Geq Plus = false
  | equal_binoptype Plus Geq = false
  | equal_binoptype Leq LShift = false
  | equal_binoptype LShift Leq = false
  | equal_binoptype Leq RShift = false
  | equal_binoptype RShift Leq = false
  | equal_binoptype Leq Modulus = false
  | equal_binoptype Modulus Leq = false
  | equal_binoptype Leq Divides = false
  | equal_binoptype Divides Leq = false
  | equal_binoptype Leq Times = false
  | equal_binoptype Times Leq = false
  | equal_binoptype Leq Minus = false
  | equal_binoptype Minus Leq = false
  | equal_binoptype Leq Plus = false
  | equal_binoptype Plus Leq = false
  | equal_binoptype Leq Geq = false
  | equal_binoptype Geq Leq = false
  | equal_binoptype Gt LShift = false
  | equal_binoptype LShift Gt = false
  | equal_binoptype Gt RShift = false
  | equal_binoptype RShift Gt = false
  | equal_binoptype Gt Modulus = false
  | equal_binoptype Modulus Gt = false
  | equal_binoptype Gt Divides = false
  | equal_binoptype Divides Gt = false
  | equal_binoptype Gt Times = false
  | equal_binoptype Times Gt = false
  | equal_binoptype Gt Minus = false
  | equal_binoptype Minus Gt = false
  | equal_binoptype Gt Plus = false
  | equal_binoptype Plus Gt = false
  | equal_binoptype Gt Geq = false
  | equal_binoptype Geq Gt = false
  | equal_binoptype Gt Leq = false
  | equal_binoptype Leq Gt = false
  | equal_binoptype Lt LShift = false
  | equal_binoptype LShift Lt = false
  | equal_binoptype Lt RShift = false
  | equal_binoptype RShift Lt = false
  | equal_binoptype Lt Modulus = false
  | equal_binoptype Modulus Lt = false
  | equal_binoptype Lt Divides = false
  | equal_binoptype Divides Lt = false
  | equal_binoptype Lt Times = false
  | equal_binoptype Times Lt = false
  | equal_binoptype Lt Minus = false
  | equal_binoptype Minus Lt = false
  | equal_binoptype Lt Plus = false
  | equal_binoptype Plus Lt = false
  | equal_binoptype Lt Geq = false
  | equal_binoptype Geq Lt = false
  | equal_binoptype Lt Leq = false
  | equal_binoptype Leq Lt = false
  | equal_binoptype Lt Gt = false
  | equal_binoptype Gt Lt = false
  | equal_binoptype BitwiseXOr LShift = false
  | equal_binoptype LShift BitwiseXOr = false
  | equal_binoptype BitwiseXOr RShift = false
  | equal_binoptype RShift BitwiseXOr = false
  | equal_binoptype BitwiseXOr Modulus = false
  | equal_binoptype Modulus BitwiseXOr = false
  | equal_binoptype BitwiseXOr Divides = false
  | equal_binoptype Divides BitwiseXOr = false
  | equal_binoptype BitwiseXOr Times = false
  | equal_binoptype Times BitwiseXOr = false
  | equal_binoptype BitwiseXOr Minus = false
  | equal_binoptype Minus BitwiseXOr = false
  | equal_binoptype BitwiseXOr Plus = false
  | equal_binoptype Plus BitwiseXOr = false
  | equal_binoptype BitwiseXOr Geq = false
  | equal_binoptype Geq BitwiseXOr = false
  | equal_binoptype BitwiseXOr Leq = false
  | equal_binoptype Leq BitwiseXOr = false
  | equal_binoptype BitwiseXOr Gt = false
  | equal_binoptype Gt BitwiseXOr = false
  | equal_binoptype BitwiseXOr Lt = false
  | equal_binoptype Lt BitwiseXOr = false
  | equal_binoptype BitwiseOr LShift = false
  | equal_binoptype LShift BitwiseOr = false
  | equal_binoptype BitwiseOr RShift = false
  | equal_binoptype RShift BitwiseOr = false
  | equal_binoptype BitwiseOr Modulus = false
  | equal_binoptype Modulus BitwiseOr = false
  | equal_binoptype BitwiseOr Divides = false
  | equal_binoptype Divides BitwiseOr = false
  | equal_binoptype BitwiseOr Times = false
  | equal_binoptype Times BitwiseOr = false
  | equal_binoptype BitwiseOr Minus = false
  | equal_binoptype Minus BitwiseOr = false
  | equal_binoptype BitwiseOr Plus = false
  | equal_binoptype Plus BitwiseOr = false
  | equal_binoptype BitwiseOr Geq = false
  | equal_binoptype Geq BitwiseOr = false
  | equal_binoptype BitwiseOr Leq = false
  | equal_binoptype Leq BitwiseOr = false
  | equal_binoptype BitwiseOr Gt = false
  | equal_binoptype Gt BitwiseOr = false
  | equal_binoptype BitwiseOr Lt = false
  | equal_binoptype Lt BitwiseOr = false
  | equal_binoptype BitwiseOr BitwiseXOr = false
  | equal_binoptype BitwiseXOr BitwiseOr = false
  | equal_binoptype BitwiseAnd LShift = false
  | equal_binoptype LShift BitwiseAnd = false
  | equal_binoptype BitwiseAnd RShift = false
  | equal_binoptype RShift BitwiseAnd = false
  | equal_binoptype BitwiseAnd Modulus = false
  | equal_binoptype Modulus BitwiseAnd = false
  | equal_binoptype BitwiseAnd Divides = false
  | equal_binoptype Divides BitwiseAnd = false
  | equal_binoptype BitwiseAnd Times = false
  | equal_binoptype Times BitwiseAnd = false
  | equal_binoptype BitwiseAnd Minus = false
  | equal_binoptype Minus BitwiseAnd = false
  | equal_binoptype BitwiseAnd Plus = false
  | equal_binoptype Plus BitwiseAnd = false
  | equal_binoptype BitwiseAnd Geq = false
  | equal_binoptype Geq BitwiseAnd = false
  | equal_binoptype BitwiseAnd Leq = false
  | equal_binoptype Leq BitwiseAnd = false
  | equal_binoptype BitwiseAnd Gt = false
  | equal_binoptype Gt BitwiseAnd = false
  | equal_binoptype BitwiseAnd Lt = false
  | equal_binoptype Lt BitwiseAnd = false
  | equal_binoptype BitwiseAnd BitwiseXOr = false
  | equal_binoptype BitwiseXOr BitwiseAnd = false
  | equal_binoptype BitwiseAnd BitwiseOr = false
  | equal_binoptype BitwiseOr BitwiseAnd = false
  | equal_binoptype NotEquals LShift = false
  | equal_binoptype LShift NotEquals = false
  | equal_binoptype NotEquals RShift = false
  | equal_binoptype RShift NotEquals = false
  | equal_binoptype NotEquals Modulus = false
  | equal_binoptype Modulus NotEquals = false
  | equal_binoptype NotEquals Divides = false
  | equal_binoptype Divides NotEquals = false
  | equal_binoptype NotEquals Times = false
  | equal_binoptype Times NotEquals = false
  | equal_binoptype NotEquals Minus = false
  | equal_binoptype Minus NotEquals = false
  | equal_binoptype NotEquals Plus = false
  | equal_binoptype Plus NotEquals = false
  | equal_binoptype NotEquals Geq = false
  | equal_binoptype Geq NotEquals = false
  | equal_binoptype NotEquals Leq = false
  | equal_binoptype Leq NotEquals = false
  | equal_binoptype NotEquals Gt = false
  | equal_binoptype Gt NotEquals = false
  | equal_binoptype NotEquals Lt = false
  | equal_binoptype Lt NotEquals = false
  | equal_binoptype NotEquals BitwiseXOr = false
  | equal_binoptype BitwiseXOr NotEquals = false
  | equal_binoptype NotEquals BitwiseOr = false
  | equal_binoptype BitwiseOr NotEquals = false
  | equal_binoptype NotEquals BitwiseAnd = false
  | equal_binoptype BitwiseAnd NotEquals = false
  | equal_binoptype Equals LShift = false
  | equal_binoptype LShift Equals = false
  | equal_binoptype Equals RShift = false
  | equal_binoptype RShift Equals = false
  | equal_binoptype Equals Modulus = false
  | equal_binoptype Modulus Equals = false
  | equal_binoptype Equals Divides = false
  | equal_binoptype Divides Equals = false
  | equal_binoptype Equals Times = false
  | equal_binoptype Times Equals = false
  | equal_binoptype Equals Minus = false
  | equal_binoptype Minus Equals = false
  | equal_binoptype Equals Plus = false
  | equal_binoptype Plus Equals = false
  | equal_binoptype Equals Geq = false
  | equal_binoptype Geq Equals = false
  | equal_binoptype Equals Leq = false
  | equal_binoptype Leq Equals = false
  | equal_binoptype Equals Gt = false
  | equal_binoptype Gt Equals = false
  | equal_binoptype Equals Lt = false
  | equal_binoptype Lt Equals = false
  | equal_binoptype Equals BitwiseXOr = false
  | equal_binoptype BitwiseXOr Equals = false
  | equal_binoptype Equals BitwiseOr = false
  | equal_binoptype BitwiseOr Equals = false
  | equal_binoptype Equals BitwiseAnd = false
  | equal_binoptype BitwiseAnd Equals = false
  | equal_binoptype Equals NotEquals = false
  | equal_binoptype NotEquals Equals = false
  | equal_binoptype LogAnd LShift = false
  | equal_binoptype LShift LogAnd = false
  | equal_binoptype LogAnd RShift = false
  | equal_binoptype RShift LogAnd = false
  | equal_binoptype LogAnd Modulus = false
  | equal_binoptype Modulus LogAnd = false
  | equal_binoptype LogAnd Divides = false
  | equal_binoptype Divides LogAnd = false
  | equal_binoptype LogAnd Times = false
  | equal_binoptype Times LogAnd = false
  | equal_binoptype LogAnd Minus = false
  | equal_binoptype Minus LogAnd = false
  | equal_binoptype LogAnd Plus = false
  | equal_binoptype Plus LogAnd = false
  | equal_binoptype LogAnd Geq = false
  | equal_binoptype Geq LogAnd = false
  | equal_binoptype LogAnd Leq = false
  | equal_binoptype Leq LogAnd = false
  | equal_binoptype LogAnd Gt = false
  | equal_binoptype Gt LogAnd = false
  | equal_binoptype LogAnd Lt = false
  | equal_binoptype Lt LogAnd = false
  | equal_binoptype LogAnd BitwiseXOr = false
  | equal_binoptype BitwiseXOr LogAnd = false
  | equal_binoptype LogAnd BitwiseOr = false
  | equal_binoptype BitwiseOr LogAnd = false
  | equal_binoptype LogAnd BitwiseAnd = false
  | equal_binoptype BitwiseAnd LogAnd = false
  | equal_binoptype LogAnd NotEquals = false
  | equal_binoptype NotEquals LogAnd = false
  | equal_binoptype LogAnd Equals = false
  | equal_binoptype Equals LogAnd = false
  | equal_binoptype LogOr LShift = false
  | equal_binoptype LShift LogOr = false
  | equal_binoptype LogOr RShift = false
  | equal_binoptype RShift LogOr = false
  | equal_binoptype LogOr Modulus = false
  | equal_binoptype Modulus LogOr = false
  | equal_binoptype LogOr Divides = false
  | equal_binoptype Divides LogOr = false
  | equal_binoptype LogOr Times = false
  | equal_binoptype Times LogOr = false
  | equal_binoptype LogOr Minus = false
  | equal_binoptype Minus LogOr = false
  | equal_binoptype LogOr Plus = false
  | equal_binoptype Plus LogOr = false
  | equal_binoptype LogOr Geq = false
  | equal_binoptype Geq LogOr = false
  | equal_binoptype LogOr Leq = false
  | equal_binoptype Leq LogOr = false
  | equal_binoptype LogOr Gt = false
  | equal_binoptype Gt LogOr = false
  | equal_binoptype LogOr Lt = false
  | equal_binoptype Lt LogOr = false
  | equal_binoptype LogOr BitwiseXOr = false
  | equal_binoptype BitwiseXOr LogOr = false
  | equal_binoptype LogOr BitwiseOr = false
  | equal_binoptype BitwiseOr LogOr = false
  | equal_binoptype LogOr BitwiseAnd = false
  | equal_binoptype BitwiseAnd LogOr = false
  | equal_binoptype LogOr NotEquals = false
  | equal_binoptype NotEquals LogOr = false
  | equal_binoptype LogOr Equals = false
  | equal_binoptype Equals LogOr = false
  | equal_binoptype LogOr LogAnd = false
  | equal_binoptype LogAnd LogOr = false
  | equal_binoptype LShift LShift = true
  | equal_binoptype RShift RShift = true
  | equal_binoptype Modulus Modulus = true
  | equal_binoptype Divides Divides = true
  | equal_binoptype Times Times = true
  | equal_binoptype Minus Minus = true
  | equal_binoptype Plus Plus = true
  | equal_binoptype Geq Geq = true
  | equal_binoptype Leq Leq = true
  | equal_binoptype Gt Gt = true
  | equal_binoptype Lt Lt = true
  | equal_binoptype BitwiseXOr BitwiseXOr = true
  | equal_binoptype BitwiseOr BitwiseOr = true
  | equal_binoptype BitwiseAnd BitwiseAnd = true
  | equal_binoptype NotEquals NotEquals = true
  | equal_binoptype Equals Equals = true
  | equal_binoptype LogAnd LogAnd = true
  | equal_binoptype LogOr LogOr = true;

fun equal_unoptype Addr BitNegate = false
  | equal_unoptype BitNegate Addr = false
  | equal_unoptype Not BitNegate = false
  | equal_unoptype BitNegate Not = false
  | equal_unoptype Not Addr = false
  | equal_unoptype Addr Not = false
  | equal_unoptype Negate BitNegate = false
  | equal_unoptype BitNegate Negate = false
  | equal_unoptype Negate Addr = false
  | equal_unoptype Addr Negate = false
  | equal_unoptype Negate Not = false
  | equal_unoptype Not Negate = false
  | equal_unoptype BitNegate BitNegate = true
  | equal_unoptype Addr Addr = true
  | equal_unoptype Not Not = true
  | equal_unoptype Negate Negate = true;

fun equal_base_inttype Double Float = false
  | equal_base_inttype Float Double = false
  | equal_base_inttype LongLong Float = false
  | equal_base_inttype Float LongLong = false
  | equal_base_inttype LongLong Double = false
  | equal_base_inttype Double LongLong = false
  | equal_base_inttype Long Float = false
  | equal_base_inttype Float Long = false
  | equal_base_inttype Long Double = false
  | equal_base_inttype Double Long = false
  | equal_base_inttype Long LongLong = false
  | equal_base_inttype LongLong Long = false
  | equal_base_inttype Int Float = false
  | equal_base_inttype Float Int = false
  | equal_base_inttype Int Double = false
  | equal_base_inttype Double Int = false
  | equal_base_inttype Int LongLong = false
  | equal_base_inttype LongLong Int = false
  | equal_base_inttype Int Long = false
  | equal_base_inttype Long Int = false
  | equal_base_inttype Short Float = false
  | equal_base_inttype Float Short = false
  | equal_base_inttype Short Double = false
  | equal_base_inttype Double Short = false
  | equal_base_inttype Short LongLong = false
  | equal_base_inttype LongLong Short = false
  | equal_base_inttype Short Long = false
  | equal_base_inttype Long Short = false
  | equal_base_inttype Short Int = false
  | equal_base_inttype Int Short = false
  | equal_base_inttype Char Float = false
  | equal_base_inttype Float Char = false
  | equal_base_inttype Char Double = false
  | equal_base_inttype Double Char = false
  | equal_base_inttype Char LongLong = false
  | equal_base_inttype LongLong Char = false
  | equal_base_inttype Char Long = false
  | equal_base_inttype Long Char = false
  | equal_base_inttype Char Int = false
  | equal_base_inttype Int Char = false
  | equal_base_inttype Char Short = false
  | equal_base_inttype Short Char = false
  | equal_base_inttype Float Float = true
  | equal_base_inttype Double Double = true
  | equal_base_inttype LongLong LongLong = true
  | equal_base_inttype Long Long = true
  | equal_base_inttype Int Int = true
  | equal_base_inttype Short Short = true
  | equal_base_inttype Char Char = true;

fun equal_bool p true = p
  | equal_bool p false = not p
  | equal_bool true p = p
  | equal_bool false p = not p;

fun equal_optiona A_ NONE (SOME x2) = false
  | equal_optiona A_ (SOME x2) NONE = false
  | equal_optiona A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_optiona A_ NONE NONE = true;

fun equal_ctypea A_ (Function (x121, x122)) Void = false
  | equal_ctypea A_ Void (Function (x121, x122)) = false
  | equal_ctypea A_ (Identa x11) Void = false
  | equal_ctypea A_ Void (Identa x11) = false
  | equal_ctypea A_ (Identa x11) (Function (x121, x122)) = false
  | equal_ctypea A_ (Function (x121, x122)) (Identa x11) = false
  | equal_ctypea A_ (Bitfield (x101, x102)) Void = false
  | equal_ctypea A_ Void (Bitfield (x101, x102)) = false
  | equal_ctypea A_ (Bitfield (x101, x102)) (Function (x121, x122)) = false
  | equal_ctypea A_ (Function (x121, x122)) (Bitfield (x101, x102)) = false
  | equal_ctypea A_ (Bitfield (x101, x102)) (Identa x11) = false
  | equal_ctypea A_ (Identa x11) (Bitfield (x101, x102)) = false
  | equal_ctypea A_ (Array (x91, x92)) Void = false
  | equal_ctypea A_ Void (Array (x91, x92)) = false
  | equal_ctypea A_ (Array (x91, x92)) (Function (x121, x122)) = false
  | equal_ctypea A_ (Function (x121, x122)) (Array (x91, x92)) = false
  | equal_ctypea A_ (Array (x91, x92)) (Identa x11) = false
  | equal_ctypea A_ (Identa x11) (Array (x91, x92)) = false
  | equal_ctypea A_ (Array (x91, x92)) (Bitfield (x101, x102)) = false
  | equal_ctypea A_ (Bitfield (x101, x102)) (Array (x91, x92)) = false
  | equal_ctypea A_ (Ptr x8) Void = false
  | equal_ctypea A_ Void (Ptr x8) = false
  | equal_ctypea A_ (Ptr x8) (Function (x121, x122)) = false
  | equal_ctypea A_ (Function (x121, x122)) (Ptr x8) = false
  | equal_ctypea A_ (Ptr x8) (Identa x11) = false
  | equal_ctypea A_ (Identa x11) (Ptr x8) = false
  | equal_ctypea A_ (Ptr x8) (Bitfield (x101, x102)) = false
  | equal_ctypea A_ (Bitfield (x101, x102)) (Ptr x8) = false
  | equal_ctypea A_ (Ptr x8) (Array (x91, x92)) = false
  | equal_ctypea A_ (Array (x91, x92)) (Ptr x8) = false
  | equal_ctypea A_ (EnumTy x7) Void = false
  | equal_ctypea A_ Void (EnumTy x7) = false
  | equal_ctypea A_ (EnumTy x7) (Function (x121, x122)) = false
  | equal_ctypea A_ (Function (x121, x122)) (EnumTy x7) = false
  | equal_ctypea A_ (EnumTy x7) (Identa x11) = false
  | equal_ctypea A_ (Identa x11) (EnumTy x7) = false
  | equal_ctypea A_ (EnumTy x7) (Bitfield (x101, x102)) = false
  | equal_ctypea A_ (Bitfield (x101, x102)) (EnumTy x7) = false
  | equal_ctypea A_ (EnumTy x7) (Array (x91, x92)) = false
  | equal_ctypea A_ (Array (x91, x92)) (EnumTy x7) = false
  | equal_ctypea A_ (EnumTy x7) (Ptr x8) = false
  | equal_ctypea A_ (Ptr x8) (EnumTy x7) = false
  | equal_ctypea A_ (UnionTy x6) Void = false
  | equal_ctypea A_ Void (UnionTy x6) = false
  | equal_ctypea A_ (UnionTy x6) (Function (x121, x122)) = false
  | equal_ctypea A_ (Function (x121, x122)) (UnionTy x6) = false
  | equal_ctypea A_ (UnionTy x6) (Identa x11) = false
  | equal_ctypea A_ (Identa x11) (UnionTy x6) = false
  | equal_ctypea A_ (UnionTy x6) (Bitfield (x101, x102)) = false
  | equal_ctypea A_ (Bitfield (x101, x102)) (UnionTy x6) = false
  | equal_ctypea A_ (UnionTy x6) (Array (x91, x92)) = false
  | equal_ctypea A_ (Array (x91, x92)) (UnionTy x6) = false
  | equal_ctypea A_ (UnionTy x6) (Ptr x8) = false
  | equal_ctypea A_ (Ptr x8) (UnionTy x6) = false
  | equal_ctypea A_ (UnionTy x6) (EnumTy x7) = false
  | equal_ctypea A_ (EnumTy x7) (UnionTy x6) = false
  | equal_ctypea A_ (StructTy x5) Void = false
  | equal_ctypea A_ Void (StructTy x5) = false
  | equal_ctypea A_ (StructTy x5) (Function (x121, x122)) = false
  | equal_ctypea A_ (Function (x121, x122)) (StructTy x5) = false
  | equal_ctypea A_ (StructTy x5) (Identa x11) = false
  | equal_ctypea A_ (Identa x11) (StructTy x5) = false
  | equal_ctypea A_ (StructTy x5) (Bitfield (x101, x102)) = false
  | equal_ctypea A_ (Bitfield (x101, x102)) (StructTy x5) = false
  | equal_ctypea A_ (StructTy x5) (Array (x91, x92)) = false
  | equal_ctypea A_ (Array (x91, x92)) (StructTy x5) = false
  | equal_ctypea A_ (StructTy x5) (Ptr x8) = false
  | equal_ctypea A_ (Ptr x8) (StructTy x5) = false
  | equal_ctypea A_ (StructTy x5) (EnumTy x7) = false
  | equal_ctypea A_ (EnumTy x7) (StructTy x5) = false
  | equal_ctypea A_ (StructTy x5) (UnionTy x6) = false
  | equal_ctypea A_ (UnionTy x6) (StructTy x5) = false
  | equal_ctypea A_ PlainChar Void = false
  | equal_ctypea A_ Void PlainChar = false
  | equal_ctypea A_ PlainChar (Function (x121, x122)) = false
  | equal_ctypea A_ (Function (x121, x122)) PlainChar = false
  | equal_ctypea A_ PlainChar (Identa x11) = false
  | equal_ctypea A_ (Identa x11) PlainChar = false
  | equal_ctypea A_ PlainChar (Bitfield (x101, x102)) = false
  | equal_ctypea A_ (Bitfield (x101, x102)) PlainChar = false
  | equal_ctypea A_ PlainChar (Array (x91, x92)) = false
  | equal_ctypea A_ (Array (x91, x92)) PlainChar = false
  | equal_ctypea A_ PlainChar (Ptr x8) = false
  | equal_ctypea A_ (Ptr x8) PlainChar = false
  | equal_ctypea A_ PlainChar (EnumTy x7) = false
  | equal_ctypea A_ (EnumTy x7) PlainChar = false
  | equal_ctypea A_ PlainChar (UnionTy x6) = false
  | equal_ctypea A_ (UnionTy x6) PlainChar = false
  | equal_ctypea A_ PlainChar (StructTy x5) = false
  | equal_ctypea A_ (StructTy x5) PlainChar = false
  | equal_ctypea A_ Bool Void = false
  | equal_ctypea A_ Void Bool = false
  | equal_ctypea A_ Bool (Function (x121, x122)) = false
  | equal_ctypea A_ (Function (x121, x122)) Bool = false
  | equal_ctypea A_ Bool (Identa x11) = false
  | equal_ctypea A_ (Identa x11) Bool = false
  | equal_ctypea A_ Bool (Bitfield (x101, x102)) = false
  | equal_ctypea A_ (Bitfield (x101, x102)) Bool = false
  | equal_ctypea A_ Bool (Array (x91, x92)) = false
  | equal_ctypea A_ (Array (x91, x92)) Bool = false
  | equal_ctypea A_ Bool (Ptr x8) = false
  | equal_ctypea A_ (Ptr x8) Bool = false
  | equal_ctypea A_ Bool (EnumTy x7) = false
  | equal_ctypea A_ (EnumTy x7) Bool = false
  | equal_ctypea A_ Bool (UnionTy x6) = false
  | equal_ctypea A_ (UnionTy x6) Bool = false
  | equal_ctypea A_ Bool (StructTy x5) = false
  | equal_ctypea A_ (StructTy x5) Bool = false
  | equal_ctypea A_ Bool PlainChar = false
  | equal_ctypea A_ PlainChar Bool = false
  | equal_ctypea A_ (Unsigned x2) Void = false
  | equal_ctypea A_ Void (Unsigned x2) = false
  | equal_ctypea A_ (Unsigned x2) (Function (x121, x122)) = false
  | equal_ctypea A_ (Function (x121, x122)) (Unsigned x2) = false
  | equal_ctypea A_ (Unsigned x2) (Identa x11) = false
  | equal_ctypea A_ (Identa x11) (Unsigned x2) = false
  | equal_ctypea A_ (Unsigned x2) (Bitfield (x101, x102)) = false
  | equal_ctypea A_ (Bitfield (x101, x102)) (Unsigned x2) = false
  | equal_ctypea A_ (Unsigned x2) (Array (x91, x92)) = false
  | equal_ctypea A_ (Array (x91, x92)) (Unsigned x2) = false
  | equal_ctypea A_ (Unsigned x2) (Ptr x8) = false
  | equal_ctypea A_ (Ptr x8) (Unsigned x2) = false
  | equal_ctypea A_ (Unsigned x2) (EnumTy x7) = false
  | equal_ctypea A_ (EnumTy x7) (Unsigned x2) = false
  | equal_ctypea A_ (Unsigned x2) (UnionTy x6) = false
  | equal_ctypea A_ (UnionTy x6) (Unsigned x2) = false
  | equal_ctypea A_ (Unsigned x2) (StructTy x5) = false
  | equal_ctypea A_ (StructTy x5) (Unsigned x2) = false
  | equal_ctypea A_ (Unsigned x2) PlainChar = false
  | equal_ctypea A_ PlainChar (Unsigned x2) = false
  | equal_ctypea A_ (Unsigned x2) Bool = false
  | equal_ctypea A_ Bool (Unsigned x2) = false
  | equal_ctypea A_ (Signed x1) Void = false
  | equal_ctypea A_ Void (Signed x1) = false
  | equal_ctypea A_ (Signed x1) (Function (x121, x122)) = false
  | equal_ctypea A_ (Function (x121, x122)) (Signed x1) = false
  | equal_ctypea A_ (Signed x1) (Identa x11) = false
  | equal_ctypea A_ (Identa x11) (Signed x1) = false
  | equal_ctypea A_ (Signed x1) (Bitfield (x101, x102)) = false
  | equal_ctypea A_ (Bitfield (x101, x102)) (Signed x1) = false
  | equal_ctypea A_ (Signed x1) (Array (x91, x92)) = false
  | equal_ctypea A_ (Array (x91, x92)) (Signed x1) = false
  | equal_ctypea A_ (Signed x1) (Ptr x8) = false
  | equal_ctypea A_ (Ptr x8) (Signed x1) = false
  | equal_ctypea A_ (Signed x1) (EnumTy x7) = false
  | equal_ctypea A_ (EnumTy x7) (Signed x1) = false
  | equal_ctypea A_ (Signed x1) (UnionTy x6) = false
  | equal_ctypea A_ (UnionTy x6) (Signed x1) = false
  | equal_ctypea A_ (Signed x1) (StructTy x5) = false
  | equal_ctypea A_ (StructTy x5) (Signed x1) = false
  | equal_ctypea A_ (Signed x1) PlainChar = false
  | equal_ctypea A_ PlainChar (Signed x1) = false
  | equal_ctypea A_ (Signed x1) Bool = false
  | equal_ctypea A_ Bool (Signed x1) = false
  | equal_ctypea A_ (Signed x1) (Unsigned x2) = false
  | equal_ctypea A_ (Unsigned x2) (Signed x1) = false
  | equal_ctypea A_ (Function (x121, x122)) (Function (y121, y122)) = equal_ctypea A_ x121 y121 andalso equal_lista (equal_ctype A_) x122 y122
  | equal_ctypea A_ (Identa x11) (Identa y11) = equal_abr_stringa x11 y11
  | equal_ctypea A_ (Bitfield (x101, x102)) (Bitfield (y101, y102)) = equal_bool x101 y101 andalso eq A_ x102 y102
  | equal_ctypea A_ (Array (x91, x92)) (Array (y91, y92)) = equal_ctypea A_ x91 y91 andalso equal_optiona A_ x92 y92
  | equal_ctypea A_ (Ptr x8) (Ptr y8) = equal_ctypea A_ x8 y8
  | equal_ctypea A_ (EnumTy x7) (EnumTy y7) = equal_optiona equal_abr_string x7 y7
  | equal_ctypea A_ (UnionTy x6) (UnionTy y6) = equal_abr_stringa x6 y6
  | equal_ctypea A_ (StructTy x5) (StructTy y5) = equal_abr_stringa x5 y5
  | equal_ctypea A_ (Unsigned x2) (Unsigned y2) = equal_base_inttype x2 y2
  | equal_ctypea A_ (Signed x1) (Signed y1) = equal_base_inttype x1 y1
  | equal_ctypea A_ Void Void = true
  | equal_ctypea A_ PlainChar PlainChar = true
  | equal_ctypea A_ Bool Bool = true
and equal_ctype A_ = {equal = equal_ctypea A_} : 'a ctype equal;

fun equal_StringCvt_radix DEC HEX = false
  | equal_StringCvt_radix HEX DEC = false
  | equal_StringCvt_radix OCT HEX = false
  | equal_StringCvt_radix HEX OCT = false
  | equal_StringCvt_radix OCT DEC = false
  | equal_StringCvt_radix DEC OCT = false
  | equal_StringCvt_radix BIN HEX = false
  | equal_StringCvt_radix HEX BIN = false
  | equal_StringCvt_radix BIN DEC = false
  | equal_StringCvt_radix DEC BIN = false
  | equal_StringCvt_radix BIN OCT = false
  | equal_StringCvt_radix OCT BIN = false
  | equal_StringCvt_radix HEX HEX = true
  | equal_StringCvt_radix DEC DEC = true
  | equal_StringCvt_radix OCT OCT = true
  | equal_StringCvt_radix BIN BIN = true;

fun equal_literalconstant_nodea (NUMCONST (x11, x12, x13)) (STRING_LIT x2) = false
  | equal_literalconstant_nodea (STRING_LIT x2) (NUMCONST (x11, x12, x13)) = false
  | equal_literalconstant_nodea (STRING_LIT x2) (STRING_LIT y2) = equal_abr_stringa x2 y2
  | equal_literalconstant_nodea (NUMCONST (x11, x12, x13)) (NUMCONST (y11, y12, y13)) = x11 = y11 andalso (equal_abr_stringa x12 y12 andalso equal_StringCvt_radix x13 y13);

val equal_literalconstant_node = {equal = equal_literalconstant_nodea} : literalconstant_node equal;

val equal_integer = {equal = (fn a => fn b => a = b)} : int equal;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun equal_more_infoa EnumC FunctionName = false
  | equal_more_infoa FunctionName EnumC = false
  | equal_more_infoa (MungedVar (x11, x12)) FunctionName = false
  | equal_more_infoa FunctionName (MungedVar (x11, x12)) = false
  | equal_more_infoa (MungedVar (x11, x12)) EnumC = false
  | equal_more_infoa EnumC (MungedVar (x11, x12)) = false
  | equal_more_infoa (MungedVar (x11, x12)) (MungedVar (y11, y12)) = equal_abr_stringa x11 y11 andalso equal_optiona equal_abr_string x12 y12
  | equal_more_infoa FunctionName FunctionName = true
  | equal_more_infoa EnumC EnumC = true;

val equal_more_info = {equal = equal_more_infoa} : more_info equal;

fun equal_option A_ = {equal = equal_optiona A_} : ('a option) equal;

fun equal_expr () = {equal = equal_expra} : expr equal
and equal_expr_nodea (Arbitrary x14) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (Arbitrary x14) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (SizeofTy x11a) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (SizeofTy x11a) = false
  | equal_expr_nodea (Sizeof x10) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (Sizeof x10) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (Deref x8) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (Deref x8) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (StructDot (x61, x62)) = false
  | equal_expr_nodea (Var (x51, x52)) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (Var (x51, x52)) = false
  | equal_expr_nodea (Constant x4) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (Constant x4) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (UnOp (x21, x22)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (MKBOOL x15) = false
  | equal_expr_nodea (MKBOOL x15) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (Arbitrary x14) = false
  | equal_expr_nodea (Arbitrary x14) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (CompLiteral (x131, x132)) = false
  | equal_expr_nodea (CompLiteral (x131, x132)) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (EFnCall (x121, x122)) = false
  | equal_expr_nodea (EFnCall (x121, x122)) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (SizeofTy x11a) = false
  | equal_expr_nodea (SizeofTy x11a) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (Sizeof x10) = false
  | equal_expr_nodea (Sizeof x10) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (TypeCast (x91, x92)) = false
  | equal_expr_nodea (TypeCast (x91, x92)) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (Deref x8) = false
  | equal_expr_nodea (Deref x8) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (ArrayDeref (x71, x72)) = false
  | equal_expr_nodea (ArrayDeref (x71, x72)) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (StructDot (x61, x62)) = false
  | equal_expr_nodea (StructDot (x61, x62)) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (Var (x51, x52)) = false
  | equal_expr_nodea (Var (x51, x52)) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (Constant x4) = false
  | equal_expr_nodea (Constant x4) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (CondExp (x31, x32, x33)) = false
  | equal_expr_nodea (CondExp (x31, x32, x33)) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (BinOp (x11, x12, x13)) (UnOp (x21, x22)) = false
  | equal_expr_nodea (UnOp (x21, x22)) (BinOp (x11, x12, x13)) = false
  | equal_expr_nodea (MKBOOL x15) (MKBOOL y15) = equal_expra x15 y15
  | equal_expr_nodea (Arbitrary x14) (Arbitrary y14) = equal_ctypea (equal_expr ()) x14 y14
  | equal_expr_nodea (CompLiteral (x131, x132)) (CompLiteral (y131, y132)) = equal_ctypea (equal_expr ()) x131 y131 andalso equal_lista (equal_prod (equal_list (equal_designator ())) (equal_initializer ())) x132 y132
  | equal_expr_nodea (EFnCall (x121, x122)) (EFnCall (y121, y122)) = equal_expra x121 y121 andalso equal_lista (equal_expr ()) x122 y122
  | equal_expr_nodea (SizeofTy x11a) (SizeofTy y11a) = equal_Region_Wrap (equal_ctype (equal_expr ())) x11a y11a
  | equal_expr_nodea (Sizeof x10) (Sizeof y10) = equal_expra x10 y10
  | equal_expr_nodea (TypeCast (x91, x92)) (TypeCast (y91, y92)) = equal_Region_Wrap (equal_ctype (equal_expr ())) x91 y91 andalso equal_expra x92 y92
  | equal_expr_nodea (Deref x8) (Deref y8) = equal_expra x8 y8
  | equal_expr_nodea (ArrayDeref (x71, x72)) (ArrayDeref (y71, y72)) = equal_expra x71 y71 andalso equal_expra x72 y72
  | equal_expr_nodea (StructDot (x61, x62)) (StructDot (y61, y62)) = equal_expra x61 y61 andalso equal_abr_stringa x62 y62
  | equal_expr_nodea (Var (x51, x52)) (Var (y51, y52)) = equal_abr_stringa x51 y51 andalso equal_Unsynchronized_ref (equal_option (equal_prod (equal_ctype equal_integer) equal_more_info)) x52 y52
  | equal_expr_nodea (Constant x4) (Constant y4) = equal_Region_Wrap equal_literalconstant_node x4 y4
  | equal_expr_nodea (CondExp (x31, x32, x33)) (CondExp (y31, y32, y33)) = equal_expra x31 y31 andalso (equal_expra x32 y32 andalso equal_expra x33 y33)
  | equal_expr_nodea (UnOp (x21, x22)) (UnOp (y21, y22)) = equal_unoptype x21 y21 andalso equal_expra x22 y22
  | equal_expr_nodea (BinOp (x11, x12, x13)) (BinOp (y11, y12, y13)) = equal_binoptype x11 y11 andalso (equal_expra x12 y12 andalso equal_expra x13 y13)
and equal_expr_node () = {equal = equal_expr_nodea} : expr_node equal
and equal_expra (E x) (E ya) = equal_Region_Wrap (equal_expr_node ()) x ya
and equal_designatora (DesignE x1) (DesignFld x2) = false
  | equal_designatora (DesignFld x2) (DesignE x1) = false
  | equal_designatora (DesignFld x2) (DesignFld y2) = equal_abr_stringa x2 y2
  | equal_designatora (DesignE x1) (DesignE y1) = equal_expra x1 y1
and equal_designator () = {equal = equal_designatora} : designator equal
and equal_initializera (InitE x1) (InitList x2) = false
  | equal_initializera (InitList x2) (InitE x1) = false
  | equal_initializera (InitList x2) (InitList y2) = equal_lista (equal_prod (equal_list (equal_designator ())) (equal_initializer ())) x2 y2
  | equal_initializera (InitE x1) (InitE y1) = equal_expra x1 y1
and equal_initializer () = {equal = equal_initializera} : initializer equal;
val equal_expr = equal_expr ();
val equal_expr_node = equal_expr_node ();
val equal_designator = equal_designator ();
val equal_initializer = equal_initializer ();

datatype 'a itself = Type;

type 'a len0 = {len_of : 'a itself -> nat};
val len_of = #len_of : 'a len0 -> 'a itself -> nat;

fun integer_of_nat (Nat x) = x;

fun times_nat m n = Nat (integer_of_nat m * integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer = {less_eq = (fn a => fn b => a <= b), less = (fn a => fn b => a < b)} : int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

type 'a finite = {};

datatype 'a bit0 = Abs_bit0 of inta;

fun len_of_bit0 A_ uu = times_nat (nat_of_integer (2 : IntInf.int)) (len_of A_ Type);

fun len0_bit0 A_ = {len_of = len_of_bit0 A_} : 'a bit0 len0;

val one_nat : nat = Nat (1 : IntInf.int);

datatype num1 = One_num1;

fun len_of_num1 uu = one_nat;

val len0_num1 = {len_of = len_of_num1} : num1 len0;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_integer = {plus = (fn a => fn b => a + b)} : int plus;

datatype gcc_attribute = GCC_AttribID of abr_string | GCC_AttribFn of abr_string * expr list | OWNED_BY of abr_string;

fun equal_gcc_attributea (GCC_AttribFn (x21, x22)) (OWNED_BY x3) = false
  | equal_gcc_attributea (OWNED_BY x3) (GCC_AttribFn (x21, x22)) = false
  | equal_gcc_attributea (GCC_AttribID x1) (OWNED_BY x3) = false
  | equal_gcc_attributea (OWNED_BY x3) (GCC_AttribID x1) = false
  | equal_gcc_attributea (GCC_AttribID x1) (GCC_AttribFn (x21, x22)) = false
  | equal_gcc_attributea (GCC_AttribFn (x21, x22)) (GCC_AttribID x1) = false
  | equal_gcc_attributea (OWNED_BY x3) (OWNED_BY y3) = equal_abr_stringa x3 y3
  | equal_gcc_attributea (GCC_AttribFn (x21, x22)) (GCC_AttribFn (y21, y22)) = equal_abr_stringa x21 y21 andalso equal_lista equal_expr x22 y22
  | equal_gcc_attributea (GCC_AttribID x1) (GCC_AttribID y1) = equal_abr_stringa x1 y1;

val equal_gcc_attribute = {equal = equal_gcc_attributea} : gcc_attribute equal;

datatype 'a word = Word of inta;

datatype ('b, 'a) alist = Alist of ('b * 'a) list;

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

datatype fnspec = Fnspec of abr_string region_Wrap | Relspec of abr_string region_Wrap | Fn_modifies of abr_string list | Didnt_translate | Gcc_attribs of gcc_attribute list;

datatype asmblock = Asmblock of abr_string * (abr_string option * (abr_string * expr)) list * (abr_string option * (abr_string * expr)) list * abr_string list;

datatype storage_class = SC_EXTERN | SC_STATIC | SC_AUTO | SC_REGISTER | SC_THRD_LOCAL;

datatype declaration = VarDecl of (expr ctype * (abr_string region_Wrap * (storage_class list * (initializer option * gcc_attribute list)))) | StructDecl of abr_string region_Wrap * (expr ctype * abr_string region_Wrap) list |
  TypeDecl of (expr ctype * abr_string region_Wrap) list | ExtFnDecl of expr ctype * abr_string region_Wrap * (expr ctype * abr_string option) list * fnspec list |
  EnumDecl of (abr_string option) region_Wrap * (abr_string region_Wrap * expr option) list;

datatype trappable = BreakT | ContinueT;

datatype block_item = BI_Stmt of statement | BI_Decl of declaration region_Wrap
and statement_node = Assign of expr * expr | AssignFnCall of expr option * expr * expr list | Chaos of expr | EmbFnCall of expr * expr * expr list | Block of block_item list | While of expr * abr_string region_Wrap option * statement |
  Trap of trappable * statement | Return of expr option | ReturnFnCall of expr * expr list | Break | Continue | IfStmt of expr * statement * statement | Switch of expr * ((expr option) list * block_item list) list | EmptyStmt |
  Auxupd of abr_string | Ghostupd of abr_string | Spec of ((abr_string * abr_string) * (statement list * abr_string)) | AsmStmt of bool * asmblock | LocalInit of expr
and statement = Stmt of statement_node region_Wrap;

datatype ext_decl = FnDefn of (expr ctype * abr_string region_Wrap) * (expr ctype * abr_string region_Wrap) list * fnspec list * (block_item list) region_Wrap | Decl of declaration region_Wrap;

datatype name = Name0 of int;

datatype cChar = CChar0 of char * bool | CChars0 of char list * bool;

datatype 'a flags = Flags0 of int;

datatype position = Position0 of int * abr_string * int * int | NoPosition0 | BuiltinPosition0 | InternalPosition0;

datatype nodeInfo = OnlyPos0 of position * (position * int) | NodeInfo0 of position * (position * int) * name;

datatype ident = Ident0 of abr_string * int * nodeInfo;

datatype cFloat = CFloat0 of abr_string;

datatype sUERef = AnonymousRef0 of name | NamedRef0 of ident;

datatype ('a, 'b) either = Left of 'a | Right of 'b;

datatype 'a optiona = None | Some of 'a;

datatype ('a, 'b, 'c, 'd) struct_flat = Struct_root of 'a * 'b * (('a * 'c), 'd) sum list | Struct_leaf of (('a * 'b), 'd) sum;

datatype ('a, 'b, 'c, 'd) struct_tree = Struct_tree of 'a option * 'b * ((('a, 'b, 'c, 'd) struct_tree * 'c), 'd) sum list;

datatype cString = CString0 of abr_string * bool;

datatype commentFormat = SingleLine | MultiLine;

datatype comment = Comment of position * abr_string * commentFormat;

datatype ('a, 'b, 'c, 'd, 'e, 'f) declaration0 = VarDecl0 of 'a | StructDecl0_root of 'b | StructDecl0_child of 'c | TypeDecl0 of 'd | ExtFnDecl0 of 'e | EnumDecl0 of 'f;

datatype cIntFlag = FlagUnsigned0 | FlagLong0 | FlagLongLong0 | FlagImag0;

datatype cIntRepr = DecRepr0 | HexRepr0 | OctalRepr0;

datatype cInteger = CInteger0 of int * cIntRepr * cIntFlag flags;

datatype cUnaryOp = CPreIncOp0 | CPreDecOp0 | CPostIncOp0 | CPostDecOp0 | CAdrOp0 | CIndOp0 | CPlusOp0 | CMinOp0 | CCompOp0 | CNegOp0;

datatype parsing_style = Style_Haskell | Style_ML;

datatype cAssignOp = CAssignOp0 | CMulAssOp0 | CDivAssOp0 | CRmdAssOp0 | CAddAssOp0 | CSubAssOp0 | CShlAssOp0 | CShrAssOp0 | CAndAssOp0 | CXorAssOp0 | COrAssOp0;

datatype cBinaryOp = CMulOp0 | CDivOp0 | CRmdOp0 | CAddOp0 | CSubOp0 | CShlOp0 | CShrOp0 | CLeOp0 | CGrOp0 | CLeqOp0 | CGeqOp0 | CEqOp0 | CNeqOp0 | CAndOp0 | CXorOp0 | COrOp0 | CLndOp0 | CLorOp0;

datatype 'a cConstant = CIntConst0 of cInteger * 'a | CCharConst0 of cChar * 'a | CFloatConst0 of cFloat * 'a | CStrConst0 of cString * 'a;

datatype 'a cFunctionSpecifier = CInlineQual0 of 'a | CNoreturnQual0 of 'a;

datatype 'a cStorageSpecifier = CAuto0 of 'a | CRegister0 of 'a | CStatic0 of 'a | CExtern0 of 'a | CTypedef0 of 'a | CThread0 of 'a;

datatype cStructTag = CStructTag0 | CUnionTag0;

datatype 'a cStringLiteral = CStrLit0 of cString * 'a;

datatype 'a cArraySize = CNoArrSize0 of bool | CArrSize0 of bool * 'a cExpression
and 'a cDerivedDeclarator = CPtrDeclr0 of 'a cTypeQualifier list * 'a | CArrDeclr0 of 'a cTypeQualifier list * 'a cArraySize * 'a | CFunDeclr0 of ((ident list), ('a cDeclaration list * bool)) either * 'a cAttribute list * 'a
and 'a cDeclarator = CDeclr0 of ident optiona * 'a cDerivedDeclarator list * 'a cStringLiteral optiona * 'a cAttribute list * 'a
and 'a cFunctionDef = CFunDef0 of 'a cDeclarationSpecifier list * 'a cDeclarator * 'a cDeclaration list * 'a cStatement * 'a
and 'a cCompoundBlockItem = CBlockStmt0 of 'a cStatement | CBlockDecl0 of 'a cDeclaration | CNestedFunDef0 of 'a cFunctionDef
and 'a cStatement = CLabel0 of ident * 'a cStatement * 'a cAttribute list * 'a | CCase0 of 'a cExpression * 'a cStatement * 'a | CCases0 of 'a cExpression * 'a cExpression * 'a cStatement * 'a | CDefault0 of 'a cStatement * 'a |
  CExpr0 of 'a cExpression optiona * 'a | CCompound0 of ident list * 'a cCompoundBlockItem list * 'a | CIf0 of 'a cExpression * 'a cStatement * 'a cStatement optiona * 'a | CSwitch0 of 'a cExpression * 'a cStatement * 'a |
  CWhile0 of 'a cExpression * 'a cStatement * bool * 'a | CFor0 of ('a cExpression optiona, 'a cDeclaration) either * 'a cExpression optiona * 'a cExpression optiona * 'a cStatement * 'a | CGoto0 of ident * 'a |
  CGotoPtr0 of 'a cExpression * 'a | CCont0 of 'a | CBreak0 of 'a | CReturn0 of 'a cExpression optiona * 'a | CAsm0 of 'a cAssemblyStatement * 'a
and 'a cExpression = CComma0 of 'a cExpression list * 'a | CAssign0 of cAssignOp * 'a cExpression * 'a cExpression * 'a | CCond0 of 'a cExpression * 'a cExpression optiona * 'a cExpression * 'a |
  CBinary0 of cBinaryOp * 'a cExpression * 'a cExpression * 'a | CCast0 of 'a cDeclaration * 'a cExpression * 'a | CUnary0 of cUnaryOp * 'a cExpression * 'a | CSizeofExpr0 of 'a cExpression * 'a | CSizeofType0 of 'a cDeclaration * 'a |
  CAlignofExpr0 of 'a cExpression * 'a | CAlignofType0 of 'a cDeclaration * 'a | CComplexReal0 of 'a cExpression * 'a | CComplexImag0 of 'a cExpression * 'a | CIndex0 of 'a cExpression * 'a cExpression * 'a |
  CCall0 of 'a cExpression * 'a cExpression list * 'a | CMember0 of 'a cExpression * ident * bool * 'a | CVar0 of ident * 'a | CConst0 of 'a cConstant |
  CCompoundLit0 of 'a cDeclaration * ('a cPartDesignator list * 'a cInitializer) list * 'a | CGenericSelection0 of 'a cExpression * ('a cDeclaration optiona * 'a cExpression) list * 'a | CStatExpr0 of 'a cStatement * 'a |
  CLabAddrExpr0 of ident * 'a | CBuiltinExpr0 of 'a cBuiltinThing
and 'a cAttribute = CAttr0 of ident * 'a cExpression list * 'a
and 'a cTypeQualifier = CConstQual0 of 'a | CVolatQual0 of 'a | CRestrQual0 of 'a | CAtomicQual0 of 'a | CAttrQual0 of 'a cAttribute | CNullableQual0 of 'a | CNonnullQual0 of 'a
and 'a cEnumeration = CEnum0 of ident optiona * ((ident * 'a cExpression optiona) list) optiona * 'a cAttribute list * 'a
and 'a cPartDesignator = CArrDesig0 of 'a cExpression * 'a | CMemberDesig0 of ident * 'a | CRangeDesig0 of 'a cExpression * 'a cExpression * 'a
and 'a cInitializer = CInitExpr0 of 'a cExpression * 'a | CInitList0 of ('a cPartDesignator list * 'a cInitializer) list * 'a
and 'a cAssemblyOperand = CAsmOperand0 of ident optiona * 'a cStringLiteral * 'a cExpression * 'a
and 'a cAssemblyStatement = CAsmStmt0 of 'a cTypeQualifier optiona * 'a cStringLiteral * 'a cAssemblyOperand list * 'a cAssemblyOperand list * 'a cStringLiteral list * 'a
and 'a cAlignmentSpecifier = CAlignAsType0 of 'a cDeclaration * 'a | CAlignAsExpr0 of 'a cExpression * 'a
and 'a cDeclarationSpecifier = CStorageSpec0 of 'a cStorageSpecifier | CTypeSpec0 of 'a cTypeSpecifier | CTypeQual0 of 'a cTypeQualifier | CFunSpec0 of 'a cFunctionSpecifier | CAlignSpec0 of 'a cAlignmentSpecifier
and 'a cDeclaration = CDecl0 of 'a cDeclarationSpecifier list * (('a cDeclarator optiona * 'a cInitializer optiona) * 'a cExpression optiona) list * 'a | CStaticAssert0 of 'a cExpression * 'a cStringLiteral * 'a
and 'a cBuiltinThing = CBuiltinVaArg0 of 'a cExpression * 'a cDeclaration * 'a | CBuiltinOffsetOf0 of 'a cDeclaration * 'a cPartDesignator list * 'a | CBuiltinTypesCompatible0 of 'a cDeclaration * 'a cDeclaration * 'a
and 'a cStructureUnion = CStruct0 of cStructTag * ident optiona * ('a cDeclaration list) optiona * 'a cAttribute list * 'a
and 'a cTypeSpecifier = CVoidType0 of 'a | CCharType0 of 'a | CShortType0 of 'a | CIntType0 of 'a | CLongType0 of 'a | CFloatType0 of 'a | CDoubleType0 of 'a | CSignedType0 of 'a | CUnsigType0 of 'a | CBoolType0 of 'a |
  CComplexType0 of 'a | CInt128Type0 of 'a | CSUType0 of 'a cStructureUnion * 'a | CEnumType0 of 'a cEnumeration * 'a | CTypeDef0 of ident * 'a | CTypeOfExpr0 of 'a cExpression * 'a | CTypeOfType0 of 'a cDeclaration * 'a |
  CAtomicType0 of 'a cDeclaration * 'a;

datatype clangCVersion = ClangCVersion0 of abr_string;

datatype 'a cExternalDeclaration = CDeclExt0 of 'a cDeclaration | CFDefExt0 of 'a cFunctionDef | CAsmExt0 of 'a cStringLiteral * 'a;

datatype 'a cTranslationUnit = CTranslUnit0 of 'a cExternalDeclaration list * 'a;

datatype 'a comment_type = Invariant of char list | Fnspeca of (char list * char list) list | Relspeca of char list | Modifies of ((char list) option) list | Dont_translate | Auxupda of char list | Ghostupda of char list |
  Speca of (char list * char list) | End_spec of char list | Calls of ((char list) option) list | Owned_by of char list | OTHER of 'a;

fun id x = (fn xa => xa) x;

fun plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

fun suc n = plus_nat n one_nat;

fun minus_nat m n = Nat (max ord_integer (0 : IntInf.int) (integer_of_nat m - integer_of_nat n));

fun equal_nat m n = integer_of_nat m = integer_of_nat n;

val zero_nat : nat = Nat (0 : IntInf.int);

fun nth (x :: xs) n = (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nat));

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys
  | zip xs [] = []
  | zip [] ys = [];

fun app_rev x f = f x;

val current_parsing_style : parsing_style = Style_ML;

fun mapa f [] = []
  | mapa f (x21 :: x22) = f x21 :: mapa f x22;

fun function_definition_params0 f =
  (fn a => (case a of [] => mapa f [] | CDecl0 ([], list2, xa) :: lista => mapa f (CDecl0 ([], list2, xa) :: lista)
             | CDecl0 (ab :: listb, list2, xa) :: lista =>
               (case ab of CStorageSpec0 cStorageSpecifier => mapa f (CDecl0 (CStorageSpec0 cStorageSpecifier :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CVoidType0 x) =>
                   (case listb of [] => (case list2 of [] => (case lista of [] => [] | ad :: listaa => mapa f (CDecl0 ([CTypeSpec0 (CVoidType0 x)], [], xa) :: ad :: listaa))
                                          | ad :: listba => mapa f (CDecl0 ([CTypeSpec0 (CVoidType0 x)], ad :: listba, xa) :: lista))
                     | ad :: listc => mapa f (CDecl0 (CTypeSpec0 (CVoidType0 x) :: ad :: listc, list2, xa) :: lista))
                 | CTypeSpec0 (CCharType0 aba) => mapa f (CDecl0 (CTypeSpec0 (CCharType0 aba) :: listb, list2, xa) :: lista) | CTypeSpec0 (CShortType0 aba) => mapa f (CDecl0 (CTypeSpec0 (CShortType0 aba) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CIntType0 aba) => mapa f (CDecl0 (CTypeSpec0 (CIntType0 aba) :: listb, list2, xa) :: lista) | CTypeSpec0 (CLongType0 aba) => mapa f (CDecl0 (CTypeSpec0 (CLongType0 aba) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CFloatType0 aba) => mapa f (CDecl0 (CTypeSpec0 (CFloatType0 aba) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CDoubleType0 aba) => mapa f (CDecl0 (CTypeSpec0 (CDoubleType0 aba) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CSignedType0 aba) => mapa f (CDecl0 (CTypeSpec0 (CSignedType0 aba) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CUnsigType0 aba) => mapa f (CDecl0 (CTypeSpec0 (CUnsigType0 aba) :: listb, list2, xa) :: lista) | CTypeSpec0 (CBoolType0 aba) => mapa f (CDecl0 (CTypeSpec0 (CBoolType0 aba) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CComplexType0 aba) => mapa f (CDecl0 (CTypeSpec0 (CComplexType0 aba) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CInt128Type0 aba) => mapa f (CDecl0 (CTypeSpec0 (CInt128Type0 aba) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CSUType0 (cStructureUnion, aba)) => mapa f (CDecl0 (CTypeSpec0 (CSUType0 (cStructureUnion, aba)) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CEnumType0 (cEnumeration, aba)) => mapa f (CDecl0 (CTypeSpec0 (CEnumType0 (cEnumeration, aba)) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CTypeDef0 (ident, aba)) => mapa f (CDecl0 (CTypeSpec0 (CTypeDef0 (ident, aba)) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CTypeOfExpr0 (cExpression, aba)) => mapa f (CDecl0 (CTypeSpec0 (CTypeOfExpr0 (cExpression, aba)) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CTypeOfType0 (cDeclaration, aba)) => mapa f (CDecl0 (CTypeSpec0 (CTypeOfType0 (cDeclaration, aba)) :: listb, list2, xa) :: lista)
                 | CTypeSpec0 (CAtomicType0 (cDeclaration, aba)) => mapa f (CDecl0 (CTypeSpec0 (CAtomicType0 (cDeclaration, aba)) :: listb, list2, xa) :: lista)
                 | CTypeQual0 cTypeQualifier => mapa f (CDecl0 (CTypeQual0 cTypeQualifier :: listb, list2, xa) :: lista) | CFunSpec0 cFunctionSpecifier => mapa f (CDecl0 (CFunSpec0 cFunctionSpecifier :: listb, list2, xa) :: lista)
                 | CAlignSpec0 cAlignmentSpecifier => mapa f (CDecl0 (CAlignSpec0 cAlignmentSpecifier :: listb, list2, xa) :: lista))
             | CStaticAssert0 (cExpression, cStringLiteral, aa) :: lista => mapa f (CStaticAssert0 (cExpression, cStringLiteral, aa) :: lista)));

fun flatten x = String_concatWith (SS_base (ST ""), x);

fun ident_struct_type0 s = flatten [s, SS_base (ST "_C")];

fun less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun foldl_one f accu s = foldl f accu (String.explode s);

fun foldlb f accu = (fn a => (case a of ST aa => foldl_one f accu aa | STa aa => foldl f accu aa));

fun foldla f accu e = (case e of SS_base a => foldlb f accu a | String_concatWith (abr, a) => (case a of [] => accu | x :: aa => foldl (fn accua => foldla f (foldla f accua abr)) (foldla f accu x) aa));

fun to_list s = rev (foldla (fn l => fn c => c :: l) [] s);

fun length x = foldla (fn n => fn _ => suc n) zero_nat x;

fun pref_ident s = (if less_eq_nat one_nat (length s) andalso (((nth (to_list s) zero_nat) : char) = #"_") then flatten [SS_base (ST "StrictC'"), s] else s);

fun ident_struct_type x = (fn Ident0 (s, _, _) => pref_ident (ident_struct_type0 s)) x;

fun decl_spec_ty_tag x = (fn a => (case a of CStructTag0 => StructTy | CUnionTag0 => UnionTy)) x;

fun map_option f = (fn a => (case a of None => NONE | Some x => SOME (f x)));

fun ident x = (fn Ident0 (s, _, _) => pref_ident s) x;

fun ident_option x = map_option ident x;

fun map_filter f [] = []
  | map_filter f (x :: xs) = (case f x of NONE => map_filter f xs | SOME y => y :: map_filter f xs);

fun identb x = (fn Ident0 (s, _, _) => Identa (pref_ident s)) x;

fun takeWhile p [] = []
  | takeWhile p (x :: xs) = (if p x then x :: takeWhile p xs else []);

fun dropWhile p [] = []
  | dropWhile p (x :: xs) = (if p x then dropWhile p xs else x :: xs);

fun groupBy cmp l = (case l of [] => [] | x :: xs => let
                                                       val cmp_x = cmp x;
                                                     in
                                                       (x :: takeWhile cmp_x xs) :: groupBy cmp (dropWhile cmp_x xs)
                                                     end);

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun hd (x21 :: x22) = x21;

fun decl_spec_ty l_decl_spec =
  (case map_filter (fn a => (case a of CStorageSpec0 _ => NONE | CTypeSpec0 aa => SOME aa | CTypeQual0 _ => NONE | CFunSpec0 _ => NONE | CAlignSpec0 _ => NONE)) l_decl_spec
    of [] => let
               val (siga, l) =
                 (case hd [] of CVoidType0 _ => (NONE, []) | CCharType0 _ => (NONE, []) | CShortType0 _ => (NONE, []) | CIntType0 _ => (NONE, []) | CLongType0 _ => (NONE, []) | CFloatType0 _ => (NONE, []) | CDoubleType0 _ => (NONE, [])
                   | CSignedType0 _ => (SOME Signed, tl []) | CUnsigType0 _ => (SOME Unsigned, tl []) | CBoolType0 _ => (NONE, []) | CComplexType0 _ => (NONE, []) | CInt128Type0 _ => (NONE, []) | CSUType0 (_, _) => (NONE, [])
                   | CEnumType0 (_, _) => (NONE, []) | CTypeDef0 (_, _) => (NONE, []) | CTypeOfExpr0 (_, _) => (NONE, []) | CTypeOfType0 (_, _) => (NONE, []) | CAtomicType0 (_, _) => (NONE, []));
             in
               (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                  | [CDoubleType0 _] => Double))
                                    (groupBy (fn a => fn b =>
                                               (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                 | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                 | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                 | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                 | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                 | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                 | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                 | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                      l)
                              of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                              | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                 of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                 | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
             end
    | [CVoidType0 _] => Void
    | CVoidType0 x :: ab :: lista =>
      let
        val (siga, l) =
          (case hd (CVoidType0 x :: ab :: lista) of CVoidType0 _ => (NONE, CVoidType0 x :: ab :: lista) | CCharType0 _ => (NONE, CVoidType0 x :: ab :: lista) | CShortType0 _ => (NONE, CVoidType0 x :: ab :: lista)
            | CIntType0 _ => (NONE, CVoidType0 x :: ab :: lista) | CLongType0 _ => (NONE, CVoidType0 x :: ab :: lista) | CFloatType0 _ => (NONE, CVoidType0 x :: ab :: lista) | CDoubleType0 _ => (NONE, CVoidType0 x :: ab :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CVoidType0 x :: ab :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CVoidType0 x :: ab :: lista)) | CBoolType0 _ => (NONE, CVoidType0 x :: ab :: lista)
            | CComplexType0 _ => (NONE, CVoidType0 x :: ab :: lista) | CInt128Type0 _ => (NONE, CVoidType0 x :: ab :: lista) | CSUType0 (_, _) => (NONE, CVoidType0 x :: ab :: lista)
            | CEnumType0 (_, _) => (NONE, CVoidType0 x :: ab :: lista) | CTypeDef0 (_, _) => (NONE, CVoidType0 x :: ab :: lista) | CTypeOfExpr0 (_, _) => (NONE, CVoidType0 x :: ab :: lista)
            | CTypeOfType0 (_, _) => (NONE, CVoidType0 x :: ab :: lista) | CAtomicType0 (_, _) => (NONE, CVoidType0 x :: ab :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CCharType0 aa :: lista =>
      let
        val (siga, l) =
          (case hd (CCharType0 aa :: lista) of CVoidType0 _ => (NONE, CCharType0 aa :: lista) | CCharType0 _ => (NONE, CCharType0 aa :: lista) | CShortType0 _ => (NONE, CCharType0 aa :: lista)
            | CIntType0 _ => (NONE, CCharType0 aa :: lista) | CLongType0 _ => (NONE, CCharType0 aa :: lista) | CFloatType0 _ => (NONE, CCharType0 aa :: lista) | CDoubleType0 _ => (NONE, CCharType0 aa :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CCharType0 aa :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CCharType0 aa :: lista)) | CBoolType0 _ => (NONE, CCharType0 aa :: lista)
            | CComplexType0 _ => (NONE, CCharType0 aa :: lista) | CInt128Type0 _ => (NONE, CCharType0 aa :: lista) | CSUType0 (_, _) => (NONE, CCharType0 aa :: lista) | CEnumType0 (_, _) => (NONE, CCharType0 aa :: lista)
            | CTypeDef0 (_, _) => (NONE, CCharType0 aa :: lista) | CTypeOfExpr0 (_, _) => (NONE, CCharType0 aa :: lista) | CTypeOfType0 (_, _) => (NONE, CCharType0 aa :: lista) | CAtomicType0 (_, _) => (NONE, CCharType0 aa :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | [CShortType0 x] =>
      let
        val (siga, l) =
          (case hd [CShortType0 x] of CVoidType0 _ => (NONE, [CShortType0 x]) | CCharType0 _ => (NONE, [CShortType0 x]) | CShortType0 _ => (NONE, [CShortType0 x]) | CIntType0 _ => (NONE, [CShortType0 x])
            | CLongType0 _ => (NONE, [CShortType0 x]) | CFloatType0 _ => (NONE, [CShortType0 x]) | CDoubleType0 _ => (NONE, [CShortType0 x]) | CSignedType0 _ => (SOME Signed, tl [CShortType0 x])
            | CUnsigType0 _ => (SOME Unsigned, tl [CShortType0 x]) | CBoolType0 _ => (NONE, [CShortType0 x]) | CComplexType0 _ => (NONE, [CShortType0 x]) | CInt128Type0 _ => (NONE, [CShortType0 x])
            | CSUType0 (_, _) => (NONE, [CShortType0 x]) | CEnumType0 (_, _) => (NONE, [CShortType0 x]) | CTypeDef0 (_, _) => (NONE, [CShortType0 x]) | CTypeOfExpr0 (_, _) => (NONE, [CShortType0 x])
            | CTypeOfType0 (_, _) => (NONE, [CShortType0 x]) | CAtomicType0 (_, _) => (NONE, [CShortType0 x]));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CVoidType0 ac :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CVoidType0 ac :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CVoidType0 ac :: lista) | CCharType0 _ => (NONE, CShortType0 x :: CVoidType0 ac :: lista)
            | CShortType0 _ => (NONE, CShortType0 x :: CVoidType0 ac :: lista) | CIntType0 _ => (NONE, CShortType0 x :: CVoidType0 ac :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CVoidType0 ac :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CVoidType0 ac :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CVoidType0 ac :: lista) | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CVoidType0 ac :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CVoidType0 ac :: lista)) | CBoolType0 _ => (NONE, CShortType0 x :: CVoidType0 ac :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CVoidType0 ac :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CVoidType0 ac :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CVoidType0 ac :: lista) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CVoidType0 ac :: lista)
            | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CVoidType0 ac :: lista) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CVoidType0 ac :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CVoidType0 ac :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CVoidType0 ac :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CCharType0 ac :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CCharType0 ac :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CCharType0 ac :: lista) | CCharType0 _ => (NONE, CShortType0 x :: CCharType0 ac :: lista)
            | CShortType0 _ => (NONE, CShortType0 x :: CCharType0 ac :: lista) | CIntType0 _ => (NONE, CShortType0 x :: CCharType0 ac :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CCharType0 ac :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CCharType0 ac :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CCharType0 ac :: lista) | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CCharType0 ac :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CCharType0 ac :: lista)) | CBoolType0 _ => (NONE, CShortType0 x :: CCharType0 ac :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CCharType0 ac :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CCharType0 ac :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CCharType0 ac :: lista) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CCharType0 ac :: lista)
            | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CCharType0 ac :: lista) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CCharType0 ac :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CCharType0 ac :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CCharType0 ac :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CShortType0 ac :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CShortType0 ac :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CShortType0 ac :: lista) | CCharType0 _ => (NONE, CShortType0 x :: CShortType0 ac :: lista)
            | CShortType0 _ => (NONE, CShortType0 x :: CShortType0 ac :: lista) | CIntType0 _ => (NONE, CShortType0 x :: CShortType0 ac :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CShortType0 ac :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CShortType0 ac :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CShortType0 ac :: lista) | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CShortType0 ac :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CShortType0 ac :: lista)) | CBoolType0 _ => (NONE, CShortType0 x :: CShortType0 ac :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CShortType0 ac :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CShortType0 ac :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CShortType0 ac :: lista) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CShortType0 ac :: lista)
            | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CShortType0 ac :: lista) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CShortType0 ac :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CShortType0 ac :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CShortType0 ac :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CIntType0 ac :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CIntType0 ac :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CIntType0 ac :: lista) | CCharType0 _ => (NONE, CShortType0 x :: CIntType0 ac :: lista)
            | CShortType0 _ => (NONE, CShortType0 x :: CIntType0 ac :: lista) | CIntType0 _ => (NONE, CShortType0 x :: CIntType0 ac :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CIntType0 ac :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CIntType0 ac :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CIntType0 ac :: lista) | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CIntType0 ac :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CIntType0 ac :: lista)) | CBoolType0 _ => (NONE, CShortType0 x :: CIntType0 ac :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CIntType0 ac :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CIntType0 ac :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CIntType0 ac :: lista) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CIntType0 ac :: lista)
            | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CIntType0 ac :: lista) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CIntType0 ac :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CIntType0 ac :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CIntType0 ac :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CLongType0 ac :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CLongType0 ac :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CLongType0 ac :: lista) | CCharType0 _ => (NONE, CShortType0 x :: CLongType0 ac :: lista)
            | CShortType0 _ => (NONE, CShortType0 x :: CLongType0 ac :: lista) | CIntType0 _ => (NONE, CShortType0 x :: CLongType0 ac :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CLongType0 ac :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CLongType0 ac :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CLongType0 ac :: lista) | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CLongType0 ac :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CLongType0 ac :: lista)) | CBoolType0 _ => (NONE, CShortType0 x :: CLongType0 ac :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CLongType0 ac :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CLongType0 ac :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CLongType0 ac :: lista) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CLongType0 ac :: lista)
            | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CLongType0 ac :: lista) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CLongType0 ac :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CLongType0 ac :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CLongType0 ac :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CFloatType0 ac :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CFloatType0 ac :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CFloatType0 ac :: lista) | CCharType0 _ => (NONE, CShortType0 x :: CFloatType0 ac :: lista)
            | CShortType0 _ => (NONE, CShortType0 x :: CFloatType0 ac :: lista) | CIntType0 _ => (NONE, CShortType0 x :: CFloatType0 ac :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CFloatType0 ac :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CFloatType0 ac :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CFloatType0 ac :: lista) | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CFloatType0 ac :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CFloatType0 ac :: lista)) | CBoolType0 _ => (NONE, CShortType0 x :: CFloatType0 ac :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CFloatType0 ac :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CFloatType0 ac :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CFloatType0 ac :: lista) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CFloatType0 ac :: lista)
            | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CFloatType0 ac :: lista) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CFloatType0 ac :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CFloatType0 ac :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CFloatType0 ac :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CDoubleType0 ac :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CDoubleType0 ac :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CDoubleType0 ac :: lista) | CCharType0 _ => (NONE, CShortType0 x :: CDoubleType0 ac :: lista)
            | CShortType0 _ => (NONE, CShortType0 x :: CDoubleType0 ac :: lista) | CIntType0 _ => (NONE, CShortType0 x :: CDoubleType0 ac :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CDoubleType0 ac :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CDoubleType0 ac :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CDoubleType0 ac :: lista) | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CDoubleType0 ac :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CDoubleType0 ac :: lista)) | CBoolType0 _ => (NONE, CShortType0 x :: CDoubleType0 ac :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CDoubleType0 ac :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CDoubleType0 ac :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CDoubleType0 ac :: lista) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CDoubleType0 ac :: lista)
            | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CDoubleType0 ac :: lista) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CDoubleType0 ac :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CDoubleType0 ac :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CDoubleType0 ac :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CSignedType0 ac :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CSignedType0 ac :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CSignedType0 ac :: lista) | CCharType0 _ => (NONE, CShortType0 x :: CSignedType0 ac :: lista)
            | CShortType0 _ => (NONE, CShortType0 x :: CSignedType0 ac :: lista) | CIntType0 _ => (NONE, CShortType0 x :: CSignedType0 ac :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CSignedType0 ac :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CSignedType0 ac :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CSignedType0 ac :: lista) | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CSignedType0 ac :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CSignedType0 ac :: lista)) | CBoolType0 _ => (NONE, CShortType0 x :: CSignedType0 ac :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CSignedType0 ac :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CSignedType0 ac :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CSignedType0 ac :: lista) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CSignedType0 ac :: lista)
            | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CSignedType0 ac :: lista) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CSignedType0 ac :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CSignedType0 ac :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CSignedType0 ac :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CUnsigType0 xa :: lista =>
      (case lista of [] => let
                             val (siga, l) =
                               (case hd [CShortType0 x, CUnsigType0 xa] of CVoidType0 _ => (NONE, [CShortType0 x, CUnsigType0 xa]) | CCharType0 _ => (NONE, [CShortType0 x, CUnsigType0 xa])
                                 | CShortType0 _ => (NONE, [CShortType0 x, CUnsigType0 xa]) | CIntType0 _ => (NONE, [CShortType0 x, CUnsigType0 xa]) | CLongType0 _ => (NONE, [CShortType0 x, CUnsigType0 xa])
                                 | CFloatType0 _ => (NONE, [CShortType0 x, CUnsigType0 xa]) | CDoubleType0 _ => (NONE, [CShortType0 x, CUnsigType0 xa]) | CSignedType0 _ => (SOME Signed, tl [CShortType0 x, CUnsigType0 xa])
                                 | CUnsigType0 _ => (SOME Unsigned, tl [CShortType0 x, CUnsigType0 xa]) | CBoolType0 _ => (NONE, [CShortType0 x, CUnsigType0 xa]) | CComplexType0 _ => (NONE, [CShortType0 x, CUnsigType0 xa])
                                 | CInt128Type0 _ => (NONE, [CShortType0 x, CUnsigType0 xa]) | CSUType0 (_, _) => (NONE, [CShortType0 x, CUnsigType0 xa]) | CEnumType0 (_, _) => (NONE, [CShortType0 x, CUnsigType0 xa])
                                 | CTypeDef0 (_, _) => (NONE, [CShortType0 x, CUnsigType0 xa]) | CTypeOfExpr0 (_, _) => (NONE, [CShortType0 x, CUnsigType0 xa]) | CTypeOfType0 (_, _) => (NONE, [CShortType0 x, CUnsigType0 xa])
                                 | CAtomicType0 (_, _) => (NONE, [CShortType0 x, CUnsigType0 xa]));
                           in
                             (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong
                                                                | [CFloatType0 _] => Float | [CDoubleType0 _] => Double))
                                                  (groupBy (fn a => fn b =>
                                                             (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                               | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                               | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                               | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                               | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false
                                                               | (CLongType0 _, CTypeOfType0 (_, _)) => false | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false
                                                               | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false
                                                               | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false
                                                               | (CAtomicType0 (_, _), _) => false))
                                                    l)
                                            of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                                            | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                               of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                               | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
                           end
        | CVoidType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CCharType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CShortType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | [CIntType0 _] => Unsigned Short
        | CIntType0 xb :: af :: listaa =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CFloatType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CDoubleType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CSignedType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CUnsigType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CBoolType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CComplexType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CInt128Type0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CSUType0 (cStructureUnion, ae) :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb))
                | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)) | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CEnumType0 (cEnumeration, ae) :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb))
                | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)) | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CTypeDef0 (ident, ae) :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb))
                | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CTypeOfExpr0 (cExpression, ae) :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb))
                | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)) | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CTypeOfType0 (cDeclaration, ae) :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb))
                | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)) | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CAtomicType0 (cDeclaration, ae) :: listb =>
          let
            val (siga, l) =
              (case hd (CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) of CVoidType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CCharType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CShortType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CIntType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CLongType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CFloatType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CDoubleType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb))
                | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)) | CBoolType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CComplexType0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CInt128Type0 _ => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CSUType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end)
    | CShortType0 x :: CBoolType0 ac :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CBoolType0 ac :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CBoolType0 ac :: lista) | CCharType0 _ => (NONE, CShortType0 x :: CBoolType0 ac :: lista)
            | CShortType0 _ => (NONE, CShortType0 x :: CBoolType0 ac :: lista) | CIntType0 _ => (NONE, CShortType0 x :: CBoolType0 ac :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CBoolType0 ac :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CBoolType0 ac :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CBoolType0 ac :: lista) | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CBoolType0 ac :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CBoolType0 ac :: lista)) | CBoolType0 _ => (NONE, CShortType0 x :: CBoolType0 ac :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CBoolType0 ac :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CBoolType0 ac :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CBoolType0 ac :: lista) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CBoolType0 ac :: lista)
            | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CBoolType0 ac :: lista) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CBoolType0 ac :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CBoolType0 ac :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CBoolType0 ac :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CComplexType0 ac :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CComplexType0 ac :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CComplexType0 ac :: lista) | CCharType0 _ => (NONE, CShortType0 x :: CComplexType0 ac :: lista)
            | CShortType0 _ => (NONE, CShortType0 x :: CComplexType0 ac :: lista) | CIntType0 _ => (NONE, CShortType0 x :: CComplexType0 ac :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CComplexType0 ac :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CComplexType0 ac :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CComplexType0 ac :: lista) | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CComplexType0 ac :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CComplexType0 ac :: lista)) | CBoolType0 _ => (NONE, CShortType0 x :: CComplexType0 ac :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CComplexType0 ac :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CComplexType0 ac :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CComplexType0 ac :: lista) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CComplexType0 ac :: lista)
            | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CComplexType0 ac :: lista) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CComplexType0 ac :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CComplexType0 ac :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CComplexType0 ac :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CInt128Type0 ac :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CInt128Type0 ac :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CInt128Type0 ac :: lista) | CCharType0 _ => (NONE, CShortType0 x :: CInt128Type0 ac :: lista)
            | CShortType0 _ => (NONE, CShortType0 x :: CInt128Type0 ac :: lista) | CIntType0 _ => (NONE, CShortType0 x :: CInt128Type0 ac :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CInt128Type0 ac :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CInt128Type0 ac :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CInt128Type0 ac :: lista) | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CInt128Type0 ac :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CInt128Type0 ac :: lista)) | CBoolType0 _ => (NONE, CShortType0 x :: CInt128Type0 ac :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CInt128Type0 ac :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CInt128Type0 ac :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CInt128Type0 ac :: lista) | CEnumType0 (_, _) => (NONE, CShortType0 x :: CInt128Type0 ac :: lista)
            | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CInt128Type0 ac :: lista) | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CInt128Type0 ac :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CInt128Type0 ac :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CInt128Type0 ac :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista)
            | CCharType0 _ => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista) | CShortType0 _ => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista)
            | CIntType0 _ => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista))
            | CBoolType0 _ => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista)
            | CEnumType0 (_, _) => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista)
            | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CSUType0 (cStructureUnion, ac) :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista)
            | CCharType0 _ => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista) | CShortType0 _ => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista)
            | CIntType0 _ => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista))
            | CBoolType0 _ => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista)
            | CEnumType0 (_, _) => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista)
            | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CEnumType0 (cEnumeration, ac) :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CTypeDef0 (ident, ac) :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CTypeDef0 (ident, ac) :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista) | CCharType0 _ => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista)
            | CShortType0 _ => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista) | CIntType0 _ => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CTypeDef0 (ident, ac) :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CTypeDef0 (ident, ac) :: lista))
            | CBoolType0 _ => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista)
            | CEnumType0 (_, _) => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista)
            | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CTypeDef0 (ident, ac) :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista)
            | CCharType0 _ => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista) | CShortType0 _ => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista)
            | CIntType0 _ => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista))
            | CBoolType0 _ => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista)
            | CEnumType0 (_, _) => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista)
            | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CTypeOfExpr0 (cExpression, ac) :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista)
            | CCharType0 _ => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista) | CShortType0 _ => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista)
            | CIntType0 _ => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista))
            | CBoolType0 _ => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista)
            | CEnumType0 (_, _) => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista)
            | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CTypeOfType0 (cDeclaration, ac) :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista =>
      let
        val (siga, l) =
          (case hd (CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista) of CVoidType0 _ => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista)
            | CCharType0 _ => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista) | CShortType0 _ => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista)
            | CIntType0 _ => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista) | CLongType0 _ => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista)
            | CFloatType0 _ => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista) | CDoubleType0 _ => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista))
            | CBoolType0 _ => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista) | CComplexType0 _ => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista)
            | CInt128Type0 _ => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista) | CSUType0 (_, _) => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista)
            | CEnumType0 (_, _) => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista) | CTypeDef0 (_, _) => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista)
            | CTypeOfExpr0 (_, _) => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista) | CTypeOfType0 (_, _) => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista)
            | CAtomicType0 (_, _) => (NONE, CShortType0 x :: CAtomicType0 (cDeclaration, ac) :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CIntType0 aa :: lista =>
      let
        val (siga, l) =
          (case hd (CIntType0 aa :: lista) of CVoidType0 _ => (NONE, CIntType0 aa :: lista) | CCharType0 _ => (NONE, CIntType0 aa :: lista) | CShortType0 _ => (NONE, CIntType0 aa :: lista) | CIntType0 _ => (NONE, CIntType0 aa :: lista)
            | CLongType0 _ => (NONE, CIntType0 aa :: lista) | CFloatType0 _ => (NONE, CIntType0 aa :: lista) | CDoubleType0 _ => (NONE, CIntType0 aa :: lista) | CSignedType0 _ => (SOME Signed, tl (CIntType0 aa :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CIntType0 aa :: lista)) | CBoolType0 _ => (NONE, CIntType0 aa :: lista) | CComplexType0 _ => (NONE, CIntType0 aa :: lista) | CInt128Type0 _ => (NONE, CIntType0 aa :: lista)
            | CSUType0 (_, _) => (NONE, CIntType0 aa :: lista) | CEnumType0 (_, _) => (NONE, CIntType0 aa :: lista) | CTypeDef0 (_, _) => (NONE, CIntType0 aa :: lista) | CTypeOfExpr0 (_, _) => (NONE, CIntType0 aa :: lista)
            | CTypeOfType0 (_, _) => (NONE, CIntType0 aa :: lista) | CAtomicType0 (_, _) => (NONE, CIntType0 aa :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CLongType0 x :: lista =>
      (case lista of [] => let
                             val (siga, l) =
                               (case hd [CLongType0 x] of CVoidType0 _ => (NONE, [CLongType0 x]) | CCharType0 _ => (NONE, [CLongType0 x]) | CShortType0 _ => (NONE, [CLongType0 x]) | CIntType0 _ => (NONE, [CLongType0 x])
                                 | CLongType0 _ => (NONE, [CLongType0 x]) | CFloatType0 _ => (NONE, [CLongType0 x]) | CDoubleType0 _ => (NONE, [CLongType0 x]) | CSignedType0 _ => (SOME Signed, tl [CLongType0 x])
                                 | CUnsigType0 _ => (SOME Unsigned, tl [CLongType0 x]) | CBoolType0 _ => (NONE, [CLongType0 x]) | CComplexType0 _ => (NONE, [CLongType0 x]) | CInt128Type0 _ => (NONE, [CLongType0 x])
                                 | CSUType0 (_, _) => (NONE, [CLongType0 x]) | CEnumType0 (_, _) => (NONE, [CLongType0 x]) | CTypeDef0 (_, _) => (NONE, [CLongType0 x]) | CTypeOfExpr0 (_, _) => (NONE, [CLongType0 x])
                                 | CTypeOfType0 (_, _) => (NONE, [CLongType0 x]) | CAtomicType0 (_, _) => (NONE, [CLongType0 x]));
                           in
                             (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong
                                                                | [CFloatType0 _] => Float | [CDoubleType0 _] => Double))
                                                  (groupBy (fn a => fn b =>
                                                             (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                               | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                               | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                               | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                               | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false
                                                               | (CLongType0 _, CTypeOfType0 (_, _)) => false | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false
                                                               | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false
                                                               | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false
                                                               | (CAtomicType0 (_, _), _) => false))
                                                    l)
                                            of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                                            | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                               of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                               | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
                           end
        | CVoidType0 ac :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CVoidType0 ac :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CVoidType0 ac :: listaa) | CCharType0 _ => (NONE, CLongType0 x :: CVoidType0 ac :: listaa)
                | CShortType0 _ => (NONE, CLongType0 x :: CVoidType0 ac :: listaa) | CIntType0 _ => (NONE, CLongType0 x :: CVoidType0 ac :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CVoidType0 ac :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CVoidType0 ac :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CVoidType0 ac :: listaa) | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CVoidType0 ac :: listaa))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CVoidType0 ac :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CVoidType0 ac :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CVoidType0 ac :: listaa)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CVoidType0 ac :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CVoidType0 ac :: listaa) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CVoidType0 ac :: listaa)
                | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CVoidType0 ac :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CVoidType0 ac :: listaa) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CVoidType0 ac :: listaa)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CVoidType0 ac :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CCharType0 ac :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CCharType0 ac :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CCharType0 ac :: listaa) | CCharType0 _ => (NONE, CLongType0 x :: CCharType0 ac :: listaa)
                | CShortType0 _ => (NONE, CLongType0 x :: CCharType0 ac :: listaa) | CIntType0 _ => (NONE, CLongType0 x :: CCharType0 ac :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CCharType0 ac :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CCharType0 ac :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CCharType0 ac :: listaa) | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CCharType0 ac :: listaa))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CCharType0 ac :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CCharType0 ac :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CCharType0 ac :: listaa)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CCharType0 ac :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CCharType0 ac :: listaa) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CCharType0 ac :: listaa)
                | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CCharType0 ac :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CCharType0 ac :: listaa) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CCharType0 ac :: listaa)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CCharType0 ac :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CShortType0 ac :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CShortType0 ac :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CShortType0 ac :: listaa) | CCharType0 _ => (NONE, CLongType0 x :: CShortType0 ac :: listaa)
                | CShortType0 _ => (NONE, CLongType0 x :: CShortType0 ac :: listaa) | CIntType0 _ => (NONE, CLongType0 x :: CShortType0 ac :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CShortType0 ac :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CShortType0 ac :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CShortType0 ac :: listaa) | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CShortType0 ac :: listaa))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CShortType0 ac :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CShortType0 ac :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CShortType0 ac :: listaa)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CShortType0 ac :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CShortType0 ac :: listaa) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CShortType0 ac :: listaa)
                | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CShortType0 ac :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CShortType0 ac :: listaa) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CShortType0 ac :: listaa)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CShortType0 ac :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CIntType0 ac :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CIntType0 ac :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CIntType0 ac :: listaa) | CCharType0 _ => (NONE, CLongType0 x :: CIntType0 ac :: listaa)
                | CShortType0 _ => (NONE, CLongType0 x :: CIntType0 ac :: listaa) | CIntType0 _ => (NONE, CLongType0 x :: CIntType0 ac :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CIntType0 ac :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CIntType0 ac :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CIntType0 ac :: listaa) | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CIntType0 ac :: listaa))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CIntType0 ac :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CIntType0 ac :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CIntType0 ac :: listaa)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CIntType0 ac :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CIntType0 ac :: listaa) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CIntType0 ac :: listaa)
                | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CIntType0 ac :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CIntType0 ac :: listaa) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CIntType0 ac :: listaa)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CIntType0 ac :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | [CLongType0 xa] =>
          let
            val (siga, l) =
              (case hd [CLongType0 x, CLongType0 xa] of CVoidType0 _ => (NONE, [CLongType0 x, CLongType0 xa]) | CCharType0 _ => (NONE, [CLongType0 x, CLongType0 xa]) | CShortType0 _ => (NONE, [CLongType0 x, CLongType0 xa])
                | CIntType0 _ => (NONE, [CLongType0 x, CLongType0 xa]) | CLongType0 _ => (NONE, [CLongType0 x, CLongType0 xa]) | CFloatType0 _ => (NONE, [CLongType0 x, CLongType0 xa])
                | CDoubleType0 _ => (NONE, [CLongType0 x, CLongType0 xa]) | CSignedType0 _ => (SOME Signed, tl [CLongType0 x, CLongType0 xa]) | CUnsigType0 _ => (SOME Unsigned, tl [CLongType0 x, CLongType0 xa])
                | CBoolType0 _ => (NONE, [CLongType0 x, CLongType0 xa]) | CComplexType0 _ => (NONE, [CLongType0 x, CLongType0 xa]) | CInt128Type0 _ => (NONE, [CLongType0 x, CLongType0 xa])
                | CSUType0 (_, _) => (NONE, [CLongType0 x, CLongType0 xa]) | CEnumType0 (_, _) => (NONE, [CLongType0 x, CLongType0 xa]) | CTypeDef0 (_, _) => (NONE, [CLongType0 x, CLongType0 xa])
                | CTypeOfExpr0 (_, _) => (NONE, [CLongType0 x, CLongType0 xa]) | CTypeOfType0 (_, _) => (NONE, [CLongType0 x, CLongType0 xa]) | CAtomicType0 (_, _) => (NONE, [CLongType0 x, CLongType0 xa]));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CVoidType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb))
                | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CVoidType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CCharType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb))
                | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CCharType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CShortType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb))
                | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CShortType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CIntType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb))
                | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CIntType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CLongType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb))
                | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CLongType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CFloatType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb))
                | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CFloatType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CDoubleType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb))
                | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CDoubleType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CSignedType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb))
                | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CSignedType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CUnsigType0 xb :: listb =>
          (case listb of [] => let
                                 val (siga, l) =
                                   (case hd [CLongType0 x, CLongType0 xa, CUnsigType0 xb] of CVoidType0 _ => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb]) | CCharType0 _ => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb])
                                     | CShortType0 _ => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb]) | CIntType0 _ => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb])
                                     | CLongType0 _ => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb]) | CFloatType0 _ => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb])
                                     | CDoubleType0 _ => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb]) | CSignedType0 _ => (SOME Signed, tl [CLongType0 x, CLongType0 xa, CUnsigType0 xb])
                                     | CUnsigType0 _ => (SOME Unsigned, tl [CLongType0 x, CLongType0 xa, CUnsigType0 xb]) | CBoolType0 _ => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb])
                                     | CComplexType0 _ => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb]) | CInt128Type0 _ => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb])
                                     | CSUType0 (_, _) => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb]) | CEnumType0 (_, _) => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb])
                                     | CTypeDef0 (_, _) => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb]) | CTypeOfExpr0 (_, _) => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb])
                                     | CTypeOfType0 (_, _) => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb]) | CAtomicType0 (_, _) => (NONE, [CLongType0 x, CLongType0 xa, CUnsigType0 xb]));
                               in
                                 (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong
                                                                    | [CFloatType0 _] => Float | [CDoubleType0 _] => Double))
                                                      (groupBy (fn a => fn b =>
                                                                 (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                                   | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                                   | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                                   | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                                   | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false
                                                                   | (CLongType0 _, CTypeOfType0 (_, _)) => false | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false
                                                                   | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false
                                                                   | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false
                                                                   | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                                        l)
                                                of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                                                | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                                   of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                                   | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
                               end
            | CVoidType0 ag :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa) | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CVoidType0 ag :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CCharType0 ag :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa) | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CCharType0 ag :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CShortType0 ag :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CShortType0 ag :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | [CIntType0 _] => Unsigned LongLong
            | CIntType0 xc :: ah :: listc =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CIntType0 xc :: ah :: listc));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CLongType0 ag :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa) | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CLongType0 ag :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CFloatType0 ag :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CFloatType0 ag :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CDoubleType0 ag :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CDoubleType0 ag :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CSignedType0 ag :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSignedType0 ag :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CUnsigType0 ag :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CUnsigType0 ag :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CBoolType0 ag :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa) | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CBoolType0 ag :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CComplexType0 ag :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CComplexType0 ag :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CInt128Type0 ag :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CInt128Type0 ag :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CSUType0 (cStructureUnion, ag) :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CSUType0 (cStructureUnion, ag) :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CEnumType0 (cEnumeration, ag) :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CEnumType0 (cEnumeration, ag) :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CTypeDef0 (ident, ag) :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeDef0 (ident, ag) :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CTypeOfExpr0 (cExpression, ag) :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfExpr0 (cExpression, ag) :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CTypeOfType0 (cDeclaration, ag) :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CTypeOfType0 (cDeclaration, ag) :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CAtomicType0 (cDeclaration, ag) :: listaa =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CUnsigType0 xb :: CAtomicType0 (cDeclaration, ag) :: listaa));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end)
        | CLongType0 xa :: CBoolType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb))
                | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CBoolType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CComplexType0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb))
                | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CComplexType0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CInt128Type0 ae :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb))
                | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CInt128Type0 ae :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)) | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CSUType0 (cStructureUnion, ae) :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)) | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CEnumType0 (cEnumeration, ae) :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CTypeDef0 (ident, ae) :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb))
                | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeDef0 (ident, ae) :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)) | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)) | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CCharType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CIntType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CFloatType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)) | CBoolType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CComplexType0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CInt128Type0 _ => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CSUType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CLongType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CFloatType0 ac :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CFloatType0 ac :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CFloatType0 ac :: listaa) | CCharType0 _ => (NONE, CLongType0 x :: CFloatType0 ac :: listaa)
                | CShortType0 _ => (NONE, CLongType0 x :: CFloatType0 ac :: listaa) | CIntType0 _ => (NONE, CLongType0 x :: CFloatType0 ac :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CFloatType0 ac :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CFloatType0 ac :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CFloatType0 ac :: listaa) | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CFloatType0 ac :: listaa))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CFloatType0 ac :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CFloatType0 ac :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CFloatType0 ac :: listaa)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CFloatType0 ac :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CFloatType0 ac :: listaa) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CFloatType0 ac :: listaa)
                | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CFloatType0 ac :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CFloatType0 ac :: listaa) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CFloatType0 ac :: listaa)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CFloatType0 ac :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CDoubleType0 ac :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CDoubleType0 ac :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa) | CCharType0 _ => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa)
                | CShortType0 _ => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa) | CIntType0 _ => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa) | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CDoubleType0 ac :: listaa))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CDoubleType0 ac :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa)
                | CComplexType0 _ => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa) | CInt128Type0 _ => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa)
                | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa) | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CDoubleType0 ac :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CSignedType0 ac :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CSignedType0 ac :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CSignedType0 ac :: listaa) | CCharType0 _ => (NONE, CLongType0 x :: CSignedType0 ac :: listaa)
                | CShortType0 _ => (NONE, CLongType0 x :: CSignedType0 ac :: listaa) | CIntType0 _ => (NONE, CLongType0 x :: CSignedType0 ac :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CSignedType0 ac :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CSignedType0 ac :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CSignedType0 ac :: listaa) | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CSignedType0 ac :: listaa))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CSignedType0 ac :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CSignedType0 ac :: listaa)
                | CComplexType0 _ => (NONE, CLongType0 x :: CSignedType0 ac :: listaa) | CInt128Type0 _ => (NONE, CLongType0 x :: CSignedType0 ac :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CSignedType0 ac :: listaa)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CSignedType0 ac :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CSignedType0 ac :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CSignedType0 ac :: listaa)
                | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CSignedType0 ac :: listaa) | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CSignedType0 ac :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CUnsigType0 xa :: listaa =>
          (case listaa of [] => let
                                  val (siga, l) =
                                    (case hd [CLongType0 x, CUnsigType0 xa] of CVoidType0 _ => (NONE, [CLongType0 x, CUnsigType0 xa]) | CCharType0 _ => (NONE, [CLongType0 x, CUnsigType0 xa])
                                      | CShortType0 _ => (NONE, [CLongType0 x, CUnsigType0 xa]) | CIntType0 _ => (NONE, [CLongType0 x, CUnsigType0 xa]) | CLongType0 _ => (NONE, [CLongType0 x, CUnsigType0 xa])
                                      | CFloatType0 _ => (NONE, [CLongType0 x, CUnsigType0 xa]) | CDoubleType0 _ => (NONE, [CLongType0 x, CUnsigType0 xa]) | CSignedType0 _ => (SOME Signed, tl [CLongType0 x, CUnsigType0 xa])
                                      | CUnsigType0 _ => (SOME Unsigned, tl [CLongType0 x, CUnsigType0 xa]) | CBoolType0 _ => (NONE, [CLongType0 x, CUnsigType0 xa]) | CComplexType0 _ => (NONE, [CLongType0 x, CUnsigType0 xa])
                                      | CInt128Type0 _ => (NONE, [CLongType0 x, CUnsigType0 xa]) | CSUType0 (_, _) => (NONE, [CLongType0 x, CUnsigType0 xa]) | CEnumType0 (_, _) => (NONE, [CLongType0 x, CUnsigType0 xa])
                                      | CTypeDef0 (_, _) => (NONE, [CLongType0 x, CUnsigType0 xa]) | CTypeOfExpr0 (_, _) => (NONE, [CLongType0 x, CUnsigType0 xa]) | CTypeOfType0 (_, _) => (NONE, [CLongType0 x, CUnsigType0 xa])
                                      | CAtomicType0 (_, _) => (NONE, [CLongType0 x, CUnsigType0 xa]));
                                in
                                  (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong
                                                                     | [CFloatType0 _] => Float | [CDoubleType0 _] => Double))
                                                       (groupBy (fn a => fn b =>
                                                                  (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                                    | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                                    | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                                    | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                                    | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false
                                                                    | (CLongType0 _, CTypeOfType0 (_, _)) => false | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false
                                                                    | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false
                                                                    | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false
                                                                    | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                                         l)
                                                 of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                                                 | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                                    of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                                    | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
                                end
            | CVoidType0 ae :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CVoidType0 ae :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CCharType0 ae :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CCharType0 ae :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CShortType0 ae :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CShortType0 ae :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | [CIntType0 _] => Unsigned Long
            | CIntType0 xb :: af :: listab =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CIntType0 xb :: af :: listab));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CLongType0 ae :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CLongType0 ae :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CFloatType0 ae :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CFloatType0 ae :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CDoubleType0 ae :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CDoubleType0 ae :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CSignedType0 ae :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CSignedType0 ae :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CUnsigType0 ae :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CUnsigType0 ae :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CBoolType0 ae :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CBoolType0 ae :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CComplexType0 ae :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CComplexType0 ae :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CInt128Type0 ae :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CInt128Type0 ae :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CSUType0 (cStructureUnion, ae) :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)) | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CSUType0 (cStructureUnion, ae) :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CEnumType0 (cEnumeration, ae) :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)) | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CEnumType0 (cEnumeration, ae) :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CTypeDef0 (ident, ae) :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb))
                    | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                    | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                    | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                    | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeDef0 (ident, ae) :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CTypeOfExpr0 (cExpression, ae) :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)) | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb) | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfExpr0 (cExpression, ae) :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CTypeOfType0 (cDeclaration, ae) :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)) | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CTypeOfType0 (cDeclaration, ae) :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end
            | CAtomicType0 (cDeclaration, ae) :: listb =>
              let
                val (siga, l) =
                  (case hd (CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) of CVoidType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                    | CCharType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CShortType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                    | CIntType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CLongType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                    | CFloatType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CDoubleType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                    | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb))
                    | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)) | CBoolType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                    | CComplexType0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CInt128Type0 _ => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                    | CSUType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                    | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                    | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb)
                    | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CUnsigType0 xa :: CAtomicType0 (cDeclaration, ae) :: listb));
              in
                (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                                   | [CDoubleType0 _] => Double))
                                     (groupBy (fn a => fn b =>
                                                (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                                  | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                                  | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                                  | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                                  | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                                  | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                                  | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false
                                                  | (CTypeDef0 (_, _), _) => false | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                       l)
                               of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong
                               | [LongLong, Int] => LongLong | [Double] => Double | [Float] => Float))
                  of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double
                  | (NONE, Float) => Signed Float | (SOME sigb, ty) => sigb ty)
              end)
        | CBoolType0 ac :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CBoolType0 ac :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CBoolType0 ac :: listaa) | CCharType0 _ => (NONE, CLongType0 x :: CBoolType0 ac :: listaa)
                | CShortType0 _ => (NONE, CLongType0 x :: CBoolType0 ac :: listaa) | CIntType0 _ => (NONE, CLongType0 x :: CBoolType0 ac :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CBoolType0 ac :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CBoolType0 ac :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CBoolType0 ac :: listaa) | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CBoolType0 ac :: listaa))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CBoolType0 ac :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CBoolType0 ac :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CBoolType0 ac :: listaa)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CBoolType0 ac :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CBoolType0 ac :: listaa) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CBoolType0 ac :: listaa)
                | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CBoolType0 ac :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CBoolType0 ac :: listaa) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CBoolType0 ac :: listaa)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CBoolType0 ac :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CComplexType0 ac :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CComplexType0 ac :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CComplexType0 ac :: listaa) | CCharType0 _ => (NONE, CLongType0 x :: CComplexType0 ac :: listaa)
                | CShortType0 _ => (NONE, CLongType0 x :: CComplexType0 ac :: listaa) | CIntType0 _ => (NONE, CLongType0 x :: CComplexType0 ac :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CComplexType0 ac :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CComplexType0 ac :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CComplexType0 ac :: listaa)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CComplexType0 ac :: listaa)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CComplexType0 ac :: listaa))
                | CBoolType0 _ => (NONE, CLongType0 x :: CComplexType0 ac :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CComplexType0 ac :: listaa) | CInt128Type0 _ => (NONE, CLongType0 x :: CComplexType0 ac :: listaa)
                | CSUType0 (_, _) => (NONE, CLongType0 x :: CComplexType0 ac :: listaa) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CComplexType0 ac :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CComplexType0 ac :: listaa)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CComplexType0 ac :: listaa) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CComplexType0 ac :: listaa)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CComplexType0 ac :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CInt128Type0 ac :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CInt128Type0 ac :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa) | CCharType0 _ => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa)
                | CShortType0 _ => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa) | CIntType0 _ => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa) | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CInt128Type0 ac :: listaa))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CInt128Type0 ac :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa)
                | CComplexType0 _ => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa) | CInt128Type0 _ => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa)
                | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa) | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CInt128Type0 ac :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CSUType0 (cStructureUnion, ac) :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa)
                | CCharType0 _ => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa)
                | CIntType0 _ => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa))
                | CBoolType0 _ => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CSUType0 (cStructureUnion, ac) :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CEnumType0 (cEnumeration, ac) :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa)
                | CCharType0 _ => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa)
                | CIntType0 _ => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa))
                | CBoolType0 _ => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CEnumType0 (cEnumeration, ac) :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CTypeDef0 (ident, ac) :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CTypeDef0 (ident, ac) :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa) | CCharType0 _ => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa)
                | CShortType0 _ => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa) | CIntType0 _ => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa)
                | CLongType0 _ => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa) | CFloatType0 _ => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa)
                | CDoubleType0 _ => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa) | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CTypeDef0 (ident, ac) :: listaa))
                | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CTypeDef0 (ident, ac) :: listaa)) | CBoolType0 _ => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa)
                | CComplexType0 _ => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa) | CInt128Type0 _ => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa)
                | CSUType0 (_, _) => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa) | CEnumType0 (_, _) => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa)
                | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa) | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa)
                | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa) | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CTypeDef0 (ident, ac) :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CTypeOfExpr0 (cExpression, ac) :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa)
                | CCharType0 _ => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa)
                | CIntType0 _ => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa))
                | CBoolType0 _ => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CTypeOfExpr0 (cExpression, ac) :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CTypeOfType0 (cDeclaration, ac) :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa)
                | CCharType0 _ => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa)
                | CIntType0 _ => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa))
                | CBoolType0 _ => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CTypeOfType0 (cDeclaration, ac) :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end
        | CAtomicType0 (cDeclaration, ac) :: listaa =>
          let
            val (siga, l) =
              (case hd (CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa) of CVoidType0 _ => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa)
                | CCharType0 _ => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa) | CShortType0 _ => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa)
                | CIntType0 _ => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa) | CLongType0 _ => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa)
                | CFloatType0 _ => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa) | CDoubleType0 _ => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa)
                | CSignedType0 _ => (SOME Signed, tl (CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa)) | CUnsigType0 _ => (SOME Unsigned, tl (CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa))
                | CBoolType0 _ => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa) | CComplexType0 _ => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa)
                | CInt128Type0 _ => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa) | CSUType0 (_, _) => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa)
                | CEnumType0 (_, _) => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa) | CTypeDef0 (_, _) => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa)
                | CTypeOfExpr0 (_, _) => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa) | CTypeOfType0 (_, _) => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa)
                | CAtomicType0 (_, _) => (NONE, CLongType0 x :: CAtomicType0 (cDeclaration, ac) :: listaa));
          in
            (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                               | [CDoubleType0 _] => Double))
                                 (groupBy (fn a => fn b =>
                                            (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                              | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                              | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                              | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                              | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                              | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                              | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                              | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                                   l)
                           of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                           | [Double] => Double | [Float] => Float))
              of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
              | (SOME sigb, ty) => sigb ty)
          end)
    | CFloatType0 aa :: lista =>
      let
        val (siga, l) =
          (case hd (CFloatType0 aa :: lista) of CVoidType0 _ => (NONE, CFloatType0 aa :: lista) | CCharType0 _ => (NONE, CFloatType0 aa :: lista) | CShortType0 _ => (NONE, CFloatType0 aa :: lista)
            | CIntType0 _ => (NONE, CFloatType0 aa :: lista) | CLongType0 _ => (NONE, CFloatType0 aa :: lista) | CFloatType0 _ => (NONE, CFloatType0 aa :: lista) | CDoubleType0 _ => (NONE, CFloatType0 aa :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CFloatType0 aa :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CFloatType0 aa :: lista)) | CBoolType0 _ => (NONE, CFloatType0 aa :: lista)
            | CComplexType0 _ => (NONE, CFloatType0 aa :: lista) | CInt128Type0 _ => (NONE, CFloatType0 aa :: lista) | CSUType0 (_, _) => (NONE, CFloatType0 aa :: lista) | CEnumType0 (_, _) => (NONE, CFloatType0 aa :: lista)
            | CTypeDef0 (_, _) => (NONE, CFloatType0 aa :: lista) | CTypeOfExpr0 (_, _) => (NONE, CFloatType0 aa :: lista) | CTypeOfType0 (_, _) => (NONE, CFloatType0 aa :: lista)
            | CAtomicType0 (_, _) => (NONE, CFloatType0 aa :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CDoubleType0 aa :: lista =>
      let
        val (siga, l) =
          (case hd (CDoubleType0 aa :: lista) of CVoidType0 _ => (NONE, CDoubleType0 aa :: lista) | CCharType0 _ => (NONE, CDoubleType0 aa :: lista) | CShortType0 _ => (NONE, CDoubleType0 aa :: lista)
            | CIntType0 _ => (NONE, CDoubleType0 aa :: lista) | CLongType0 _ => (NONE, CDoubleType0 aa :: lista) | CFloatType0 _ => (NONE, CDoubleType0 aa :: lista) | CDoubleType0 _ => (NONE, CDoubleType0 aa :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CDoubleType0 aa :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CDoubleType0 aa :: lista)) | CBoolType0 _ => (NONE, CDoubleType0 aa :: lista)
            | CComplexType0 _ => (NONE, CDoubleType0 aa :: lista) | CInt128Type0 _ => (NONE, CDoubleType0 aa :: lista) | CSUType0 (_, _) => (NONE, CDoubleType0 aa :: lista) | CEnumType0 (_, _) => (NONE, CDoubleType0 aa :: lista)
            | CTypeDef0 (_, _) => (NONE, CDoubleType0 aa :: lista) | CTypeOfExpr0 (_, _) => (NONE, CDoubleType0 aa :: lista) | CTypeOfType0 (_, _) => (NONE, CDoubleType0 aa :: lista)
            | CAtomicType0 (_, _) => (NONE, CDoubleType0 aa :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CSignedType0 aa :: lista =>
      let
        val (siga, l) =
          (case hd (CSignedType0 aa :: lista) of CVoidType0 _ => (NONE, CSignedType0 aa :: lista) | CCharType0 _ => (NONE, CSignedType0 aa :: lista) | CShortType0 _ => (NONE, CSignedType0 aa :: lista)
            | CIntType0 _ => (NONE, CSignedType0 aa :: lista) | CLongType0 _ => (NONE, CSignedType0 aa :: lista) | CFloatType0 _ => (NONE, CSignedType0 aa :: lista) | CDoubleType0 _ => (NONE, CSignedType0 aa :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CSignedType0 aa :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CSignedType0 aa :: lista)) | CBoolType0 _ => (NONE, CSignedType0 aa :: lista)
            | CComplexType0 _ => (NONE, CSignedType0 aa :: lista) | CInt128Type0 _ => (NONE, CSignedType0 aa :: lista) | CSUType0 (_, _) => (NONE, CSignedType0 aa :: lista) | CEnumType0 (_, _) => (NONE, CSignedType0 aa :: lista)
            | CTypeDef0 (_, _) => (NONE, CSignedType0 aa :: lista) | CTypeOfExpr0 (_, _) => (NONE, CSignedType0 aa :: lista) | CTypeOfType0 (_, _) => (NONE, CSignedType0 aa :: lista)
            | CAtomicType0 (_, _) => (NONE, CSignedType0 aa :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CUnsigType0 aa :: lista =>
      let
        val (siga, l) =
          (case hd (CUnsigType0 aa :: lista) of CVoidType0 _ => (NONE, CUnsigType0 aa :: lista) | CCharType0 _ => (NONE, CUnsigType0 aa :: lista) | CShortType0 _ => (NONE, CUnsigType0 aa :: lista)
            | CIntType0 _ => (NONE, CUnsigType0 aa :: lista) | CLongType0 _ => (NONE, CUnsigType0 aa :: lista) | CFloatType0 _ => (NONE, CUnsigType0 aa :: lista) | CDoubleType0 _ => (NONE, CUnsigType0 aa :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CUnsigType0 aa :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CUnsigType0 aa :: lista)) | CBoolType0 _ => (NONE, CUnsigType0 aa :: lista)
            | CComplexType0 _ => (NONE, CUnsigType0 aa :: lista) | CInt128Type0 _ => (NONE, CUnsigType0 aa :: lista) | CSUType0 (_, _) => (NONE, CUnsigType0 aa :: lista) | CEnumType0 (_, _) => (NONE, CUnsigType0 aa :: lista)
            | CTypeDef0 (_, _) => (NONE, CUnsigType0 aa :: lista) | CTypeOfExpr0 (_, _) => (NONE, CUnsigType0 aa :: lista) | CTypeOfType0 (_, _) => (NONE, CUnsigType0 aa :: lista)
            | CAtomicType0 (_, _) => (NONE, CUnsigType0 aa :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | [CBoolType0 _] => Bool
    | CBoolType0 x :: ab :: lista =>
      let
        val (siga, l) =
          (case hd (CBoolType0 x :: ab :: lista) of CVoidType0 _ => (NONE, CBoolType0 x :: ab :: lista) | CCharType0 _ => (NONE, CBoolType0 x :: ab :: lista) | CShortType0 _ => (NONE, CBoolType0 x :: ab :: lista)
            | CIntType0 _ => (NONE, CBoolType0 x :: ab :: lista) | CLongType0 _ => (NONE, CBoolType0 x :: ab :: lista) | CFloatType0 _ => (NONE, CBoolType0 x :: ab :: lista) | CDoubleType0 _ => (NONE, CBoolType0 x :: ab :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CBoolType0 x :: ab :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CBoolType0 x :: ab :: lista)) | CBoolType0 _ => (NONE, CBoolType0 x :: ab :: lista)
            | CComplexType0 _ => (NONE, CBoolType0 x :: ab :: lista) | CInt128Type0 _ => (NONE, CBoolType0 x :: ab :: lista) | CSUType0 (_, _) => (NONE, CBoolType0 x :: ab :: lista)
            | CEnumType0 (_, _) => (NONE, CBoolType0 x :: ab :: lista) | CTypeDef0 (_, _) => (NONE, CBoolType0 x :: ab :: lista) | CTypeOfExpr0 (_, _) => (NONE, CBoolType0 x :: ab :: lista)
            | CTypeOfType0 (_, _) => (NONE, CBoolType0 x :: ab :: lista) | CAtomicType0 (_, _) => (NONE, CBoolType0 x :: ab :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CComplexType0 aa :: lista =>
      let
        val (siga, l) =
          (case hd (CComplexType0 aa :: lista) of CVoidType0 _ => (NONE, CComplexType0 aa :: lista) | CCharType0 _ => (NONE, CComplexType0 aa :: lista) | CShortType0 _ => (NONE, CComplexType0 aa :: lista)
            | CIntType0 _ => (NONE, CComplexType0 aa :: lista) | CLongType0 _ => (NONE, CComplexType0 aa :: lista) | CFloatType0 _ => (NONE, CComplexType0 aa :: lista) | CDoubleType0 _ => (NONE, CComplexType0 aa :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CComplexType0 aa :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CComplexType0 aa :: lista)) | CBoolType0 _ => (NONE, CComplexType0 aa :: lista)
            | CComplexType0 _ => (NONE, CComplexType0 aa :: lista) | CInt128Type0 _ => (NONE, CComplexType0 aa :: lista) | CSUType0 (_, _) => (NONE, CComplexType0 aa :: lista) | CEnumType0 (_, _) => (NONE, CComplexType0 aa :: lista)
            | CTypeDef0 (_, _) => (NONE, CComplexType0 aa :: lista) | CTypeOfExpr0 (_, _) => (NONE, CComplexType0 aa :: lista) | CTypeOfType0 (_, _) => (NONE, CComplexType0 aa :: lista)
            | CAtomicType0 (_, _) => (NONE, CComplexType0 aa :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CInt128Type0 aa :: lista =>
      let
        val (siga, l) =
          (case hd (CInt128Type0 aa :: lista) of CVoidType0 _ => (NONE, CInt128Type0 aa :: lista) | CCharType0 _ => (NONE, CInt128Type0 aa :: lista) | CShortType0 _ => (NONE, CInt128Type0 aa :: lista)
            | CIntType0 _ => (NONE, CInt128Type0 aa :: lista) | CLongType0 _ => (NONE, CInt128Type0 aa :: lista) | CFloatType0 _ => (NONE, CInt128Type0 aa :: lista) | CDoubleType0 _ => (NONE, CInt128Type0 aa :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CInt128Type0 aa :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CInt128Type0 aa :: lista)) | CBoolType0 _ => (NONE, CInt128Type0 aa :: lista)
            | CComplexType0 _ => (NONE, CInt128Type0 aa :: lista) | CInt128Type0 _ => (NONE, CInt128Type0 aa :: lista) | CSUType0 (_, _) => (NONE, CInt128Type0 aa :: lista) | CEnumType0 (_, _) => (NONE, CInt128Type0 aa :: lista)
            | CTypeDef0 (_, _) => (NONE, CInt128Type0 aa :: lista) | CTypeOfExpr0 (_, _) => (NONE, CInt128Type0 aa :: lista) | CTypeOfType0 (_, _) => (NONE, CInt128Type0 aa :: lista)
            | CAtomicType0 (_, _) => (NONE, CInt128Type0 aa :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | [CSUType0 (CStruct0 (tag, ide, _, _, _), _)] => decl_spec_ty_tag tag let
                                                                             val Some a = ide;
                                                                           in
                                                                             ident_struct_type a
                                                                           end
    | CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista =>
      let
        val (siga, l) =
          (case hd (CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista) of CVoidType0 _ => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista)
            | CCharType0 _ => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista) | CShortType0 _ => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista)
            | CIntType0 _ => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista) | CLongType0 _ => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista)
            | CFloatType0 _ => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista) | CDoubleType0 _ => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista))
            | CBoolType0 _ => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista) | CComplexType0 _ => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista)
            | CInt128Type0 _ => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista) | CSUType0 (_, _) => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista)
            | CEnumType0 (_, _) => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista) | CTypeDef0 (_, _) => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista)
            | CTypeOfExpr0 (_, _) => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista) | CTypeOfType0 (_, _) => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista)
            | CAtomicType0 (_, _) => (NONE, CSUType0 (CStruct0 (tag, ide, x, xa, xb), xc) :: ad :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | [CEnumType0 (CEnum0 (ide, _, _, _), _)] => EnumTy (ident_option ide)
    | CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista =>
      let
        val (siga, l) =
          (case hd (CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista) of CVoidType0 _ => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista)
            | CCharType0 _ => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista) | CShortType0 _ => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista)
            | CIntType0 _ => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista) | CLongType0 _ => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista)
            | CFloatType0 _ => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista) | CDoubleType0 _ => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista)
            | CSignedType0 _ => (SOME Signed, tl (CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista))
            | CBoolType0 _ => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista) | CComplexType0 _ => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista)
            | CInt128Type0 _ => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista) | CSUType0 (_, _) => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista)
            | CEnumType0 (_, _) => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista) | CTypeDef0 (_, _) => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista)
            | CTypeOfExpr0 (_, _) => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista) | CTypeOfType0 (_, _) => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista)
            | CAtomicType0 (_, _) => (NONE, CEnumType0 (CEnum0 (ide, x, xa, xb), xc) :: ad :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | [CTypeDef0 (i, _)] => identb i
    | CTypeDef0 (i, x) :: ab :: lista =>
      let
        val (siga, l) =
          (case hd (CTypeDef0 (i, x) :: ab :: lista) of CVoidType0 _ => (NONE, CTypeDef0 (i, x) :: ab :: lista) | CCharType0 _ => (NONE, CTypeDef0 (i, x) :: ab :: lista) | CShortType0 _ => (NONE, CTypeDef0 (i, x) :: ab :: lista)
            | CIntType0 _ => (NONE, CTypeDef0 (i, x) :: ab :: lista) | CLongType0 _ => (NONE, CTypeDef0 (i, x) :: ab :: lista) | CFloatType0 _ => (NONE, CTypeDef0 (i, x) :: ab :: lista)
            | CDoubleType0 _ => (NONE, CTypeDef0 (i, x) :: ab :: lista) | CSignedType0 _ => (SOME Signed, tl (CTypeDef0 (i, x) :: ab :: lista)) | CUnsigType0 _ => (SOME Unsigned, tl (CTypeDef0 (i, x) :: ab :: lista))
            | CBoolType0 _ => (NONE, CTypeDef0 (i, x) :: ab :: lista) | CComplexType0 _ => (NONE, CTypeDef0 (i, x) :: ab :: lista) | CInt128Type0 _ => (NONE, CTypeDef0 (i, x) :: ab :: lista)
            | CSUType0 (_, _) => (NONE, CTypeDef0 (i, x) :: ab :: lista) | CEnumType0 (_, _) => (NONE, CTypeDef0 (i, x) :: ab :: lista) | CTypeDef0 (_, _) => (NONE, CTypeDef0 (i, x) :: ab :: lista)
            | CTypeOfExpr0 (_, _) => (NONE, CTypeDef0 (i, x) :: ab :: lista) | CTypeOfType0 (_, _) => (NONE, CTypeDef0 (i, x) :: ab :: lista) | CAtomicType0 (_, _) => (NONE, CTypeDef0 (i, x) :: ab :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CTypeOfExpr0 (cExpression, aa) :: lista =>
      let
        val (siga, l) =
          (case hd (CTypeOfExpr0 (cExpression, aa) :: lista) of CVoidType0 _ => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista) | CCharType0 _ => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista)
            | CShortType0 _ => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista) | CIntType0 _ => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista) | CLongType0 _ => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista)
            | CFloatType0 _ => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista) | CDoubleType0 _ => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista) | CSignedType0 _ => (SOME Signed, tl (CTypeOfExpr0 (cExpression, aa) :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CTypeOfExpr0 (cExpression, aa) :: lista)) | CBoolType0 _ => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista) | CComplexType0 _ => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista)
            | CInt128Type0 _ => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista) | CSUType0 (_, _) => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista) | CEnumType0 (_, _) => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista)
            | CTypeDef0 (_, _) => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista) | CTypeOfExpr0 (_, _) => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista) | CTypeOfType0 (_, _) => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista)
            | CAtomicType0 (_, _) => (NONE, CTypeOfExpr0 (cExpression, aa) :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CTypeOfType0 (cDeclaration, aa) :: lista =>
      let
        val (siga, l) =
          (case hd (CTypeOfType0 (cDeclaration, aa) :: lista) of CVoidType0 _ => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista) | CCharType0 _ => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista)
            | CShortType0 _ => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista) | CIntType0 _ => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista) | CLongType0 _ => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista)
            | CFloatType0 _ => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista) | CDoubleType0 _ => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista) | CSignedType0 _ => (SOME Signed, tl (CTypeOfType0 (cDeclaration, aa) :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CTypeOfType0 (cDeclaration, aa) :: lista)) | CBoolType0 _ => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista) | CComplexType0 _ => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista)
            | CInt128Type0 _ => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista) | CSUType0 (_, _) => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista) | CEnumType0 (_, _) => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista)
            | CTypeDef0 (_, _) => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista) | CTypeOfExpr0 (_, _) => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista) | CTypeOfType0 (_, _) => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista)
            | CAtomicType0 (_, _) => (NONE, CTypeOfType0 (cDeclaration, aa) :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end
    | CAtomicType0 (cDeclaration, aa) :: lista =>
      let
        val (siga, l) =
          (case hd (CAtomicType0 (cDeclaration, aa) :: lista) of CVoidType0 _ => (NONE, CAtomicType0 (cDeclaration, aa) :: lista) | CCharType0 _ => (NONE, CAtomicType0 (cDeclaration, aa) :: lista)
            | CShortType0 _ => (NONE, CAtomicType0 (cDeclaration, aa) :: lista) | CIntType0 _ => (NONE, CAtomicType0 (cDeclaration, aa) :: lista) | CLongType0 _ => (NONE, CAtomicType0 (cDeclaration, aa) :: lista)
            | CFloatType0 _ => (NONE, CAtomicType0 (cDeclaration, aa) :: lista) | CDoubleType0 _ => (NONE, CAtomicType0 (cDeclaration, aa) :: lista) | CSignedType0 _ => (SOME Signed, tl (CAtomicType0 (cDeclaration, aa) :: lista))
            | CUnsigType0 _ => (SOME Unsigned, tl (CAtomicType0 (cDeclaration, aa) :: lista)) | CBoolType0 _ => (NONE, CAtomicType0 (cDeclaration, aa) :: lista) | CComplexType0 _ => (NONE, CAtomicType0 (cDeclaration, aa) :: lista)
            | CInt128Type0 _ => (NONE, CAtomicType0 (cDeclaration, aa) :: lista) | CSUType0 (_, _) => (NONE, CAtomicType0 (cDeclaration, aa) :: lista) | CEnumType0 (_, _) => (NONE, CAtomicType0 (cDeclaration, aa) :: lista)
            | CTypeDef0 (_, _) => (NONE, CAtomicType0 (cDeclaration, aa) :: lista) | CTypeOfExpr0 (_, _) => (NONE, CAtomicType0 (cDeclaration, aa) :: lista) | CTypeOfType0 (_, _) => (NONE, CAtomicType0 (cDeclaration, aa) :: lista)
            | CAtomicType0 (_, _) => (NONE, CAtomicType0 (cDeclaration, aa) :: lista));
      in
        (case (siga, (case mapa (fn a => (case a of [CCharType0 _] => Char | [CShortType0 _] => Short | [CIntType0 _] => Int | [CLongType0 _] => Long | [CLongType0 _, CLongType0 _] => LongLong | [CFloatType0 _] => Float
                                           | [CDoubleType0 _] => Double))
                             (groupBy (fn a => fn b =>
                                        (case (a, b) of (CVoidType0 _, _) => false | (CCharType0 _, _) => false | (CShortType0 _, _) => false | (CIntType0 _, _) => false | (CLongType0 _, CVoidType0 _) => false
                                          | (CLongType0 _, CCharType0 _) => false | (CLongType0 _, CShortType0 _) => false | (CLongType0 _, CIntType0 _) => false | (CLongType0 _, CLongType0 _) => true
                                          | (CLongType0 _, CFloatType0 _) => false | (CLongType0 _, CDoubleType0 _) => false | (CLongType0 _, CSignedType0 _) => false | (CLongType0 _, CUnsigType0 _) => false
                                          | (CLongType0 _, CBoolType0 _) => false | (CLongType0 _, CComplexType0 _) => false | (CLongType0 _, CInt128Type0 _) => false | (CLongType0 _, CSUType0 (_, _)) => false
                                          | (CLongType0 _, CEnumType0 (_, _)) => false | (CLongType0 _, CTypeDef0 (_, _)) => false | (CLongType0 _, CTypeOfExpr0 (_, _)) => false | (CLongType0 _, CTypeOfType0 (_, _)) => false
                                          | (CLongType0 _, CAtomicType0 (_, _)) => false | (CFloatType0 _, _) => false | (CDoubleType0 _, _) => false | (CSignedType0 _, _) => false | (CUnsigType0 _, _) => false
                                          | (CBoolType0 _, _) => false | (CComplexType0 _, _) => false | (CInt128Type0 _, _) => false | (CSUType0 (_, _), _) => false | (CEnumType0 (_, _), _) => false | (CTypeDef0 (_, _), _) => false
                                          | (CTypeOfExpr0 (_, _), _) => false | (CTypeOfType0 (_, _), _) => false | (CAtomicType0 (_, _), _) => false))
                               l)
                       of [] => Int | [Char] => Char | [Short] => Short | [Short, Int] => Short | [Int] => Int | [Long] => Long | [Long, Int] => Long | [Long, Double] => Double | [LongLong] => LongLong | [LongLong, Int] => LongLong
                       | [Double] => Double | [Float] => Float))
          of (NONE, Char) => PlainChar | (NONE, Short) => Signed Short | (NONE, Int) => Signed Int | (NONE, Long) => Signed Long | (NONE, LongLong) => Signed LongLong | (NONE, Double) => Signed Double | (NONE, Float) => Signed Float
          | (SOME sigb, ty) => sigb ty)
      end);

fun ident_struct_const x = (fn Ident0 (s, _, _) => pref_ident (flatten [s, SS_base (ST "_C")])) x;

fun not_yet_supported x = (warning o String.implode o to_list) x;

fun map_prod f g (a, b) = (f a, g b);

val bogus : sourcePos = Ta ((~1 : IntInf.int), SS_base (ST "<bogus>"), (~1 : IntInf.int));

fun comp2 f g = (fn x => fn y => f (g x y));

fun wrap x = comp2 (fn a => Tb (x, a)) (fn a => fn b => T (a, b));

fun bogwrap x = wrap x bogus bogus;

fun ebogwrap x = (E o bogwrap) x;

fun map2 f (x :: xs) (y :: ys) = f x y :: map2 f xs ys
  | map2 f xs [] = []
  | map2 f [] ys = [];

fun show_intFlag x = (fn a => (case a of FlagUnsigned0 => SS_base (ST "u") | FlagLong0 => SS_base (ST "l") | FlagLongLong0 => SS_base (ST "ll") | FlagImag0 => SS_base (ST "i"))) x;

fun sgn_integer k = (if k = (0 : IntInf.int) then (0 : IntInf.int) else (if k < (0 : IntInf.int) then (~1 : IntInf.int) else (1 : IntInf.int)));

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if k = (0 : IntInf.int) then ((0 : IntInf.int), (0 : IntInf.int))
    else (if l = (0 : IntInf.int) then ((0 : IntInf.int), k)
           else (apsnd o (fn a => fn b => a * b) o sgn_integer) l
                  (if sgn_integer k = sgn_integer l then Integer.div_mod (abs k) (abs l) else let
                                                                                                val (r, s) = Integer.div_mod (abs k) (abs l);
                                                                                              in
                                                                                                (if s = (0 : IntInf.int) then (~ r, (0 : IntInf.int)) else (~ r - (1 : IntInf.int), abs l - s))
                                                                                              end)));

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_int k l = Int_of_integer (modulo_integer (integer_of_int k) (integer_of_int l));

fun power A_ a n = (if equal_nat n zero_nat then one (one_power A_) else times (times_power A_) a (power A_ a (minus_nat n one_nat)));

fun word_of_int A_ k = Word (modulo_int k (power power_int (Int_of_integer (2 : IntInf.int)) (len_of A_ Type)));

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun concat xss = foldr (fn a => fn b => a @ b) xss [];

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_int k l = Int_of_integer (divide_integer (integer_of_int k) (integer_of_int l));

fun bin_rest w = divide_int w (Int_of_integer (2 : IntInf.int));

fun equal_int k l = integer_of_int k = integer_of_int l;

fun bin_last w = equal_int (modulo_int w (Int_of_integer (2 : IntInf.int))) one_inta;

fun bin_to_bl_aux n w bl = (if equal_nat n zero_nat then bl else bin_to_bl_aux (minus_nat n one_nat) (bin_rest w) (bin_last w :: bl));

fun bin_to_bl n w = bin_to_bl_aux n w [];

fun uint A_ (Word x) = x;

fun to_bl A_ w = bin_to_bl (len_of A_ Type) (uint A_ w);

fun constant x =
  (bogwrap o (fn a => (case a of CIntConst0 (CInteger0 (i, repr, Flags0 flags), _) =>
                                NUMCONST (i, flatten (concat (rev (map2 (fn flag => fn aa => (case aa of true => [show_intFlag flag] | false => [])) [FlagImag0, FlagLongLong0, FlagLong0, FlagUnsigned0]
                                                                    (to_bl (len0_bit0 (len0_bit0 len0_num1)) (word_of_int (len0_bit0 (len0_bit0 len0_num1)) (Int_of_integer flags)))))),
                                           (case repr of DecRepr0 => DEC | HexRepr0 => HEX | OctalRepr0 => OCT))
                        | CCharConst0 (CChar0 (c, _), _) => NUMCONST ((IntInf.fromInt o Char.ord) c, SS_base (ST ""), DEC)
                        | CFloatConst0 (_, _) => let
                                                   val _ = not_yet_supported (flatten [SS_base (ST "Float not yet supported (String returned)")]);
                                                 in
                                                   STRING_LIT (SS_base (ST ""))
                                                 end
                        | CStrConst0 (CString0 (str, _), _) => STRING_LIT str)))
    x;

fun binaryOp x =
  (fn a => (case a of CMulOp0 => Times | CDivOp0 => Divides | CRmdOp0 => Modulus | CAddOp0 => Plus | CSubOp0 => Minus | CShlOp0 => LShift | CShrOp0 => RShift | CLeOp0 => Lt | CGrOp0 => Gt | CLeqOp0 => Leq | CGeqOp0 => Geq
             | CEqOp0 => Equals | CNeqOp0 => NotEquals | CAndOp0 => BitwiseAnd | CXorOp0 => BitwiseXOr | COrOp0 => BitwiseOr | CLndOp0 => LogAnd | CLorOp0 => LogOr))
    x;

fun unaryOp x = (fn a => (case a of CAdrOp0 => Addr | CMinOp0 => Negate | CCompOp0 => BitNegate | CNegOp0 => Not)) x;

fun deriv_decl_spec dDs = deriv_decl_spec0 dDs o decl_spec_ty
and expression0 e =
  (case e of CCond0 (e1, Some e2, e3, _) => CondExp (expression e1, expression e2, expression e3) | CBinary0 (bino, e1, e2, _) => BinOp (binaryOp bino, expression e1, expression e2)
    | CCast0 (CDecl0 (l, l_arg, _), ea, _) =>
      TypeCast (bogwrap (deriv_decl_spec (case l_arg of [] => [] | ((None, _), _) :: _ => [] | [((Some (CDeclr0 (_, dDs, _, _, _)), _), _)] => dDs | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => []) l), expression ea)
    | CUnary0 (CPreIncOp0, ea, _) => UnOp (unaryOp CPreIncOp0, expression ea) | CUnary0 (CPreDecOp0, ea, _) => UnOp (unaryOp CPreDecOp0, expression ea) | CUnary0 (CPostIncOp0, ea, _) => UnOp (unaryOp CPostIncOp0, expression ea)
    | CUnary0 (CPostDecOp0, ea, _) => UnOp (unaryOp CPostDecOp0, expression ea) | CUnary0 (CAdrOp0, ea, _) => UnOp (unaryOp CAdrOp0, expression ea) | CUnary0 (CIndOp0, ea, _) => Deref (expression ea)
    | CUnary0 (CPlusOp0, ea, _) => UnOp (unaryOp CPlusOp0, expression ea) | CUnary0 (CMinOp0, ea, _) => UnOp (unaryOp CMinOp0, expression ea) | CUnary0 (CCompOp0, ea, _) => UnOp (unaryOp CCompOp0, expression ea)
    | CUnary0 (CNegOp0, ea, _) => UnOp (unaryOp CNegOp0, expression ea) | CSizeofExpr0 (ea, _) => Sizeof (expression ea) | CSizeofType0 (CDecl0 (l, _, _), _) => SizeofTy (bogwrap (decl_spec_ty l))
    | CIndex0 (e1, e2, _) => ArrayDeref (expression e1, expression e2)
    | CCall0 (ea, l, _) =>
      (case (case ea of CComma0 (_, _) => NONE | CAssign0 (_, _, _, _) => NONE | CCond0 (_, _, _, _) => NONE | CBinary0 (_, _, _, _) => NONE | CCast0 (_, _, _) => NONE | CUnary0 (_, _, _) => NONE | CSizeofExpr0 (_, _) => NONE
              | CSizeofType0 (_, _) => NONE | CAlignofExpr0 (_, _) => NONE | CAlignofType0 (_, _) => NONE | CComplexReal0 (_, _) => NONE | CComplexImag0 (_, _) => NONE | CIndex0 (_, _, _) => NONE | CCall0 (_, _, _) => NONE
              | CMember0 (_, _, _, _) => NONE | CVar0 (Ident0 (s, _, _), _) => (if equal_abr_stringa s (SS_base (ST "__builtin_expect")) then SOME let
                               val [x, _] = l;
                             in
                               x
                             end
                                                                                 else NONE)
              | CConst0 _ => NONE | CCompoundLit0 (_, _, _) => NONE | CGenericSelection0 (_, _, _) => NONE | CStatExpr0 (_, _) => NONE | CLabAddrExpr0 (_, _) => NONE | CBuiltinExpr0 _ => NONE)
        of NONE => EFnCall (expression ea, mapa expression l) | SOME a => expression0 a)
    | CMember0 (ea, i, deref, _) => StructDot ((if deref then ebogwrap o Deref else id) (expression ea), ident_struct_const i) | CVar0 (i, _) => Var (ident i, Unsynchronized_ref NONE) | CConst0 c => Constant (constant c)
    | CCompoundLit0 (CDecl0 (l1, _, _), l2, _) => CompLiteral (decl_spec_ty l1, initializerList l2))
and expression x = (ebogwrap o expression0) x
and partDesignator e =
  (case e of CArrDesig0 (ea, _) => DesignE (expression ea) | CMemberDesig0 (i, _) => DesignFld (ident_struct_const i)
    | CRangeDesig0 (_, _, _) => let
                                  val _ = not_yet_supported (SS_base (ST "CRangeDesig not yet supported (DesignFld returned)"));
                                in
                                  DesignFld (SS_base (ST ""))
                                end)
and initializerList l = mapa (map_prod (mapa partDesignator) initializer) l
and initializer0 f e = (case e of CInitExpr0 (ea, _) => InitE (expression (f ea)) | CInitList0 (l, _) => InitList (initializerList l))
and initializer e = initializer0 id e
and deriv_decl_spec0 dDs =
  foldr (fn a => (case a of CPtrDeclr0 (_, _) => Ptr | CArrDeclr0 ([], sz, _) => (fn t => Array (t, (case sz of CNoArrSize0 false => NONE | CArrSize0 (false, expr) => SOME (expression expr))))
                   | CFunDeclr0 (Right (arg, _), _, _) => (fn t => Function (t, function_definition_params0 (fn CDecl0 (l_decl_spec, _, _) => decl_spec_ty l_decl_spec) arg))))
    dDs;

fun function_definition_params f_name = function_definition_params0 (fn CDecl0 (l_decl_spec, [((Some (CDeclr0 (Some i, dDs, _, _, _)), _), _)], _) => (deriv_decl_spec dDs l_decl_spec, f_name (ident i)));

fun p_first_of_NodeInfo x = (fn a => (case a of OnlyPos0 (pos, _) => (pos, (1 : IntInf.int)) | NodeInfo0 (pos, _, _) => (pos, (1 : IntInf.int)))) x;

fun p_last_of_NodeInfo x = (fn a => (case a of OnlyPos0 (_, len) => len | NodeInfo0 (_, len, _) => len)) x;

fun pos_of_CFunDef x = (fn CFunDef0 (_, _, _, _, pos) => pos) x;

fun pos_of_CStat x =
  (fn a => (case a of CLabel0 (_, _, _, pos) => pos | CCase0 (_, _, pos) => pos | CDefault0 (_, pos) => pos | CExpr0 (_, pos) => pos | CCompound0 (_, _, pos) => pos | CIf0 (_, _, _, pos) => pos | CSwitch0 (_, _, pos) => pos
             | CWhile0 (_, _, _, pos) => pos | CFor0 (_, _, _, _, pos) => pos | CGoto0 (_, pos) => pos | CCont0 pos => pos | CBreak0 pos => pos | CReturn0 (_, pos) => pos | CAsm0 (_, pos) => pos))
    x;

fun pos_of_CDecl x = (fn CDecl0 (_, _, pos) => pos) x;

fun pos_of_CBlockItem x = (fn a => (case a of CBlockStmt0 aa => pos_of_CStat aa | CBlockDecl0 aa => pos_of_CDecl aa | CNestedFunDef0 aa => pos_of_CFunDef aa)) x;

fun map_comment_type f (Invariant x1) = Invariant x1
  | map_comment_type f (Fnspeca x2) = Fnspeca x2
  | map_comment_type f (Relspeca x3) = Relspeca x3
  | map_comment_type f (Modifies x4) = Modifies x4
  | map_comment_type f Dont_translate = Dont_translate
  | map_comment_type f (Auxupda x6) = Auxupda x6
  | map_comment_type f (Ghostupda x7) = Ghostupda x7
  | map_comment_type f (Speca x8) = Speca x8
  | map_comment_type f (End_spec x9) = End_spec x9
  | map_comment_type f (Calls x10) = Calls x10
  | map_comment_type f (Owned_by x11) = Owned_by x11
  | map_comment_type f (OTHER x12) = OTHER (f x12);

fun catch_error m f = (case m of Inl a => f a | Inr a => Inr a);

fun or f1 f2 ts = catch_error (f1 ts) (fn _ => f2 ts);

fun returna x = (fn ts => Inr (x, ts));

fun binda m f = (case m of Inl a => Inl a | Inr a => f a);

fun bindb m f ts = binda (m ts) (fn (a, b) => f a b);

fun many_c_a_t_c_h_a_l_l_aux l f = or (bindb f (fn v => many_c_a_t_c_h_a_l_l_aux (v :: l) f)) (returna (rev l));

fun many_c_a_t_c_h_a_l_l x = many_c_a_t_c_h_a_l_l_aux [] x;

fun map_sum f1 f2 (Inl a) = Inl (f1 a)
  | map_sum f1 f2 (Inr a) = Inr (f2 a);

fun bind2 m f = map_sum id (map_prod f id) m;

fun bind3 scan f xs = bind2 (scan xs) f;

fun scan_upto_b_i_n_d enda ts =
  or (bind3 enda (fn a => ([], a)))
    (fn a => (case a of [] => Inl [#"d", #"i", #"d", #" ", #"n", #"o", #"t", #" ", #"f", #"i", #"n", #"d", #" ", #"t", #"h", #"e", #" ", #"e", #"n", #"d", #"-", #"m", #"a", #"r", #"k", #"e", #"r"]
               | t :: aa => bindb (scan_upto_b_i_n_d enda) (fn (res1, res2) => returna (t :: res1, res2)) aa))
    ts;

fun errorb e = (fn _ => Inl e);

fun oneof_b_i_n_d x =
  (fn a => (case a of [] => errorb [#"d", #"i", #"d", #" ", #"n", #"o", #"t", #" ", #"f", #"i", #"n", #"d", #" ", #"a", #" ", #"m", #"a", #"t", #"c", #"h", #"i", #"n", #"g", #" ", #"e", #"l", #"e", #"m", #"e", #"n", #"t"]
             | xa :: xs => fold (fn x2 => fn x1 => or x1 x2) xs xa))
    x;

fun bind_k scan f = bind3 scan (fn _ => f);

fun shows_prec_list A_ p xs = shows_list A_ xs;

fun shows_quote s = shows_prec_char zero_nat #"'" o s o shows_prec_char zero_nat #"'";

fun take n [] = []
  | take n (x :: xs) = (if equal_nat n zero_nat then [] else x :: take (minus_nat n one_nat) xs);

fun err_expecting A_ msg ts =
  Inl ([#"e", #"x", #"p", #"e", #"c", #"t", #"i", #"n", #"g", #" "] @
        msg @ [#",", #" ", #"b", #"u", #"t", #" ", #"f", #"o", #"u", #"n", #"d", #":", #" "] @ shows_quote (shows_prec_list A_ zero_nat (take (nat_of_integer (30 : IntInf.int)) ts)) []);

fun exactly_aux (A1_, A2_) s i (x :: xs) (y :: ys) = (if eq A1_ x y then exactly_aux (A1_, A2_) s i xs ys else err_expecting A2_ ([#"\""] @ s @ [#"\""]) i)
  | exactly_aux (A1_, A2_) s i [] xs = Inr (s, xs)
  | exactly_aux (A1_, A2_) s i (x :: xs) [] = err_expecting A2_ ([#"\""] @ s @ [#"\""]) i;

fun exactly s x = exactly_aux (equal_char, show_char) s x s x;

fun many p (t :: ts) = (if p t then binda (many p ts) (fn (rs, tsa) => Inr (t :: rs, tsa)) else Inr ([], t :: ts))
  | many p [] = Inr ([], []);

fun many1 p =
  (fn a => (case a of [] => Inl [#"d", #"i", #"d", #" ", #"n", #"o", #"t", #" ", #"f", #"i", #"n", #"d", #" ", #"a", #"n", #" ", #"e", #"l", #"e", #"m", #"e", #"n", #"t"]
             | t :: ts => (if p t then binda (many p ts) (fn (rs, tsa) => Inr (t :: rs, tsa))
                            else Inl [#"d", #"i", #"d", #" ", #"n", #"o", #"t", #" ", #"f", #"i", #"n", #"d", #" ", #"a", #" ", #"f", #"i", #"r", #"s", #"t", #" ", #"m", #"a", #"t", #"c", #"h", #"i", #"n", #"g", #" ", #"e", #"l", #"e",
                                       #"m", #"e", #"n", #"t"])));

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun manyof1 cs = many1 (member equal_char cs);

fun stars1 x = manyof1 [#"*"] x;

fun end_comment x = bindb stars1 (fn _ => exactly [#"/"]) x;

fun parse_id_m_a_y_b_e l_token =
  scan_upto_b_i_n_d
    (oneof_b_i_n_d
      (concat [bind_k end_comment (SOME [#"e", #"n", #"d", #" ", #"o", #"f", #" ", #"c", #"o", #"m", #"m", #"e", #"n", #"t"]) ::
                 mapa (fn s => bind_k (exactly s) (SOME [#"e", #"n", #"c", #"o", #"u", #"n", #"t", #"e", #"r", #"i", #"n", #"g", #" ", #"n", #"e", #"x", #"t", #" ", #"t", #"o", #"k", #"e", #"n"])) l_token,
                [bind_k (manyof1 [#" ", #"\n", #"\t", #"\r"]) NONE]]));

fun parse_id_o_n_e l_token = bindb (parse_id_m_a_y_b_e l_token) (fn a => (case a of ([], NONE) => returna [] | ([], SOME aa) => errorb aa | (aa :: lista, _) => returna (aa :: lista)));

fun many_m_a_x_aux l f = bindb f (fn v => let
                                            val la = v :: l;
                                          in
                                            or (many_m_a_x_aux la f) (returna (rev la))
                                          end);

fun many_m_a_x x = many_m_a_x_aux [] x;

fun parse_id_list l_token = many_c_a_t_c_h_a_l_l (bindb (bindb (many (member equal_char [#" ", #"\n", #"\t", #"\r"])) (fn _ => returna ())) (fn _ => or (bind_k (exactly [#"[", #"*", #"]"]) NONE) (bind3 (parse_id_o_n_e l_token) SOME)));

fun in_safe_monad f s = let
                          val Inr sa = f s;
                        in
                          sa
                        end;

fun parse_str_aux l = bindb (scan_upto_b_i_n_d (or (bind_k (exactly [#"\\", #"\""]) (fn s => parse_str_aux ([#"\""] :: s :: l))) (bind_k (exactly [#"\""]) (fn s => returna (concat (rev (s :: l))))))) (fn (s, f) => f s);

fun parse_str x = bindb (exactly [#"\""]) (fn _ => parse_str_aux []) x;

fun shows_sep s sep [] = shows_string []
  | shows_sep s sep [x] = s x
  | shows_sep s sep (x :: v :: va) = s x o sep o shows_sep s sep (v :: va);

fun null [] = true
  | null (x :: xs) = false;

fun shows_list_gen showsx e l s r xs = (if null xs then shows_string e else shows_string l o shows_sep showsx (shows_string s) xs o shows_string r);

fun showsp_list s p xs = shows_list_gen (s zero_nat) [#"[", #"]"] [#"["] [#",", #" "] [#"]"] xs;

fun shows_list_list A_ xss = showsp_list (shows_prec_list A_) zero_nat xss;

fun gen_length n (x :: xs) = gen_length (suc n) xs
  | gen_length n [] = n;

fun size_list x = gen_length zero_nat x;

fun trim x = dropWhile (member equal_char [#" ", #"\n", #"\t", #"\r"]) x;

fun drop n [] = []
  | drop n (x :: xs) = (if equal_nat n zero_nat then x :: xs else drop (minus_nat n one_nat) xs);

fun oneof_aux allowed (x :: xs) ts = (if equal_lista equal_char (mapa snd (zip x ts)) x then Inr (x, trim (drop (size_list x) ts)) else oneof_aux allowed xs ts)
  | oneof_aux allowed [] ts = err_expecting show_char ([#"o", #"n", #"e", #" ", #"o", #"f", #" "] @ shows_list_list show_char allowed []) ts;

fun oneof xs = oneof_aux xs xs;

fun eoi A_ [] = Inr ((), [])
  | eoi A_ (v :: va) = err_expecting A_ [#"e", #"n", #"d", #" ", #"o", #"f", #" ", #"i", #"n", #"p", #"u", #"t"] (v :: va);

fun parse_commenta x =
  bindb (exactly [#"/"])
    (fn _ => bindb stars1 (fn _ => bindb (many_c_a_t_c_h_a_l_l
                                           let
                                             val colon = (fn f => bindb f (fn _ => bindb (bindb (many (member equal_char [#" ", #"\n", #"\t", #"\r"])) (fn _ => returna ())) (fn _ => exactly [#":"])));
                                             val colon_s = colon o exactly;
                                             val str = (fn f => bindb f (fn _ => bindb (bindb (many (member equal_char [#" ", #"\n", #"\t", #"\r"])) (fn _ => returna ())) (fn _ => parse_str)));
                                           in
                                             bindb (bindb (many (member equal_char [#" ", #"\n", #"\t", #"\r"])) (fn _ => returna ()))
                                               (fn _ => or (bind3 (app_rev (app_rev (oneof [[#"I", #"N", #"V", #"A", #"R", #"I", #"A", #"N", #"T"], [#"I", #"N", #"V"]]) colon) str) Invariant)
                                                          (or (oneof_b_i_n_d
                                                                let
                                                                  val fnspec = [#"F", #"N", #"S", #"P", #"E", #"C"];
                                                                  val relspec = [#"R", #"E", #"L", #"S", #"P", #"E", #"C"];
                                                                  val modifies = [#"M", #"O", #"D", #"I", #"F", #"I", #"E", #"S"];
                                                                  val dONT_TRANSLATE = [#"D", #"O", #"N", #"T", #"_", #"T", #"R", #"A", #"N", #"S", #"L", #"A", #"T", #"E"];
                                                                in
                                                                  [bind3 (bindb (exactly fnspec)
                                                                           (fn _ => many_m_a_x (bindb (bindb (many (member equal_char [#" ", #"\n", #"\t", #"\r"])) (fn _ => returna ()))
                                                                                                 (fn _ => bindb (scan_upto_b_i_n_d
                                                                                                                  (bindb (bindb (many (member equal_char [#" ", #"\n", #"\t", #"\r"])) (fn _ => returna ())) (fn _ => exactly [#":"])))
                                                                                                            (fn (s1, _) =>
                                                                                                              bindb (bindb (many (member equal_char [#" ", #"\n", #"\t", #"\r"])) (fn _ => returna ()))
                                                                                                                (fn _ => bindb parse_str (fn s2 => returna (s1, s2))))))))
                                                                     Fnspeca,
                                                                    bind3 (app_rev (exactly relspec) str) Relspeca, bind3 (bindb (colon_s modifies) (fn _ => parse_id_list [fnspec, relspec, modifies, dONT_TRANSLATE])) Modifies,
                                                                    bind_k (exactly dONT_TRANSLATE) Dont_translate]
                                                                end)
                                                            (or (bind3 (app_rev (colon_s [#"A", #"U", #"X", #"U", #"P", #"D"]) str) Auxupda)
                                                              (or (bind3 (app_rev (colon_s [#"G", #"H", #"O", #"S", #"T", #"U", #"P", #"D"]) str) Ghostupda)
                                                                (or (bind3 (bind3 (app_rev (colon_s [#"S", #"P", #"E", #"C"]) str)
                                                                             (in_safe_monad (or (bindb (scan_upto_b_i_n_d (exactly [#"."])) (returna o fst)) (fn ts => returna ts []))))
                                                                      Speca)
                                                                  (or (bind3 (app_rev (colon_s [#"E", #"N", #"D", #"-", #"S", #"P", #"E", #"C"]) str) End_spec)
                                                                    (or (bind3 (bindb (exactly [#"C", #"A", #"L", #"L", #"S"]) (fn _ => parse_id_list [])) Calls)
                                                                      (bind3 (bindb (exactly [#"O", #"W", #"N", #"E", #"D", #"_", #"B", #"Y"])
                                                                               (fn _ => bindb (bindb (many (member equal_char [#" ", #"\n", #"\t", #"\r"])) (fn _ => returna ())) (fn _ => parse_id_o_n_e [])))
                                                                        Owned_by))))))))
                                           end)
                                     (fn cmd => bindb (scan_upto_b_i_n_d (bindb (bindb (many (member equal_char [#" ", #"\n", #"\t", #"\r"])) (fn _ => returna ())) (fn _ => end_comment)))
                                                  (fn (remain, _) => bindb (eoi show_char) (fn _ => returna (if null remain then cmd else cmd @ [OTHER remain]))))))
    x;

fun string_implode x = SS_base (STa x);

fun errora x = (error o String.implode o to_list) x;

fun parse_comment x =
  (fn a => (case a of Comment (_, s, SingleLine) => [OTHER s]
             | Comment (_, s, MultiLine) =>
               (case parse_commenta (to_list s) of Inl sa => errora (SS_base (STa sa)) | Inr (l, []) => mapa (map_comment_type string_implode) l | Inr (_, _ :: _) => errora (SS_base (ST "the remaining stream is not empty")))))
    x;

fun sbogwrap x = (Stmt o bogwrap) x;

fun filter_statement l =
  app_rev (app_rev l (mapa (map_filter let
                                         val inl = (fn s => fn f => app_rev (app_rev (app_rev (f (SS_base (STa s))) (BI_Stmt o sbogwrap)) Inl) SOME);
                                         val inr = (fn s => app_rev (app_rev s Inr) SOME);
                                       in
                                         (fn a => (case a of Invariant _ => NONE | Fnspeca _ => NONE | Relspeca _ => NONE | Modifies _ => NONE | Dont_translate => NONE | Auxupda s => inl s Auxupd | Ghostupda s => inl s Ghostupd
                                                    | Speca (s1, s2) => inr (Inl (SS_base (STa s1), SS_base (STa s2))) | End_spec s => inr (Inr (SS_base (STa s))) | Calls _ => NONE | Owned_by _ => NONE | OTHER _ => NONE))
                                       end o
                             parse_comment)))
    concat;

fun impl_of (Alist x) = x;

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

fun lookup A_ xa = map_of A_ (impl_of xa);

fun lookupa A_ = lookup A_;

fun get_column A_ (B1_, B2_) rbt pos = fold (fn (c, len) => fn ca => (if less B2_ c ca then plus B1_ ca len else ca)) (case lookupa A_ rbt pos of NONE => [] | SOME l_comm => l_comm);

fun pos_in_interval_haskell rbt =
  (fn a => (case a of ((Position0 (_, f1, l1, c1), p1), (Position0 (_, f2, l2, c2), p2)) =>
                     (fn aa => (case aa of Position0 (_, ff, ll, cc) =>
                                          let
                                            val b1 = equal_abr_stringa ff f1;
                                            val b2 = equal_abr_stringa ff f2;
                                          in
                                            (b1 orelse b2) andalso
                                              ((if b1 then l1 < ll orelse l1 = ll andalso get_column (equal_prod equal_abr_string equal_integer) (plus_integer, ord_integer) rbt (f1, l1) c1 + p1 <= cc + (1 : IntInf.int)
                                                 else true) andalso
                                                (if b2 then ll < l2 orelse ll = l2 andalso cc + (1 : IntInf.int) <= get_column (equal_prod equal_abr_string equal_integer) (plus_integer, ord_integer) rbt (f2, l2) c2 + p2 else true))
                                          end
                                 | NoPosition0 => false | BuiltinPosition0 => false | InternalPosition0 => false))
             | ((Position0 (_, _, _, _), _), (NoPosition0, _)) => (fn _ => false) | ((Position0 (_, _, _, _), _), (BuiltinPosition0, _)) => (fn _ => false) | ((Position0 (_, _, _, _), _), (InternalPosition0, _)) => (fn _ => false)
             | ((NoPosition0, _), _) => (fn _ => false) | ((BuiltinPosition0, _), _) => (fn _ => false) | ((InternalPosition0, _), _) => (fn _ => false)));

fun pos_in_interval_ml uu =
  (fn a => (case a of ((Position0 (off1, _, _, _), p1), (Position0 (off2, _, _, _), p2)) =>
                     (fn aa => (case aa of Position0 (off, _, _, _) => off1 + p1 <= off andalso off <= off2 + p2 | NoPosition0 => false | BuiltinPosition0 => false | InternalPosition0 => false))
             | ((Position0 (_, _, _, _), _), (NoPosition0, _)) => (fn _ => false) | ((Position0 (_, _, _, _), _), (BuiltinPosition0, _)) => (fn _ => false) | ((Position0 (_, _, _, _), _), (InternalPosition0, _)) => (fn _ => false)
             | ((NoPosition0, _), _) => (fn _ => false) | ((BuiltinPosition0, _), _) => (fn _ => false) | ((InternalPosition0, _), _) => (fn _ => false)));

fun pos_in_interval x = (case current_parsing_style of Style_Haskell => pos_in_interval_haskell | Style_ML => pos_in_interval_ml) x;

fun partition p [] = ([], [])
  | partition p (x :: xs) = let
                              val (yes, no) = partition p xs;
                            in
                              (if p x then (x :: yes, no) else (yes, x :: no))
                            end;

fun comment_interval x = (fn (l, rbt) => fn interv => app_rev (app_rev l (partition (fn Comment (pos, _, _) => pos_in_interval rbt interv pos))) fst) x;

fun return x acc = (acc, x);

fun bind m f acc = let
                     val (acca, x) = m acc;
                   in
                     f x acca
                   end;

fun foldM_o f = (fn a => (case a of None => return None | Some e => bind (f e) (fn ea => return (Some ea))));

fun unsupported s = let
                      val p = OnlyPos0 (NoPosition0, (NoPosition0, (0 : IntInf.int)));
                    in
                      return let
                               val _ = not_yet_supported (flatten [SS_base (ST "Statements in expression not yet supported "), s, SS_base (ST " (empty variable returned)")]);
                             in
                               CVar0 (Ident0 (SS_base (ST ""), (0 : IntInf.int), p), p)
                             end
                    end;

fun foldM f [] = return []
  | foldM f (x :: xs) = bind (f x) (fn xa => bind (foldM f xs) (fn xsa => return (xa :: xsa)));

fun stmt_out_of_expr e =
  (case e of CComma0 (l, _) => bind (foldM stmt_out_of_expr l) (fn _ => unsupported (SS_base (ST "CComma")))
    | CAssign0 (_, e1, e2, _) => bind (stmt_out_of_expr e1) (fn _ => bind (stmt_out_of_expr e2) (fn _ => unsupported (SS_base (ST "CAssign"))))
    | CCond0 (e1, o_e2, e3, pos) => bind (stmt_out_of_expr e1) (fn e1a => bind (foldM_o stmt_out_of_expr o_e2) (fn o_e2a => bind (stmt_out_of_expr e3) (fn e3a => return (CCond0 (e1a, o_e2a, e3a, pos)))))
    | CBinary0 (bin, e1, e2, pos) => bind (stmt_out_of_expr e1) (fn e1a => bind (stmt_out_of_expr e2) (fn e2a => return (CBinary0 (bin, e1a, e2a, pos))))
    | CCast0 (d, ea, pos) => bind (stmt_out_of_expr ea) (fn eb => return (CCast0 (d, eb, pos)))
    | CUnary0 (una, ea, pos) =>
      bind (stmt_out_of_expr ea)
        (fn eb => (case (case una of CPreIncOp0 => SOME (SS_base (ST "CPreIncOp")) | CPreDecOp0 => SOME (SS_base (ST "CPreDecOp")) | CPostIncOp0 => SOME (SS_base (ST "CPostIncOp")) | CPostDecOp0 => SOME (SS_base (ST "CPostDecOp"))
                          | CAdrOp0 => NONE | CIndOp0 => NONE | CPlusOp0 => NONE | CMinOp0 => NONE | CCompOp0 => NONE | CNegOp0 => NONE)
                    of NONE => return (CUnary0 (una, eb, pos)) | SOME s => unsupported (flatten [s, SS_base (ST " |> CUnary")])))
    | CSizeofExpr0 (cExpression, a) => return (CSizeofExpr0 (cExpression, a)) | CSizeofType0 (cDeclaration, a) => return (CSizeofType0 (cDeclaration, a)) | CAlignofExpr0 (cExpression, a) => return (CAlignofExpr0 (cExpression, a))
    | CAlignofType0 (_, _) => unsupported (SS_base (ST "CAlignofType")) | CComplexReal0 (cExpression, a) => return (CComplexReal0 (cExpression, a)) | CComplexImag0 (cExpression, a) => return (CComplexImag0 (cExpression, a))
    | CIndex0 (e1, e2, pos) => bind (stmt_out_of_expr e2) (fn e2a => bind (stmt_out_of_expr e1) (fn e1a => return (CIndex0 (e1a, e2a, pos))))
    | CCall0 (ea, l, pos) => bind (stmt_out_of_expr ea) (fn eb => bind (foldM stmt_out_of_expr l) (fn la => return (CCall0 (eb, la, pos)))) | CMember0 (cExpression, ident, boola, a) => return (CMember0 (cExpression, ident, boola, a))
    | CVar0 (ident, a) => return (CVar0 (ident, a)) | CConst0 cConstant => return (CConst0 cConstant) | CCompoundLit0 (cDeclaration, lista, a) => return (CCompoundLit0 (cDeclaration, lista, a))
    | CGenericSelection0 (cExpression, lista, a) => return (CGenericSelection0 (cExpression, lista, a)) | CStatExpr0 (_, _) => unsupported (SS_base (ST "CStatExpr")) | CLabAddrExpr0 (ident, a) => return (CLabAddrExpr0 (ident, a))
    | CBuiltinExpr0 _ => unsupported (SS_base (ST "CBuiltinExpr")));

fun stmt_out_of_expra x = app_rev (stmt_out_of_expr x ()) snd;

fun map_optiona f NONE = NONE
  | map_optiona f (SOME x2) = SOME (f x2);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun filter_gen f1 f2 l = (case maps (map_filter (map_optiona string_implode o f1) o parse_comment) l of [] => NONE | [x] => SOME (f2 x));

fun filter_owned_by x =
  filter_gen (fn a => (case a of Invariant _ => NONE | Fnspeca _ => NONE | Relspeca _ => NONE | Modifies _ => NONE | Dont_translate => NONE | Auxupda _ => NONE | Ghostupda _ => NONE | Speca _ => NONE | End_spec _ => NONE
                        | Calls _ => NONE | Owned_by aa => SOME aa | OTHER _ => NONE))
    OWNED_BY x;

fun tree_of_decl_spec s =
  let
    val CStruct0 (tag, n, opt, l, a) = s;
    val l_opt = (case opt of None => [] | Some la => la);
  in
    Struct_tree (ident_option n, (tag, (l_opt, (l, a))),
                  mapa (fn CDecl0 (l1, l2, _) =>
                         (case map_filter (fn aa => (case aa of CStorageSpec0 _ => NONE
                                                      | CTypeSpec0 ab =>
                                                        (case ab of CVoidType0 _ => NONE | CCharType0 _ => NONE | CShortType0 _ => NONE | CIntType0 _ => NONE | CLongType0 _ => NONE | CFloatType0 _ => NONE | CDoubleType0 _ => NONE
                                                          | CSignedType0 _ => NONE | CUnsigType0 _ => NONE | CBoolType0 _ => NONE | CComplexType0 _ => NONE | CInt128Type0 _ => NONE | CSUType0 (CStruct0 (_, _, None, _, _), _) => NONE
                                                          | CSUType0 (CStruct0 (taga, na, Some l0, la, ac), _) => SOME (CStruct0 (taga, na, Some l0, la, ac), (taga, l2)) | CEnumType0 (_, _) => NONE | CTypeDef0 (_, _) => NONE
                                                          | CTypeOfExpr0 (_, _) => NONE | CTypeOfType0 (_, _) => NONE | CAtomicType0 (_, _) => NONE)
                                                      | CTypeQual0 _ => NONE | CFunSpec0 _ => NONE | CAlignSpec0 _ => NONE))
                                 l1
                           of [] => Inr (l1, l2) | [x] => Inl (map_prod tree_of_decl_spec id x) | _ :: _ :: _ => Inr (l1, l2)))
                    l_opt)
  end;

fun fresh_ident x = (SS_base o ST o fresh_ident0) x;

fun concat_map x = comp2 concat mapa x;

fun struct_conv a =
  let
    val Struct_tree (n, na, child) = a;
    val nb = (case n of NONE => flatten [SS_base (ST "ISA_anon_struct|"), fresh_ident ()] | SOME aa => ident_struct_type0 aa);
  in
    (nb, (case child of [] => [Struct_leaf (Inl (nb, na))]
           | _ :: _ => let
                         val l = mapa (map_sum (map_prod struct_conv id) id) child;
                       in
                         Struct_root (nb, na, mapa (fn aa => (case aa of Inl ((x, _), nc) => Inl (x, nc) | Inr ab => Inr ab)) l) :: concat_map (fn aa => (case aa of Inl ((_, la), _) => la | Inr b => [Struct_leaf (Inr b)])) l
                       end))
  end;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun extract p (x :: xs) = (if p x then SOME ([], (x, xs)) else (case extract p xs of NONE => NONE | SOME (ys, (y, zs)) => SOME (x :: ys, (y, zs))))
  | extract p [] = NONE;

fun decl_spec0 l_decl_spec =
  (fn (l_arg, pos_arg) =>
    (case map_filter (fn a => (case a of CStorageSpec0 _ => NONE | CTypeSpec0 (CVoidType0 _) => NONE | CTypeSpec0 (CCharType0 _) => NONE | CTypeSpec0 (CShortType0 _) => NONE | CTypeSpec0 (CIntType0 _) => NONE
                                | CTypeSpec0 (CLongType0 _) => NONE | CTypeSpec0 (CFloatType0 _) => NONE | CTypeSpec0 (CDoubleType0 _) => NONE | CTypeSpec0 (CSignedType0 _) => NONE | CTypeSpec0 (CUnsigType0 _) => NONE
                                | CTypeSpec0 (CBoolType0 _) => NONE | CTypeSpec0 (CComplexType0 _) => NONE | CTypeSpec0 (CInt128Type0 _) => NONE | CTypeSpec0 (CSUType0 (_, _)) => NONE
                                | CTypeSpec0 (CEnumType0 (CEnum0 (_, None, _, _), _)) => NONE | CTypeSpec0 (CEnumType0 (CEnum0 (_, Some [], _, _), _)) => NONE
                                | CTypeSpec0 (CEnumType0 (CEnum0 (n, Some (x :: xs), _, _), _)) => SOME (EnumDecl0 (bogwrap (ident_option n), mapa (fn (i, e) => (ident i, map_option expression e)) (x :: xs)))
                                | CTypeSpec0 (CTypeDef0 (_, _)) => NONE | CTypeSpec0 (CTypeOfExpr0 (_, _)) => NONE | CTypeSpec0 (CTypeOfType0 (_, _)) => NONE | CTypeSpec0 (CAtomicType0 (_, _)) => NONE | CTypeQual0 _ => NONE
                                | CFunSpec0 _ => NONE | CAlignSpec0 _ => NONE))
            l_decl_spec
      of [] => [] | x :: _ => [x]) @
      let
        val a = (case map_filter (fn a => (case a of CStorageSpec0 _ => NONE
                                            | CTypeSpec0 aa =>
                                              (case aa of CVoidType0 _ => NONE | CCharType0 _ => NONE | CShortType0 _ => NONE | CIntType0 _ => NONE | CLongType0 _ => NONE | CFloatType0 _ => NONE | CDoubleType0 _ => NONE
                                                | CSignedType0 _ => NONE | CUnsigType0 _ => NONE | CBoolType0 _ => NONE | CComplexType0 _ => NONE | CInt128Type0 _ => NONE
                                                | CSUType0 (CStruct0 (tag, n, opt, l, ab), _) => map_option (fn _ => (CStruct0 (tag, n, opt, l, ab), tag)) opt | CEnumType0 (_, _) => NONE | CTypeDef0 (_, _) => NONE
                                                | CTypeOfExpr0 (_, _) => NONE | CTypeOfType0 (_, _) => NONE | CAtomicType0 (_, _) => NONE)
                                            | CTypeQual0 _ => NONE | CFunSpec0 _ => NONE | CAlignSpec0 _ => NONE))
                        l_decl_spec
                  of [] => (NONE, [])
                  | (s, tag) :: _ =>
                    map_prod (SOME o decl_spec_ty_tag tag)
                      (map_filter (fn a => (case a of Struct_root (sa, n, l) => SOME (StructDecl0_root (sa, (n, l))) | Struct_leaf (Inl d) => SOME (StructDecl0_child d) | Struct_leaf (Inr _) => NONE)))
                      (struct_conv (tree_of_decl_spec s)));
        val (struct_name, aa) = a;
      in
        (if list_ex (fn ab => (case ab of CStorageSpec0 (CAuto0 _) => false | CStorageSpec0 (CRegister0 _) => false | CStorageSpec0 (CStatic0 _) => false | CStorageSpec0 (CExtern0 _) => false | CStorageSpec0 (CTypedef0 _) => true
                                | CStorageSpec0 (CThread0 _) => false | CTypeSpec0 _ => false | CTypeQual0 _ => false | CFunSpec0 _ => false | CAlignSpec0 _ => false))
              l_decl_spec
          then mapa (fn ((Some (CDeclr0 (n, dDs, _, _, _)), _), _) => TypeDecl0 (n, (struct_name, dDs))) l_arg
          else app_rev (foldr (fn ((Some (CDeclr0 (n, dDs, _, gcc_attr, pos)), init), _) => fn (acc, pos2) =>
                                let
                                  val pos1 = p_first_of_NodeInfo pos;
                                in
                                  ((case extract (fn ab => (case ab of CPtrDeclr0 (_, _) => false | CArrDeclr0 (_, _, _) => false | CFunDeclr0 (_, _, _) => true)) dDs
                                     of NONE => VarDecl0 (n, (struct_name, (dDs, (init, (pos1, (pos2, gcc_attr)))))) | SOME ab => let
              val (dDs0, ac) = ab;
              val (CFunDeclr0 (l_arga, l_attr, ad), dDs1) = ac;
            in
              ExtFnDecl0 (n, (dDs0, ((l_arga, (l_attr, ad)), (dDs1, gcc_attr))))
            end) ::
                                     acc,
                                    pos1)
                                end)
                         l_arg ([], pos_arg))
                 fst) @
          aa
      end);

fun identa x = (fn Ident0 (s, _, _) => pref_ident (if equal_abr_stringa s (SS_base (ST "const")) then flatten [SS_base (ST "__"), s, SS_base (ST "__")] else s)) x;

fun attrs0 x = (fn a => (case a of CAttr0 (i, [], _) => GCC_AttribID (identa i) | CAttr0 (i, aa :: lista, _) => GCC_AttribFn (ident i, mapa expression (aa :: lista)))) x;

val empty : ('a, 'b) alist = Alist [];

val emptya : ('a, 'b) alist = empty;

fun update A_ k v [] = [(k, v)]
  | update A_ k v (p :: ps) = (if eq A_ (fst p) k then (k, v) :: ps else p :: update A_ k v ps);

fun updatea A_ xc xd xe = Alist (update A_ xc xd (impl_of xe));

fun insert A_ = updatea A_;

fun union_loada A_ = fold (fn x => fn (_, (acc, rbt)) => (false, (case lookupa A_ rbt x of NONE => (x :: acc, insert A_ x () rbt) | SOME _ => (acc, rbt))));

fun entries x = impl_of x;

fun is_empty l = null (entries l);

fun keys_emptya f = (fn (b, (acc, rbt)) => (if b andalso is_empty rbt then [] else [f (rev acc)]));

fun bulkload A_ l = fold (fn (a, b) => insert A_ a b) l emptya;

fun folda f = fold (fn (a, b) => f a b) o entries;

fun union A_ l1 l2 = folda (insert A_) l2 l1;

fun union_load A_ l = map_prod (fn _ => false) (union A_ (bulkload A_ (mapa (fn x => (x, ())) l)));

fun keys x = (mapa fst o impl_of) x;

fun keys_empty f = (fn (b, rbt) => (if b andalso is_empty rbt then [] else [f (keys rbt)]));

fun collapse_mod_attribs l =
  let
    val (mods, (attribs, specs)) =
      fold (fn x => fn (mods, (attribs, specs)) =>
             (case x of Fnspec _ => (mods, (attribs, x :: specs)) | Relspec _ => (mods, (attribs, x :: specs)) | Fn_modifies la => (union_load equal_abr_string la mods, (attribs, specs))
               | Didnt_translate => (mods, (attribs, x :: specs)) | Gcc_attribs la => (mods, (union_loada equal_gcc_attribute la attribs, specs))))
        l ((true, emptya), ((true, ([], emptya)), []));
  in
    keys_empty Fn_modifies mods @ keys_emptya Gcc_attribs attribs @ specs
  end;

fun filter_fnspec x =
  (concat o mapa (map_filter (fn a => (case a of Invariant _ => NONE
                                        | Fnspeca l =>
                                          app_rev (app_rev (app_rev (app_rev (app_rev l (mapa (fn (s1, s2) => let
                                                                                                                val (s1a, s2a) = map_prod string_implode string_implode (s1, s2);
                                                                                                              in
                                                                                                                flatten [s1a, SS_base (ST ": \""), s2a, SS_base (ST "\"")]
                                                                                                              end)))
                                                                      (fn aa => String_concatWith (SS_base (ST "\n"), aa)))
                                                             bogwrap)
                                                    Fnspec)
                                            SOME
                                        | Relspeca s => app_rev (app_rev (app_rev (flatten [SS_base (ST "\""), SS_base (STa s), SS_base (ST "\"")]) bogwrap) Relspec) SOME
                                        | Modifies l => app_rev (app_rev (app_rev l (mapa (fn aa => (case aa of NONE => SS_base (ST "phantom_machine_state") | SOME s => SS_base (STa s))))) Fn_modifies) SOME
                                        | Dont_translate => app_rev Didnt_translate SOME | Auxupda _ => NONE | Ghostupda _ => NONE | Speca _ => NONE | End_spec _ => NONE | Calls _ => NONE | Owned_by _ => NONE | OTHER _ => NONE)) o
                   parse_comment))
    x;

fun attrs l_decl_spec dDs gcc_attr pos_rbt =
  let
    val l = concat [map_filter (fn a => (case a of CStorageSpec0 _ => NONE | CTypeSpec0 _ => NONE | CTypeQual0 (CConstQual0 _) => NONE | CTypeQual0 (CVolatQual0 _) => NONE | CTypeQual0 (CRestrQual0 _) => NONE
                                          | CTypeQual0 (CAtomicQual0 _) => NONE | CTypeQual0 (CAttrQual0 x) => SOME (attrs0 x) | CTypeQual0 (CNullableQual0 _) => NONE | CTypeQual0 (CNonnullQual0 _) => NONE
                                          | CFunSpec0 (CInlineQual0 _) => NONE | CFunSpec0 (CNoreturnQual0 _) => SOME (GCC_AttribID (SS_base (ST "noreturn"))) | CAlignSpec0 _ => NONE))
                      (rev l_decl_spec),
                     mapa attrs0 (concat_map let
                                               val f_attr = map_filter (fn a => (case a of CConstQual0 _ => NONE | CVolatQual0 _ => NONE | CRestrQual0 _ => NONE | CAtomicQual0 _ => NONE | CAttrQual0 aa => SOME aa
                                                                                  | CNullableQual0 _ => NONE | CNonnullQual0 _ => NONE));
                                             in
                                               (fn a => (case a of CPtrDeclr0 (l, _) => f_attr l | CArrDeclr0 (l, _, _) => f_attr l | CFunDeclr0 (_, l, _) => l))
                                             end
                                    dDs @
                                   gcc_attr)];
    val fnspec = (case pos_rbt of ((_, NONE), _) => [] | ((rbt, SOME pos1), pos2) => filter_fnspec (comment_interval rbt (pos1, pos2)));
  in
    collapse_mod_attribs (if null l then fnspec else Gcc_attribs l :: fnspec)
  end;

fun decl_spec l_decl_spec l_arg pos_rbt =
  mapa let
         val mk_id = (fn Some i => bogwrap (ident i));
         val f_struct_ty = (fn dDs => fn a => (case a of NONE => deriv_decl_spec dDs l_decl_spec | SOME aa => deriv_decl_spec0 dDs aa));
       in
         (fn a => (case a of VarDecl0 (n, (struct_name, (dDs, (init, (pos1, (pos2, gcc_attr)))))) =>
                            VarDecl (f_struct_ty dDs struct_name,
                                      (mk_id n, (map_filter (fn aa => (case aa of CStorageSpec0 (CAuto0 _) => NONE | CStorageSpec0 (CRegister0 _) => SOME SC_REGISTER | CStorageSpec0 (CStatic0 _) => SOME SC_STATIC
                                                                        | CStorageSpec0 (CExtern0 _) => SOME SC_EXTERN | CStorageSpec0 (CTypedef0 _) => NONE | CStorageSpec0 (CThread0 _) => NONE | CTypeSpec0 _ => NONE
                                                                        | CTypeQual0 _ => NONE | CFunSpec0 _ => NONE | CAlignSpec0 _ => NONE))
                                                   l_decl_spec,
                                                  (map_option (initializer0 stmt_out_of_expra) init, let
                                                                                                       val l = rev (mapa attrs0 gcc_attr);
                                                                                                     in
                                                                                                       (case filter_owned_by (comment_interval let
                           val ((rbt, _), _) = pos_rbt;
                         in
                           rbt
                         end
         (pos1, pos2))
                                                                                                         of NONE => l | SOME x => x :: l)
                                                                                                     end))))
                    | StructDecl0_root (n, (_, l)) =>
                      StructDecl (bogwrap n, maps (fn aa => (case aa of Inl ab => let
                                                                                    val (s, ac) = ab;
                                                                                    val (tag, ad) = ac;
                                                                                  in
                                                                                    mapa (fn ((Some (CDeclr0 (Some i, dDs, _, _, _)), _), _) => (deriv_decl_spec0 dDs (decl_spec_ty_tag tag s), bogwrap (ident_struct_const i))) ad
                                                                                  end
                                                              | Inr ab => let
                                                                            val (l_decl_speca, ac) = ab;
                                                                          in
                                                                            mapa (fn ad => (case ad of ((None, None), Some e) =>
                                                                                                      let
                                                                                                        val (b, msg) =
                                                                                                          (case decl_spec_ty l_decl_speca of Signed _ => (true, SS_base (ST "Signed")) | Unsigned _ => (false, SS_base (ST "Unsigned"))
                                                                                                            | Bool => (false, SS_base (ST "Unsigned (default)")) | PlainChar => (false, SS_base (ST "Unsigned (default)"))
                                                                                                            | StructTy _ => (false, SS_base (ST "Unsigned (default)")) | UnionTy _ => (false, SS_base (ST "Unsigned (default)"))
                                                                                                            | EnumTy _ => (false, SS_base (ST "Unsigned (default)")) | Ptr _ => (false, SS_base (ST "Unsigned (default)"))
                                                                                                            | Array (_, _) => (false, SS_base (ST "Unsigned (default)")) | Bitfield (_, _) => (false, SS_base (ST "Unsigned (default)"))
                                                                                                            | Identa _ => (false, SS_base (ST "Unsigned (default)")) | Function (_, _) => (false, SS_base (ST "Unsigned (default)"))
                                                                                                            | Void => (false, SS_base (ST "Unsigned (default)")));
                                                                                                        val _ = not_yet_supported (flatten [SS_base (ST "Anonymous bitfield ("), msg, SS_base (ST " returned) not yet supported")]);
                                                                                                      in
                                                                                                        (Bitfield (b, expression e), bogwrap (SS_base (ST "")))
                                                                                                      end
                                                                                             | ((Some (CDeclr0 (Some i, dDs, _, _, _)), _), _) => (deriv_decl_spec dDs l_decl_speca, bogwrap (ident_struct_const i))))
                                                                              ac
                                                                          end))
                                               l)
                    | StructDecl0_child (n, (_, (l_child, (_, _)))) =>
                      StructDecl (bogwrap n, maps (fn CDecl0 (l_decl_speca, l_prod, _) => mapa (fn ((Some (CDeclr0 (Some i, dDs, _, _, _)), _), _) => (deriv_decl_spec dDs l_decl_speca, bogwrap (ident i))) l_prod) l_child)
                    | TypeDecl0 (n, (struct_name, dDs)) => TypeDecl [(f_struct_ty dDs struct_name, mk_id n)]
                    | ExtFnDecl0 aa =>
                      let
                        val (Some i, (dDs0, ab)) = aa;
                        val ((l_arga, ac), aaa) = ab;
                        val (l_attr, ad) = ac;
                        val (dDs1, gcc_attr) = aaa;
                      in
                        ExtFnDecl (deriv_decl_spec dDs1 l_decl_spec, bogwrap (ident i),
                                    (case l_arga of Left ae => mapa (fn x => (identb x, NONE)) ae
                                      | Right ae =>
                                        (case ae of ([], true) => let
                                                                    val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                  in
                                                                    []
                                                                  end
                                          | ([], false) =>
                                            mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                   let
                                                     val (n, dDs) =
                                                       (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                         | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                   in
                                                     (deriv_decl_spec dDs l_decl_speca, n)
                                                   end)
                                              []
                                          | (aab :: lista, af) =>
                                            (case aab of CDecl0 ([], list2, xa) =>
                                                        (case af of true => let
                                                                              val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                            in
                                                                              []
                                                                            end
                                                          | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                            let
                                                                              val (n, dDs) =
                                                                                (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                                  | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                            in
                                                                              (deriv_decl_spec dDs l_decl_speca, n)
                                                                            end)
                                                                       (CDecl0 ([], list2, xa) :: lista))
                                              | CDecl0 (aba :: listb, list2, xa) =>
                                                (case aba of CStorageSpec0 cStorageSpecifier =>
                                                            (case af of true => let
                                                                                  val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                                in
                                                                                  []
                                                                                end
                                                              | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                                let
                                                                                  val (n, dDs) =
                                                                                    (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                                      | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                                in
                                                                                  (deriv_decl_spec dDs l_decl_speca, n)
                                                                                end)
                                                                           (CDecl0 (CStorageSpec0 cStorageSpecifier :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CVoidType0 x) =>
                                                    (case listb of [] => (case list2 of [] => (case lista of [] => (case af of true =>
        let
          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
        in
          []
        end
                                                                                                                     | false => [])
                                                                                                | ada :: listaa =>
                                                                                                  (case af of true => let
  val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
in
  []
end
                                                                                                    | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
let
  val (n, dDs) = (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs) | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
in
  (deriv_decl_spec dDs l_decl_speca, n)
end)
                                                                                                                 (CDecl0 ([CTypeSpec0 (CVoidType0 x)], [], xa) :: ada :: listaa)))
                                                                           | ada :: listba =>
                                                                             (case af of true => let
                                                                                                   val _ = not_yet_supported
                                                                                                             (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                                                 in
                                                                                                   []
                                                                                                 end
                                                                               | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                                                 let
                                                                                                   val (n, dDs) =
                                                                                                     (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, [])
                                                                                                       | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                                                       | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                                                 in
                                                                                                   (deriv_decl_spec dDs l_decl_speca, n)
                                                                                                 end)
                                                                                            (CDecl0 ([CTypeSpec0 (CVoidType0 x)], ada :: listba, xa) :: lista)))
                                                      | ada :: listc =>
                                                        (case af of true => let
                                                                              val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                            in
                                                                              []
                                                                            end
                                                          | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                            let
                                                                              val (n, dDs) =
                                                                                (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                                  | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                            in
                                                                              (deriv_decl_spec dDs l_decl_speca, n)
                                                                            end)
                                                                       (CDecl0 (CTypeSpec0 (CVoidType0 x) :: ada :: listc, list2, xa) :: lista)))
                                                  | CTypeSpec0 (CCharType0 abb) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CCharType0 abb) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CShortType0 abb) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CShortType0 abb) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CIntType0 abb) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CIntType0 abb) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CLongType0 abb) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CLongType0 abb) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CFloatType0 abb) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CFloatType0 abb) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CDoubleType0 abb) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CDoubleType0 abb) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CSignedType0 abb) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CSignedType0 abb) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CUnsigType0 abb) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CUnsigType0 abb) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CBoolType0 abb) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CBoolType0 abb) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CComplexType0 abb) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CComplexType0 abb) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CInt128Type0 abb) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CInt128Type0 abb) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CSUType0 (cStructureUnion, abb)) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CSUType0 (cStructureUnion, abb)) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CEnumType0 (cEnumeration, abb)) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CEnumType0 (cEnumeration, abb)) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CTypeDef0 (identa, abb)) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CTypeDef0 (identa, abb)) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CTypeOfExpr0 (cExpression, abb)) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CTypeOfExpr0 (cExpression, abb)) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CTypeOfType0 (cDeclaration, abb)) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CTypeOfType0 (cDeclaration, abb)) :: listb, list2, xa) :: lista))
                                                  | CTypeSpec0 (CAtomicType0 (cDeclaration, abb)) =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeSpec0 (CAtomicType0 (cDeclaration, abb)) :: listb, list2, xa) :: lista))
                                                  | CTypeQual0 cTypeQualifier =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CTypeQual0 cTypeQualifier :: listb, list2, xa) :: lista))
                                                  | CFunSpec0 cFunctionSpecifier =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CFunSpec0 cFunctionSpecifier :: listb, list2, xa) :: lista))
                                                  | CAlignSpec0 cAlignmentSpecifier =>
                                                    (case af of true => let
                                                                          val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                        in
                                                                          []
                                                                        end
                                                      | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                        let
                                                                          val (n, dDs) =
                                                                            (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                              | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                        in
                                                                          (deriv_decl_spec dDs l_decl_speca, n)
                                                                        end)
                                                                   (CDecl0 (CAlignSpec0 cAlignmentSpecifier :: listb, list2, xa) :: lista)))
                                              | CStaticAssert0 (cExpression, cStringLiteral, aac) =>
                                                (case af of true => let
                                                                      val _ = not_yet_supported (flatten [SS_base (ST "Variadic function not yet supported in "), ident i, SS_base (ST " (empty list returned)")]);
                                                                    in
                                                                      []
                                                                    end
                                                  | false => mapa (fn CDecl0 (l_decl_speca, l_name, _) =>
                                                                    let
                                                                      val (n, dDs) =
                                                                        (case l_name of [] => (NONE, []) | ((None, _), _) :: _ => (NONE, []) | [((Some (CDeclr0 (n, dDs, _, _, _)), _), _)] => (ident_option n, dDs)
                                                                          | ((Some (CDeclr0 (_, _, _, _, _)), _), _) :: _ :: _ => (NONE, []));
                                                                    in
                                                                      (deriv_decl_spec dDs l_decl_speca, n)
                                                                    end)
                                                               (CStaticAssert0 (cExpression, cStringLiteral, aac) :: lista))))),
                                    attrs l_decl_spec (dDs0 @ CFunDeclr0 (l_arga, l_attr, ad) :: dDs1) gcc_attr pos_rbt)
                      end
                    | EnumDecl0 (n, l) => EnumDecl (n, mapa (map_prod bogwrap id) l)))
       end
    (decl_spec0 l_decl_spec l_arg);

fun declaration pos_rbt f_decl = (fn CDecl0 (l_decl_spec, l_arg, pos) => mapa (f_decl o bogwrap) (decl_spec l_decl_spec (l_arg, p_last_of_NodeInfo pos) (pos_rbt, p_first_of_NodeInfo pos)));

fun equal_CAssignOp CXorAssOp0 COrAssOp0 = false
  | equal_CAssignOp COrAssOp0 CXorAssOp0 = false
  | equal_CAssignOp CAndAssOp0 COrAssOp0 = false
  | equal_CAssignOp COrAssOp0 CAndAssOp0 = false
  | equal_CAssignOp CAndAssOp0 CXorAssOp0 = false
  | equal_CAssignOp CXorAssOp0 CAndAssOp0 = false
  | equal_CAssignOp CShrAssOp0 COrAssOp0 = false
  | equal_CAssignOp COrAssOp0 CShrAssOp0 = false
  | equal_CAssignOp CShrAssOp0 CXorAssOp0 = false
  | equal_CAssignOp CXorAssOp0 CShrAssOp0 = false
  | equal_CAssignOp CShrAssOp0 CAndAssOp0 = false
  | equal_CAssignOp CAndAssOp0 CShrAssOp0 = false
  | equal_CAssignOp CShlAssOp0 COrAssOp0 = false
  | equal_CAssignOp COrAssOp0 CShlAssOp0 = false
  | equal_CAssignOp CShlAssOp0 CXorAssOp0 = false
  | equal_CAssignOp CXorAssOp0 CShlAssOp0 = false
  | equal_CAssignOp CShlAssOp0 CAndAssOp0 = false
  | equal_CAssignOp CAndAssOp0 CShlAssOp0 = false
  | equal_CAssignOp CShlAssOp0 CShrAssOp0 = false
  | equal_CAssignOp CShrAssOp0 CShlAssOp0 = false
  | equal_CAssignOp CSubAssOp0 COrAssOp0 = false
  | equal_CAssignOp COrAssOp0 CSubAssOp0 = false
  | equal_CAssignOp CSubAssOp0 CXorAssOp0 = false
  | equal_CAssignOp CXorAssOp0 CSubAssOp0 = false
  | equal_CAssignOp CSubAssOp0 CAndAssOp0 = false
  | equal_CAssignOp CAndAssOp0 CSubAssOp0 = false
  | equal_CAssignOp CSubAssOp0 CShrAssOp0 = false
  | equal_CAssignOp CShrAssOp0 CSubAssOp0 = false
  | equal_CAssignOp CSubAssOp0 CShlAssOp0 = false
  | equal_CAssignOp CShlAssOp0 CSubAssOp0 = false
  | equal_CAssignOp CAddAssOp0 COrAssOp0 = false
  | equal_CAssignOp COrAssOp0 CAddAssOp0 = false
  | equal_CAssignOp CAddAssOp0 CXorAssOp0 = false
  | equal_CAssignOp CXorAssOp0 CAddAssOp0 = false
  | equal_CAssignOp CAddAssOp0 CAndAssOp0 = false
  | equal_CAssignOp CAndAssOp0 CAddAssOp0 = false
  | equal_CAssignOp CAddAssOp0 CShrAssOp0 = false
  | equal_CAssignOp CShrAssOp0 CAddAssOp0 = false
  | equal_CAssignOp CAddAssOp0 CShlAssOp0 = false
  | equal_CAssignOp CShlAssOp0 CAddAssOp0 = false
  | equal_CAssignOp CAddAssOp0 CSubAssOp0 = false
  | equal_CAssignOp CSubAssOp0 CAddAssOp0 = false
  | equal_CAssignOp CRmdAssOp0 COrAssOp0 = false
  | equal_CAssignOp COrAssOp0 CRmdAssOp0 = false
  | equal_CAssignOp CRmdAssOp0 CXorAssOp0 = false
  | equal_CAssignOp CXorAssOp0 CRmdAssOp0 = false
  | equal_CAssignOp CRmdAssOp0 CAndAssOp0 = false
  | equal_CAssignOp CAndAssOp0 CRmdAssOp0 = false
  | equal_CAssignOp CRmdAssOp0 CShrAssOp0 = false
  | equal_CAssignOp CShrAssOp0 CRmdAssOp0 = false
  | equal_CAssignOp CRmdAssOp0 CShlAssOp0 = false
  | equal_CAssignOp CShlAssOp0 CRmdAssOp0 = false
  | equal_CAssignOp CRmdAssOp0 CSubAssOp0 = false
  | equal_CAssignOp CSubAssOp0 CRmdAssOp0 = false
  | equal_CAssignOp CRmdAssOp0 CAddAssOp0 = false
  | equal_CAssignOp CAddAssOp0 CRmdAssOp0 = false
  | equal_CAssignOp CDivAssOp0 COrAssOp0 = false
  | equal_CAssignOp COrAssOp0 CDivAssOp0 = false
  | equal_CAssignOp CDivAssOp0 CXorAssOp0 = false
  | equal_CAssignOp CXorAssOp0 CDivAssOp0 = false
  | equal_CAssignOp CDivAssOp0 CAndAssOp0 = false
  | equal_CAssignOp CAndAssOp0 CDivAssOp0 = false
  | equal_CAssignOp CDivAssOp0 CShrAssOp0 = false
  | equal_CAssignOp CShrAssOp0 CDivAssOp0 = false
  | equal_CAssignOp CDivAssOp0 CShlAssOp0 = false
  | equal_CAssignOp CShlAssOp0 CDivAssOp0 = false
  | equal_CAssignOp CDivAssOp0 CSubAssOp0 = false
  | equal_CAssignOp CSubAssOp0 CDivAssOp0 = false
  | equal_CAssignOp CDivAssOp0 CAddAssOp0 = false
  | equal_CAssignOp CAddAssOp0 CDivAssOp0 = false
  | equal_CAssignOp CDivAssOp0 CRmdAssOp0 = false
  | equal_CAssignOp CRmdAssOp0 CDivAssOp0 = false
  | equal_CAssignOp CMulAssOp0 COrAssOp0 = false
  | equal_CAssignOp COrAssOp0 CMulAssOp0 = false
  | equal_CAssignOp CMulAssOp0 CXorAssOp0 = false
  | equal_CAssignOp CXorAssOp0 CMulAssOp0 = false
  | equal_CAssignOp CMulAssOp0 CAndAssOp0 = false
  | equal_CAssignOp CAndAssOp0 CMulAssOp0 = false
  | equal_CAssignOp CMulAssOp0 CShrAssOp0 = false
  | equal_CAssignOp CShrAssOp0 CMulAssOp0 = false
  | equal_CAssignOp CMulAssOp0 CShlAssOp0 = false
  | equal_CAssignOp CShlAssOp0 CMulAssOp0 = false
  | equal_CAssignOp CMulAssOp0 CSubAssOp0 = false
  | equal_CAssignOp CSubAssOp0 CMulAssOp0 = false
  | equal_CAssignOp CMulAssOp0 CAddAssOp0 = false
  | equal_CAssignOp CAddAssOp0 CMulAssOp0 = false
  | equal_CAssignOp CMulAssOp0 CRmdAssOp0 = false
  | equal_CAssignOp CRmdAssOp0 CMulAssOp0 = false
  | equal_CAssignOp CMulAssOp0 CDivAssOp0 = false
  | equal_CAssignOp CDivAssOp0 CMulAssOp0 = false
  | equal_CAssignOp CAssignOp0 COrAssOp0 = false
  | equal_CAssignOp COrAssOp0 CAssignOp0 = false
  | equal_CAssignOp CAssignOp0 CXorAssOp0 = false
  | equal_CAssignOp CXorAssOp0 CAssignOp0 = false
  | equal_CAssignOp CAssignOp0 CAndAssOp0 = false
  | equal_CAssignOp CAndAssOp0 CAssignOp0 = false
  | equal_CAssignOp CAssignOp0 CShrAssOp0 = false
  | equal_CAssignOp CShrAssOp0 CAssignOp0 = false
  | equal_CAssignOp CAssignOp0 CShlAssOp0 = false
  | equal_CAssignOp CShlAssOp0 CAssignOp0 = false
  | equal_CAssignOp CAssignOp0 CSubAssOp0 = false
  | equal_CAssignOp CSubAssOp0 CAssignOp0 = false
  | equal_CAssignOp CAssignOp0 CAddAssOp0 = false
  | equal_CAssignOp CAddAssOp0 CAssignOp0 = false
  | equal_CAssignOp CAssignOp0 CRmdAssOp0 = false
  | equal_CAssignOp CRmdAssOp0 CAssignOp0 = false
  | equal_CAssignOp CAssignOp0 CDivAssOp0 = false
  | equal_CAssignOp CDivAssOp0 CAssignOp0 = false
  | equal_CAssignOp CAssignOp0 CMulAssOp0 = false
  | equal_CAssignOp CMulAssOp0 CAssignOp0 = false
  | equal_CAssignOp COrAssOp0 COrAssOp0 = true
  | equal_CAssignOp CXorAssOp0 CXorAssOp0 = true
  | equal_CAssignOp CAndAssOp0 CAndAssOp0 = true
  | equal_CAssignOp CShrAssOp0 CShrAssOp0 = true
  | equal_CAssignOp CShlAssOp0 CShlAssOp0 = true
  | equal_CAssignOp CSubAssOp0 CSubAssOp0 = true
  | equal_CAssignOp CAddAssOp0 CAddAssOp0 = true
  | equal_CAssignOp CRmdAssOp0 CRmdAssOp0 = true
  | equal_CAssignOp CDivAssOp0 CDivAssOp0 = true
  | equal_CAssignOp CMulAssOp0 CMulAssOp0 = true
  | equal_CAssignOp CAssignOp0 CAssignOp0 = true;

fun statement_of_expression_CAssign_fun e =
  (case e of CComma0 (_, _) => false | CAssign0 (_, _, _, _) => false | CCond0 (_, _, _, _) => false | CBinary0 (_, _, _, _) => false | CCast0 (_, _, _) => false | CUnary0 (_, _, _) => false | CSizeofExpr0 (_, _) => false
    | CSizeofType0 (_, _) => false | CAlignofExpr0 (_, _) => false | CAlignofType0 (_, _) => false | CComplexReal0 (_, _) => false | CComplexImag0 (_, _) => false | CIndex0 (_, _, _) => false | CCall0 (_, _, _) => false
    | CMember0 (_, _, true, _) => false | CMember0 (ea, _, false, _) => statement_of_expression_CAssign_fun ea | CVar0 (_, _) => true | CConst0 _ => false | CCompoundLit0 (_, _, _) => false | CGenericSelection0 (_, _, _) => false
    | CStatExpr0 (_, _) => false | CLabAddrExpr0 (_, _) => false | CBuiltinExpr0 _ => false);

fun binoptype_of_CAssignOp x =
  (fn a => (case a of CAssignOp0 => NONE | CMulAssOp0 => SOME Times | CDivAssOp0 => SOME Divides | CRmdAssOp0 => SOME Modulus | CAddAssOp0 => SOME Plus | CSubAssOp0 => SOME Minus | CShlAssOp0 => SOME LShift | CShrAssOp0 => SOME RShift
             | CAndAssOp0 => SOME BitwiseAnd | CXorAssOp0 => SOME BitwiseXOr | COrAssOp0 => SOME BitwiseOr))
    x;

fun statement_of_expression_CAssign ass_op e1 e2 =
  let
    val e1a = stmt_out_of_expra e1;
    val e2a = stmt_out_of_expra e2;
  in
    (case (case e2a of CComma0 (_, _) => NONE | CAssign0 (_, _, _, _) => NONE | CCond0 (_, _, _, _) => NONE | CBinary0 (_, _, _, _) => NONE | CCast0 (_, _, _) => NONE | CUnary0 (_, _, _) => NONE | CSizeofExpr0 (_, _) => NONE
            | CSizeofType0 (_, _) => NONE | CAlignofExpr0 (_, _) => NONE | CAlignofType0 (_, _) => NONE | CComplexReal0 (_, _) => NONE | CComplexImag0 (_, _) => NONE | CIndex0 (_, _, _) => NONE
            | CCall0 (f, l_arg, _) => (if statement_of_expression_CAssign_fun e1a andalso equal_CAssignOp ass_op CAssignOp0 then SOME (AssignFnCall (SOME (expression e1a), expression f, mapa expression l_arg)) else NONE)
            | CMember0 (_, _, _, _) => NONE | CVar0 (_, _) => NONE | CConst0 _ => NONE | CCompoundLit0 (_, _, _) => NONE | CGenericSelection0 (_, _, _) => NONE | CStatExpr0 (_, _) => NONE | CLabAddrExpr0 (_, _) => NONE
            | CBuiltinExpr0 _ => NONE)
      of NONE => let
                   val e1b = expression e1a;
                   val e2b = expression e2a;
                 in
                   Assign (e1b, (case binoptype_of_CAssignOp ass_op of NONE => e2b | SOME ass_opa => ebogwrap (BinOp (ass_opa, e1b, e2b))))
                 end
      | SOME s => s)
  end;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun expr_int i = ebogwrap (Constant (bogwrap (NUMCONST (i, SS_base (ST ""), DEC))));

fun statement_node_of_expression e =
  let
    val var_const =
      (fn l => (if list_all (fn a => (case a of CComma0 (_, _) => false | CAssign0 (_, _, _, _) => false | CCond0 (_, _, _, _) => false | CBinary0 (_, _, _, _) => false | CCast0 (_, _, _) => false | CUnary0 (_, _, _) => false
                                       | CSizeofExpr0 (_, _) => false | CSizeofType0 (_, _) => false | CAlignofExpr0 (_, _) => false | CAlignofType0 (_, _) => false | CComplexReal0 (_, _) => false | CComplexImag0 (_, _) => false
                                       | CIndex0 (_, _, _) => false | CCall0 (_, _, _) => false | CMember0 (_, _, _, _) => false | CVar0 (_, _) => true | CConst0 _ => true | CCompoundLit0 (_, _, _) => false
                                       | CGenericSelection0 (_, _, _) => false | CStatExpr0 (_, _) => false | CLabAddrExpr0 (_, _) => false | CBuiltinExpr0 _ => false))
                     l
                 then EmptyStmt else errora (SS_base (ST "not yet supported"))));
  in
    (fn a => (case a of CComma0 (l, _) => Block (mapa (BI_Stmt o sbogwrap o statement_node_of_expression) l) | CAssign0 (ass_op, e1, e2, _) => statement_of_expression_CAssign ass_op e1 e2 | CBinary0 (_, e1, e2, _) => var_const [e1, e2]
               | CCast0 (_, CComma0 (lista, aa), _) => var_const [CComma0 (lista, aa)] | CCast0 (_, CAssign0 (cAssignOp, cExpression1, cExpression2, aa), _) => var_const [CAssign0 (cAssignOp, cExpression1, cExpression2, aa)]
               | CCast0 (_, CCond0 (cExpression1, optiona, cExpression2, aa), _) => var_const [CCond0 (cExpression1, optiona, cExpression2, aa)]
               | CCast0 (_, CBinary0 (cBinaryOp, cExpression1, cExpression2, aa), _) => var_const [CBinary0 (cBinaryOp, cExpression1, cExpression2, aa)]
               | CCast0 (_, CCast0 (cDeclaration, cExpression, aa), _) => var_const [CCast0 (cDeclaration, cExpression, aa)] | CCast0 (_, CUnary0 (cUnaryOp, cExpression, aa), _) => var_const [CUnary0 (cUnaryOp, cExpression, aa)]
               | CCast0 (_, CSizeofExpr0 (cExpression, aa), _) => var_const [CSizeofExpr0 (cExpression, aa)] | CCast0 (_, CSizeofType0 (cDeclaration, aa), _) => var_const [CSizeofType0 (cDeclaration, aa)]
               | CCast0 (_, CAlignofExpr0 (cExpression, aa), _) => var_const [CAlignofExpr0 (cExpression, aa)] | CCast0 (_, CAlignofType0 (cDeclaration, aa), _) => var_const [CAlignofType0 (cDeclaration, aa)]
               | CCast0 (_, CComplexReal0 (cExpression, aa), _) => var_const [CComplexReal0 (cExpression, aa)] | CCast0 (_, CComplexImag0 (cExpression, aa), _) => var_const [CComplexImag0 (cExpression, aa)]
               | CCast0 (_, CIndex0 (cExpression1, cExpression2, aa), _) => var_const [CIndex0 (cExpression1, cExpression2, aa)]
               | CCast0 (_, CCall0 (f, l_arg, _), _) => AssignFnCall (NONE, expression (stmt_out_of_expra f), mapa (expression o stmt_out_of_expra) l_arg)
               | CCast0 (_, CMember0 (cExpression, ident, boola, aa), _) => var_const [CMember0 (cExpression, ident, boola, aa)] | CCast0 (_, CVar0 (ident, aa), _) => var_const [CVar0 (ident, aa)]
               | CCast0 (_, CConst0 cConstant, _) => var_const [CConst0 cConstant] | CCast0 (_, CCompoundLit0 (cDeclaration, lista, aa), _) => var_const [CCompoundLit0 (cDeclaration, lista, aa)]
               | CCast0 (_, CGenericSelection0 (cExpression, lista, aa), _) => var_const [CGenericSelection0 (cExpression, lista, aa)] | CCast0 (_, CStatExpr0 (cStatement, aa), _) => var_const [CStatExpr0 (cStatement, aa)]
               | CCast0 (_, CLabAddrExpr0 (ident, aa), _) => var_const [CLabAddrExpr0 (ident, aa)] | CCast0 (_, CBuiltinExpr0 cBuiltinThing, _) => var_const [CBuiltinExpr0 cBuiltinThing]
               | CUnary0 (ass_op, expr, _) => let
                                                val (pre_post, oper) = (case ass_op of CPreIncOp0 => (false, Plus) | CPreDecOp0 => (false, Minus) | CPostIncOp0 => (true, Plus) | CPostDecOp0 => (true, Minus));
                                                val expra = expression expr;
                                              in
                                                (if pre_post then Assign (expra, ebogwrap (BinOp (oper, expra, expr_int (1 : IntInf.int)))) else Assign (expra, ebogwrap (BinOp (oper, expra, expr_int (1 : IntInf.int)))))
                                              end
               | CCall0 (f, l_arg, _) => AssignFnCall (NONE, expression (stmt_out_of_expra f), mapa (expression o stmt_out_of_expra) l_arg)))
  end
    e;

fun filter_auxupd x =
  filter_gen (fn a => (case a of Invariant _ => NONE | Fnspeca _ => NONE | Relspeca _ => NONE | Modifies _ => NONE | Dont_translate => NONE | Auxupda aa => SOME aa | Ghostupda _ => NONE | Speca _ => NONE | End_spec _ => NONE
                        | Calls _ => NONE | Owned_by _ => NONE | OTHER _ => NONE))
    Auxupd x;

fun pos_of_CBuiltin x = (fn a => (case a of CBuiltinVaArg0 (_, _, pos) => pos | CBuiltinOffsetOf0 (_, _, pos) => pos)) x;

fun pos_of_CConst x = (fn a => (case a of CIntConst0 (_, pos) => pos | CCharConst0 (_, pos) => pos | CFloatConst0 (_, pos) => pos | CStrConst0 (_, pos) => pos)) x;

fun pos_of_CExpr x =
  (fn a => (case a of CComma0 (_, pos) => pos | CAssign0 (_, _, _, pos) => pos | CCond0 (_, _, _, pos) => pos | CBinary0 (_, _, _, pos) => pos | CCast0 (_, _, pos) => pos | CUnary0 (_, _, pos) => pos | CSizeofExpr0 (_, pos) => pos
             | CSizeofType0 (_, pos) => pos | CAlignofType0 (_, pos) => pos | CIndex0 (_, _, pos) => pos | CCall0 (_, _, pos) => pos | CMember0 (_, _, _, pos) => pos | CVar0 (_, pos) => pos | CConst0 aa => pos_of_CConst aa
             | CCompoundLit0 (_, _, pos) => pos | CStatExpr0 (_, pos) => pos | CBuiltinExpr0 aa => pos_of_CBuiltin aa))
    x;

fun statement_node_of_expressiona x =
  (fn a => (case a of None => (fn _ => EmptyStmt)
             | Some e => let
                           val stmt = statement_node_of_expression e;
                         in
                           (fn aa => (case aa of NONE => stmt
                                       | SOME (pos_stat, rbt) =>
                                         (case filter_auxupd (comment_interval rbt (p_last_of_NodeInfo (pos_of_CExpr e), p_first_of_NodeInfo pos_stat)) of NONE => stmt
                                           | SOME s2 => let
                                                          val f = (fn l1 => fn l2 => Block (l1 @ mapa (BI_Stmt o sbogwrap) l2));
                                                        in
                                                          (case stmt of Assign (expr1, expr2) => f [] [Assign (expr1, expr2), s2] | AssignFnCall (optiona, expr, lista) => f [] [AssignFnCall (optiona, expr, lista), s2]
                                                            | Chaos expr => f [] [Chaos expr, s2] | EmbFnCall (expr1, expr2, lista) => f [] [EmbFnCall (expr1, expr2, lista), s2] | Block l => f l [s2]
                                                            | While (expr, optiona, statement) => f [] [While (expr, optiona, statement), s2] | Trap (trappable, statement) => f [] [Trap (trappable, statement), s2]
                                                            | Return optiona => f [] [Return optiona, s2] | ReturnFnCall (expr, lista) => f [] [ReturnFnCall (expr, lista), s2] | Break => f [] [Break, s2]
                                                            | Continue => f [] [Continue, s2] | IfStmt (expr, statement1, statement2) => f [] [IfStmt (expr, statement1, statement2), s2]
                                                            | Switch (expr, lista) => f [] [Switch (expr, lista), s2] | EmptyStmt => f [] [EmptyStmt, s2] | Auxupd abr_string => f [] [Auxupd abr_string, s2]
                                                            | Ghostupd abr_string => f [] [Ghostupd abr_string, s2] | Spec prod => f [] [Spec prod, s2] | AsmStmt (boola, asmblock) => f [] [AsmStmt (boola, asmblock), s2]
                                                            | LocalInit expr => f [] [LocalInit expr, s2])
                                                        end)))
                         end))
    x;

fun remove_last_break s =
  (case s of CCompound0 (_, [], _) => NONE
    | CCompound0 (l0, x :: xs, a) =>
      (case (case rev (x :: xs)
              of [] => dropWhile (fn aa => (case aa of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                             | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                             | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                             | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                             | CNestedFunDef0 _ => false))
                         []
              | CBlockStmt0 aa :: l =>
                (case aa of CLabel0 (ident, cStatementa, listb, aaa) =>
                           dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                                 | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                                 | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                                 | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                                 | CNestedFunDef0 _ => false))
                             (CBlockStmt0 (CLabel0 (ident, cStatementa, listb, aaa)) :: l)
                  | CCase0 (cExpression, cStatementa, aaa) =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CCase0 (cExpression, cStatementa, aaa)) :: l)
                  | CCases0 (cExpression1, cExpression2, cStatementa, aaa) =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CCases0 (cExpression1, cExpression2, cStatementa, aaa)) :: l)
                  | CDefault0 (cStatementa, aaa) =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CDefault0 (cStatementa, aaa)) :: l)
                  | CExpr0 (optiona, aaa) =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CExpr0 (optiona, aaa)) :: l)
                  | CCompound0 (l0a, la, ab) => (case remove_last_break (CCompound0 (l0a, la, ab)) of NONE => l | SOME xa => CBlockStmt0 xa :: l)
                  | CIf0 (cExpression, cStatementa, optiona, aaa) =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CIf0 (cExpression, cStatementa, optiona, aaa)) :: l)
                  | CSwitch0 (cExpression, cStatementa, aaa) =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CSwitch0 (cExpression, cStatementa, aaa)) :: l)
                  | CWhile0 (cExpression, cStatementa, boola, aaa) =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CWhile0 (cExpression, cStatementa, boola, aaa)) :: l)
                  | CFor0 (either, option1, option2, cStatementa, aaa) =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CFor0 (either, option1, option2, cStatementa, aaa)) :: l)
                  | CGoto0 (ident, aaa) =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CGoto0 (ident, aaa)) :: l)
                  | CGotoPtr0 (cExpression, aaa) =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CGotoPtr0 (cExpression, aaa)) :: l)
                  | CCont0 aaa =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CCont0 aaa) :: l)
                  | CBreak0 aaa =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CBreak0 aaa) :: l)
                  | CReturn0 (optiona, aaa) =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CReturn0 (optiona, aaa)) :: l)
                  | CAsm0 (cAssemblyStatement, aaa) =>
                    dropWhile (fn ab => (case ab of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                          | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                          | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                          | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                          | CNestedFunDef0 _ => false))
                      (CBlockStmt0 (CAsm0 (cAssemblyStatement, aaa)) :: l))
              | CBlockDecl0 cDeclaration :: l =>
                dropWhile (fn aa => (case aa of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                      | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                      | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                      | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                      | CNestedFunDef0 _ => false))
                  (CBlockDecl0 cDeclaration :: l)
              | CNestedFunDef0 cFunctionDef :: l =>
                dropWhile (fn aa => (case aa of CBlockStmt0 (CLabel0 (_, _, _, _)) => false | CBlockStmt0 (CCase0 (_, _, _)) => false | CBlockStmt0 (CCases0 (_, _, _, _)) => false | CBlockStmt0 (CDefault0 (_, _)) => false
                                      | CBlockStmt0 (CExpr0 (_, _)) => false | CBlockStmt0 (CCompound0 (_, _, _)) => false | CBlockStmt0 (CIf0 (_, _, _, _)) => false | CBlockStmt0 (CSwitch0 (_, _, _)) => false
                                      | CBlockStmt0 (CWhile0 (_, _, _, _)) => false | CBlockStmt0 (CFor0 (_, _, _, _, _)) => false | CBlockStmt0 (CGoto0 (_, _)) => false | CBlockStmt0 (CGotoPtr0 (_, _)) => false
                                      | CBlockStmt0 (CCont0 _) => false | CBlockStmt0 (CBreak0 _) => true | CBlockStmt0 (CReturn0 (_, _)) => false | CBlockStmt0 (CAsm0 (_, _)) => false | CBlockDecl0 _ => false
                                      | CNestedFunDef0 _ => false))
                  (CNestedFunDef0 cFunctionDef :: l))
        of [] => NONE | aa :: lista => SOME (CCompound0 (l0, rev (aa :: lista), a)))
    | CBreak0 _ => NONE);

fun statement0_case l s =
  (case s of CLabel0 (_, _, _, _) => (false, (rev l, s)) | CCase0 (e, sa, _) => statement0_case (e :: l) sa | CCases0 (_, _, _, _) => (false, (rev l, s)) | CDefault0 (sa, _) => (true, (rev l, sa)) | CExpr0 (_, _) => (false, (rev l, s))
    | CCompound0 (_, _, _) => (false, (rev l, s)) | CIf0 (_, _, _, _) => (false, (rev l, s)) | CSwitch0 (_, _, _) => (false, (rev l, s)) | CWhile0 (_, _, _, _) => (false, (rev l, s)) | CFor0 (_, _, _, _, _) => (false, (rev l, s))
    | CGoto0 (_, _) => (false, (rev l, s)) | CGotoPtr0 (_, _) => (false, (rev l, s)) | CCont0 _ => (false, (rev l, s)) | CBreak0 _ => (false, (rev l, s)) | CReturn0 (_, _) => (false, (rev l, s)) | CAsm0 (_, _) => (false, (rev l, s)));

fun statement_Switch statement0 block_item_list0 expr l n_info =
  Trap (BreakT, sbogwrap (Switch (expression expr,
                                   let
                                     val (l_def, l_case) =
                                       app_rev (app_rev (app_rev (app_rev (app_rev l (mapa (fn CBlockStmt0 s => s)))
                                                                   (groupBy (fn _ => fn a =>
                                                                              (case a of CLabel0 (_, _, _, _) => true | CCase0 (_, _, _) => false | CCases0 (_, _, _, _) => true | CDefault0 (_, _) => false | CExpr0 (_, _) => true
                                                                                | CCompound0 (_, _, _) => true | CIf0 (_, _, _, _) => true | CSwitch0 (_, _, _) => true | CWhile0 (_, _, _, _) => true | CFor0 (_, _, _, _, _) => true
                                                                                | CGoto0 (_, _) => true | CGotoPtr0 (_, _) => true | CCont0 _ => true | CBreak0 _ => true | CReturn0 (_, _) => true | CAsm0 (_, _) => true))))
                                                          (fn la => foldr (fn x :: xs => fn (acc, pos2) =>
                                                                            let
                                                                              val pos1 = p_first_of_NodeInfo (pos_of_CStat x);
                                                                            in
                                                                              (map_prod (fn a => (case a of [] => [NONE] | aa :: lista => mapa (SOME o expression) (aa :: lista)))
                                                                                 (fn xa => (case remove_last_break (CCompound0 ([], mapa CBlockStmt0 (xa :: xs), n_info)) of NONE => []
                                                                                             | SOME (CCompound0 (_, lb, _)) => block_item_list0 lb (pos1, pos2)))
                                                                                 (case statement0_case [] x of (true, (_, s)) => ([], s) | (false, (lb, s)) => (lb, s)) ::
                                                                                 acc,
                                                                                pos1)
                                                                            end)
                                                                      la ([], p_last_of_NodeInfo n_info)))
                                                 fst)
                                         (partition (fn a => (case a of ([], _) => false | ([NONE], _) => true | (NONE :: _ :: _, _) => false | (SOME _ :: _, _) => false)));
                                   in
                                     l_case @ (if null l_def then [([NONE], [BI_Stmt (sbogwrap EmptyStmt)])] else l_def)
                                   end)));

fun filter_invariant x =
  filter_gen (fn a => (case a of Invariant aa => SOME aa | Fnspeca _ => NONE | Relspeca _ => NONE | Modifies _ => NONE | Dont_translate => NONE | Auxupda _ => NONE | Ghostupda _ => NONE | Speca _ => NONE | End_spec _ => NONE
                        | Calls _ => NONE | Owned_by _ => NONE | OTHER _ => NONE))
    bogwrap x;

fun statement_While expr =
  (fn (stat, pos_stat) => fn is_do => fn (pos, rbt) =>
    Trap (BreakT, sbogwrap let
                             val body = sbogwrap (Trap (ContinueT, stat));
                             val loop = While (expression (stmt_out_of_expra expr),
                                                filter_invariant (comment_interval rbt ((if is_do then p_first_of_NodeInfo pos else p_last_of_NodeInfo (pos_of_CExpr expr)), p_first_of_NodeInfo pos_stat)), body);
                           in
                             (if is_do then Block (mapa BI_Stmt [body, sbogwrap loop]) else loop)
                           end));

fun flattena a b = flatten [a, b];

fun map f l = rev (foldl (fn la => fn x => f x :: la) [] l);

fun replace_chars f s1 s s2 = flattena s1 (flattena (case s of NONE => SS_base (ST "") | SOME sa => flatten (map f (String.explode sa))) s2);

fun map_gena replace g = (fn a => (case a of ST s => replace (SS_base (ST "")) (SOME s) (SS_base (ST "")) | STa s => flatten (map g s)));

fun map_gen replace g e = (case e of SS_base a => map_gena replace g a | String_concatWith (abr, l) => String_concatWith (map_gen replace g abr, mapa (map_gen replace g) l));

fun replace_charsa f = map_gen (replace_chars f) f;

fun stringLiteral x = (fn CStrLit0 (CString0 (s, _), _) => replace_charsa (fn xa => (if ((xa : char) = #"\n") then SS_base (ST "\\n") else SS_base (STa [xa]))) s) x;

fun assemblyOperand x = mapa (fn CAsmOperand0 (o_i, s, e, _) => (ident_option o_i, (stringLiteral s, expression e))) x;

fun statement_For exp_decl o_expr2 o_expr3 =
  (fn (stat, pos_stat) => fn (pos, rbt) =>
    let
      val of_expr = (fn f => fn o_expr => mapa (BI_Stmt o sbogwrap) (f [statement_node_of_expressiona o_expr (SOME (pos_stat, rbt))]));
    in
      Block ((case exp_decl of Left a => of_expr id a | Right a => declaration (rbt, NONE) BI_Decl a) @
              [BI_Stmt (sbogwrap (Trap (BreakT, sbogwrap (While ((case o_expr2 of None => expr_int (1 : IntInf.int) | Some expr => expression (stmt_out_of_expra expr)),
                                                                  filter_invariant
                                                                    (comment_interval rbt
                                                                      (let
                                                                         val p_last = p_last_of_NodeInfo o pos_of_CExpr;
                                                                       in
                                                                         (case o_expr3
                                                                           of None => (case o_expr2
                                                                                        of None => (case exp_decl of Left a => (case a of None => p_first_of_NodeInfo pos | Some aa => p_last aa)
                                                                                                     | Right d => p_last_of_NodeInfo (pos_of_CDecl d))
                                                                                        | Some a => p_last a)
                                                                           | Some a => p_last a)
                                                                       end,
                                                                        p_first_of_NodeInfo pos_stat)),
                                                                  sbogwrap (Block (of_expr (fn a => Trap (ContinueT, stat) :: a) o_expr3)))))))])
    end);

fun statement_If statement0 expr stat1 o_stat2 = IfStmt (expression expr, statement0 stat1, (case o_stat2 of None => sbogwrap EmptyStmt | Some a => statement0 a));

fun group_spec_aux1 l x =
  (case x of [] => concat (rev l) | Inl xa :: xs => group_spec_aux1 (xa :: l) xs | Inr [Inl x1] :: xs => let
                                                                                                           val Inl l_body :: Inr [Inr x2] :: xsa = xs;
                                                                                                         in
                                                                                                           group_spec_aux2 l x1 l_body x2 xsa
                                                                                                         end
    | Inr [Inl x1, Inr x2] :: xs => group_spec_aux2 l x1 [] x2 xs)
and group_spec_aux2 l x1 l_body x2 xs = group_spec_aux1 ([BI_Stmt (sbogwrap (Spec (x1, (mapa (fn BI_Stmt s => s) l_body, x2))))] :: l) xs;

fun group_spec l =
  app_rev (app_rev (app_rev l (groupBy (fn a => fn b => (case (a, b) of (Inl _, Inl _) => true | (Inl _, Inr _) => false | (Inr _, Inl _) => false | (Inr _, Inr _) => true))))
            (mapa (fn a => (case a of Inl x :: xs => Inl (x :: mapa (fn Inl xa => xa) xs) | Inr x :: xs => Inr (x :: mapa (fn Inr xa => xa) xs)))))
    (group_spec_aux1 []);

fun block_item_list0a rbt l pos = block_item_list0 rbt l (p_first_of_NodeInfo pos, p_last_of_NodeInfo pos)
and statement0 rbt s =
  (sbogwrap o (fn a => (case a of CLabel0 (_, _, _, _) => let
                                                            val _ = not_yet_supported (SS_base (ST "CLabel not yet supported (Break returned)"));
                                                          in
                                                            Break
                                                          end
                         | CExpr0 (e, _) => statement_node_of_expressiona e NONE | CCompound0 ([], l, pos) => Block (block_item_list0a rbt l pos)
                         | CIf0 (expr, stat1, o_stat2, _) => statement_If (statement0 rbt) (stmt_out_of_expra expr) stat1 o_stat2
                         | CSwitch0 (expr, CCompound0 ([], l, n_info), _) => statement_Switch (statement0 rbt) (block_item_list0 rbt) expr l n_info
                         | CWhile0 (expr, stat, is_do, pos) => statement_While expr (statement0 rbt stat, pos_of_CStat stat) is_do (pos, rbt)
                         | CFor0 (exp_decl, o_expr2, o_expr3, stat, pos) => statement_For exp_decl o_expr2 o_expr3 (statement0 rbt stat, pos_of_CStat stat) (pos, rbt)
                         | CGoto0 (_, _) => let
                                              val _ = not_yet_supported (SS_base (ST "CGoto not yet supported (Break returned)"));
                                            in
                                              Break
                                            end
                         | CCont0 _ => Continue | CBreak0 _ => Break | CReturn0 (None, _) => Return (map_option (expression o stmt_out_of_expra) None)
                         | CReturn0 (Some (CComma0 (lista, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CComma0 (lista, ab))))
                         | CReturn0 (Some (CAssign0 (cAssignOp, cExpression1, cExpression2, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CAssign0 (cAssignOp, cExpression1, cExpression2, ab))))
                         | CReturn0 (Some (CCond0 (cExpression1, optiona, cExpression2, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CCond0 (cExpression1, optiona, cExpression2, ab))))
                         | CReturn0 (Some (CBinary0 (cBinaryOp, cExpression1, cExpression2, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CBinary0 (cBinaryOp, cExpression1, cExpression2, ab))))
                         | CReturn0 (Some (CCast0 (cDeclaration, cExpression, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CCast0 (cDeclaration, cExpression, ab))))
                         | CReturn0 (Some (CUnary0 (cUnaryOp, cExpression, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CUnary0 (cUnaryOp, cExpression, ab))))
                         | CReturn0 (Some (CSizeofExpr0 (cExpression, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CSizeofExpr0 (cExpression, ab))))
                         | CReturn0 (Some (CSizeofType0 (cDeclaration, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CSizeofType0 (cDeclaration, ab))))
                         | CReturn0 (Some (CAlignofExpr0 (cExpression, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CAlignofExpr0 (cExpression, ab))))
                         | CReturn0 (Some (CAlignofType0 (cDeclaration, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CAlignofType0 (cDeclaration, ab))))
                         | CReturn0 (Some (CComplexReal0 (cExpression, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CComplexReal0 (cExpression, ab))))
                         | CReturn0 (Some (CComplexImag0 (cExpression, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CComplexImag0 (cExpression, ab))))
                         | CReturn0 (Some (CIndex0 (cExpression1, cExpression2, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CIndex0 (cExpression1, cExpression2, ab))))
                         | CReturn0 (Some (CCall0 (f, l_arg, _)), _) => ReturnFnCall (expression f, mapa expression l_arg)
                         | CReturn0 (Some (CMember0 (cExpression, identa, boola, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CMember0 (cExpression, identa, boola, ab))))
                         | CReturn0 (Some (CVar0 (identa, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CVar0 (identa, ab))))
                         | CReturn0 (Some (CConst0 cConstant), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CConst0 cConstant)))
                         | CReturn0 (Some (CCompoundLit0 (cDeclaration, lista, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CCompoundLit0 (cDeclaration, lista, ab))))
                         | CReturn0 (Some (CGenericSelection0 (cExpression, lista, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CGenericSelection0 (cExpression, lista, ab))))
                         | CReturn0 (Some (CStatExpr0 (cStatement, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CStatExpr0 (cStatement, ab))))
                         | CReturn0 (Some (CLabAddrExpr0 (identa, ab)), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CLabAddrExpr0 (identa, ab))))
                         | CReturn0 (Some (CBuiltinExpr0 cBuiltinThing), _) => Return (map_option (expression o stmt_out_of_expra) (Some (CBuiltinExpr0 cBuiltinThing)))
                         | CAsm0 (CAsmStmt0 (Some (CVolatQual0 _), sa, l1, l2, l3, _), _) => AsmStmt (true, Asmblock (stringLiteral sa, assemblyOperand l1, assemblyOperand l2, mapa stringLiteral l3)))))
    s
and block_item_list0 rbt l =
  (fn (pos1, pos2) =>
    app_rev (app_rev let
                       val (acc, pos1a) =
                         fold (fn x => fn (acc, pos1a) =>
                                let
                                  val n = pos_of_CBlockItem x;
                                in
                                  (mapa Inl (case x of CBlockStmt0 s => [BI_Stmt (statement0 rbt s)] | CBlockDecl0 a => declaration (rbt, NONE) BI_Decl a
                                              | CNestedFunDef0 _ => let
                                                                      val _ = not_yet_supported (SS_base (ST "CNestedFunDef not yet supported (empty list returned)"));
                                                                    in
                                                                      []
                                                                    end) ::
                                     filter_statement (comment_interval rbt (pos1a, p_first_of_NodeInfo n)) :: acc,
                                    p_last_of_NodeInfo n)
                                end)
                           l ([], pos1);
                     in
                       app_rev (filter_statement (comment_interval rbt (pos1a, pos2)) :: acc) rev
                     end
              concat)
      group_spec);

fun comp3 f g = (fn x => fn y => fn z => f (g x y z));

fun block_item_list x = comp3 bogwrap block_item_list0a x;

fun function_definition x =
  (fn (rbt, pos_init) => fn a =>
    (case a of CFunDef0 (_, CDeclr0 (None, _, _, _, _), _, _, _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CLabel0 (_, _, _, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CCase0 (_, _, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CCases0 (_, _, _, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CDefault0 (_, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CExpr0 (_, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (l_decl_spec, CDeclr0 (Some i, dDs_root, _, _, _), [], CCompound0 ([], l_stmt, pos_stmt), pos) =>
        let
          val CFunDeclr0 (Right (arg, _), _, _) :: dDs = dDs_root;
          val l_fnspec = attrs l_decl_spec dDs_root [] ((rbt, pos_init), p_first_of_NodeInfo pos);
          val rettype = let
                          val ret_ty = decl_spec_ty l_decl_spec;
                        in
                          (case dDs of [] => ret_ty | [CPtrDeclr0 (_, _)] => Ptr ret_ty)
                        end;
          val name = bogwrap (ident i);
        in
          (if list_ex (fn aa => (case aa of Fnspec _ => false | Relspec _ => false | Fn_modifies _ => false | Didnt_translate => true | Gcc_attribs _ => false)) l_fnspec
            then Decl (bogwrap (ExtFnDecl (rettype, name, function_definition_params SOME arg, l_fnspec))) else FnDefn ((rettype, name), function_definition_params bogwrap arg, l_fnspec, block_item_list rbt l_stmt pos_stmt))
        end
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CCompound0 (_ :: _, _, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CIf0 (_, _, _, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CSwitch0 (_, _, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CWhile0 (_, _, _, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CFor0 (_, _, _, _, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CGoto0 (_, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CGotoPtr0 (_, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CCont0 _, _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CBreak0 _, _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CReturn0 (_, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), [], CAsm0 (_, _), _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))
      | CFunDef0 (_, CDeclr0 (Some _, _, _, _, _), _ :: _, _, _) => errora (SS_base (ST "Not yet covered: This case means the parsing has actually visited the 'function_declarator_old' branch, see Parser.y ."))))
    x;

fun external_declaration pos_init =
  (fn a => (case a of CDeclExt0 aa => declaration pos_init Decl aa | CFDefExt0 f => [function_definition pos_init f]
             | CAsmExt0 (_, _) => let
                                    val _ = not_yet_supported (SS_base (ST "Assembly declaration not yet supported (empty list returned)"));
                                  in
                                    []
                                  end));

fun pos_of_CExtDecl x = (fn a => (case a of CDeclExt0 aa => pos_of_CDecl aa | CFDefExt0 aa => pos_of_CFunDef aa | CAsmExt0 (_, pos) => pos)) x;

fun mapb A_ f = bulkload A_ o mapa (fn (k, v) => (k, f k v)) o entries;

fun translation_unit x =
  (fn (CTranslUnit0 (l, pos), (l_comm, _)) =>
    let
      val (l_comma, rbt) =
        (case current_parsing_style
          of Style_Haskell =>
            (mapa (fn Comment (Position0 (pp, ff, ll, cc), ss, fmt) => Comment (Position0 (pp, (if equal_abr_stringa ff (SS_base (ST "")) then let
                           val (Position0 (_, ffa, _, _), _) = p_first_of_NodeInfo pos;
                         in
                           ffa
                         end
                                                                                                 else ff),
                                                                                            ll, cc),
                                                                                 ss, fmt))
               l_comm,
              app_rev (fold (fn Comment (Position0 (_, ff, ll, cc), ss, _) => fn rbt =>
                              let
                                val k = (ff, ll);
                              in
                                insert (equal_prod equal_abr_string equal_integer) k
                                  let
                                    val rbta = (case lookupa (equal_prod equal_abr_string equal_integer) rbt k of NONE => emptya | SOME rbta => rbta);
                                  in
                                    (case lookupa equal_integer rbta cc of NONE => insert equal_integer cc ss rbta | SOME ssa => (if equal_abr_stringa ss ssa then rbta else errora (SS_base (ST "encountered different comments"))))
                                  end
                                  rbt
                              end)
                        l_comm emptya)
                (mapb (equal_prod equal_abr_string equal_integer) (fn _ => mapa (map_prod id (integer_of_nat o length)) o entries)))
          | Style_ML => (l_comm, emptya));
      val (_, (_, la)) =
        fold (fn fna => fn (pos1, (l_commb, acc)) => let
                                                       val pos2 = p_last_of_NodeInfo (pos_of_CExtDecl fna);
                                                       val f_take = (fn Comment (posa, _, _) => pos_in_interval rbt (pos1, pos2) posa);
                                                       val (l_take, l_drop) = partition f_take l_commb;
                                                     in
                                                       (pos2, (l_drop, external_declaration ((l_take, rbt), SOME pos1) fna :: acc))
                                                     end)
          l ((Position0 ((0 : IntInf.int), SS_base (ST ""), (1 : IntInf.int), (1 : IntInf.int)), (1 : IntInf.int)), (l_comma, []));
    in
      concat (rev la)
    end)
    x;

fun main x = translation_unit x;

fun cIf x = (fn a => fn b => fn c => CIf0 (x, a, b, c));

fun cAsm x = (fn a => CAsm0 (x, a));

fun cFor x = (fn a => fn b => fn c => fn d => CFor0 (x, a, b, c, d));

fun cVar x = (fn a => CVar0 (x, a));

fun name x = Name0 x;

fun cAttr x = (fn a => fn b => CAttr0 (x, a, b));

fun cAuto x = CAuto0 x;

fun cCall x = (fn a => fn b => CCall0 (x, a, b));

fun cCase x = (fn a => fn b => CCase0 (x, a, b));

fun cCast x = (fn a => fn b => CCast0 (x, a, b));

fun cChar x = (fn a => CChar0 (x, a));

fun cCond x = (fn a => fn b => fn c => CCond0 (x, a, b, c));

fun cCont x = CCont0 x;

fun cDecl x = (fn a => fn b => CDecl0 (x, a, b));

fun cEnum x = (fn a => fn b => fn c => CEnum0 (x, a, b, c));

val cEqOp : cBinaryOp = CEqOp0;

fun cExpr x = (fn a => CExpr0 (x, a));

fun cGoto x = (fn a => CGoto0 (x, a));

val cGrOp : cBinaryOp = CGrOp0;

val cLeOp : cBinaryOp = CLeOp0;

val cOrOp : cBinaryOp = COrOp0;

fun flags x = Flags0 x;

fun identc x = (fn a => fn b => Ident0 (x, a, b));

val cAddOp : cBinaryOp = CAddOp0;

val cAdrOp : cUnaryOp = CAdrOp0;

val cAndOp : cBinaryOp = CAndOp0;

fun cBreak x = CBreak0 x;

fun cCases x = (fn a => fn b => fn c => CCases0 (x, a, b, c));

fun cChars x = (fn a => CChars0 (x, a));

fun cComma x = (fn a => CComma0 (x, a));

fun cConst x = CConst0 x;

fun cDeclr x = (fn a => fn b => fn c => fn d => CDeclr0 (x, a, b, c, d));

val cDivOp : cBinaryOp = CDivOp0;

fun cFloat x = CFloat0 x;

val cGeqOp : cBinaryOp = CGeqOp0;

val cIndOp : cUnaryOp = CIndOp0;

fun cIndex x = (fn a => fn b => CIndex0 (x, a, b));

fun cLabel x = (fn a => fn b => fn c => CLabel0 (x, a, b, c));

val cLeqOp : cBinaryOp = CLeqOp0;

val cLndOp : cBinaryOp = CLndOp0;

val cLorOp : cBinaryOp = CLorOp0;

val cMinOp : cUnaryOp = CMinOp0;

val cMulOp : cBinaryOp = CMulOp0;

val cNegOp : cUnaryOp = CNegOp0;

val cNeqOp : cBinaryOp = CNeqOp0;

val cRmdOp : cBinaryOp = CRmdOp0;

val cShlOp : cBinaryOp = CShlOp0;

val cShrOp : cBinaryOp = CShrOp0;

val cSubOp : cBinaryOp = CSubOp0;

fun cUnary x = (fn a => fn b => CUnary0 (x, a, b));

fun cWhile x = (fn a => fn b => fn c => CWhile0 (x, a, b, c));

val cXorOp : cBinaryOp = CXorOp0;

fun cAsmExt x = (fn a => CAsmExt0 (x, a));

fun cAssign x = (fn a => fn b => fn c => CAssign0 (x, a, b, c));

fun cBinary x = (fn a => fn b => fn c => CBinary0 (x, a, b, c));

val cCompOp : cUnaryOp = CCompOp0;

fun cExtern x = CExtern0 x;

fun cFunDef x = (fn a => fn b => fn c => fn d => CFunDef0 (x, a, b, c, d));

fun cMember x = (fn a => fn b => fn c => CMember0 (x, a, b, c));

val cPlusOp : cUnaryOp = CPlusOp0;

fun cReturn x = (fn a => CReturn0 (x, a));

fun cSUType x = (fn a => CSUType0 (x, a));

fun cStatic x = CStatic0 x;

fun cStrLit x = (fn a => CStrLit0 (x, a));

fun cString x = (fn a => CString0 (x, a));

fun cStruct x = (fn a => fn b => fn c => fn d => CStruct0 (x, a, b, c, d));

fun cSwitch x = (fn a => fn b => CSwitch0 (x, a, b));

fun cThread x = CThread0 x;

val decRepr : cIntRepr = DecRepr0;

val hexRepr : cIntRepr = HexRepr0;

fun onlyPos x = (fn a => OnlyPos0 (x, a));

fun head (Asmblock (x1, x2, x3, x4)) = x1;

fun mod1 (Asmblock (x1, x2, x3, x4)) = x2;

fun mod2 (Asmblock (x1, x2, x3, x4)) = x3;

fun mod3 (Asmblock (x1, x2, x3, x4)) = x4;

fun map_Region_Wrap f (Tb (x1, x2)) = Tb (f x1, x2);

fun map_ctype f (Signed x1) = Signed x1
  | map_ctype f (Unsigned x2) = Unsigned x2
  | map_ctype f Bool = Bool
  | map_ctype f PlainChar = PlainChar
  | map_ctype f (StructTy x5) = StructTy x5
  | map_ctype f (UnionTy x6) = UnionTy x6
  | map_ctype f (EnumTy x7) = EnumTy x7
  | map_ctype f (Ptr x8) = Ptr (map_ctype f x8)
  | map_ctype f (Array (x91, x92)) = Array (map_ctype f x91, map_optiona f x92)
  | map_ctype f (Bitfield (x101, x102)) = Bitfield (x101, f x102)
  | map_ctype f (Identa x11) = Identa x11
  | map_ctype f (Function (x121, x122)) = Function (map_ctype f x121, mapa (map_ctype f) x122)
  | map_ctype f Void = Void;

fun rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (E x2) =
  f2 (map_Region_Wrap (fn expr_node => (expr_node, rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 expr_node)) x2)
and rec_designator f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (DesignE x41) = f41 x41 (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x41)
  | rec_designator f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (DesignFld x42) = f42 x42
and rec_initializer f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (InitE x31) = f31 x31 (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x31)
  | rec_initializer f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (InitList x32) =
    f32 (mapa (map_prod (mapa (fn designator => (designator, rec_designator f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 designator)))
                (fn initializer => (initializer, rec_initializer f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 initializer)))
          x32)
and rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (BinOp (x111, x112, x113)) =
  f11 x111 x112 x113 (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x112) (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x113)
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (UnOp (x121, x122)) =
    f12 x121 x122 (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x122)
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (CondExp (x131, x132, x133)) =
    f13 x131 x132 x133 (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x131) (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x132)
      (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x133)
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (Constant x14) = f14 x14
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (Var (x151, x152)) = f15 x151 x152
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (StructDot (x161, x162)) =
    f16 x161 x162 (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x161)
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (ArrayDeref (x171, x172)) =
    f17 x171 x172 (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x171) (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x172)
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (Deref x18) = f18 x18 (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x18)
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (TypeCast (x191, x192)) =
    f19 (map_Region_Wrap (map_ctype (fn expr => (expr, rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 expr))) x191) x192
      (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x192)
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (Sizeof x110) = f110 x110 (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x110)
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (SizeofTy x111a) =
    f111 (map_Region_Wrap (map_ctype (fn expr => (expr, rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 expr))) x111a)
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (EFnCall (x1121, x1122)) =
    f112 x1121 (mapa (fn expr => (expr, rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 expr)) x1122)
      (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x1121)
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (CompLiteral (x1131, x1132)) =
    f113 (map_ctype (fn expr => (expr, rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 expr)) x1131)
      (mapa (map_prod (mapa (fn designator => (designator, rec_designator f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 designator)))
              (fn initializer => (initializer, rec_initializer f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 initializer)))
        x1132)
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (Arbitrary x114) =
    f114 (map_ctype (fn expr => (expr, rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 expr)) x114)
  | rec_expr_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 (MKBOOL x115) = f115 x115 (rec_expr f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f2 f31 f32 f41 f42 x115);

fun cArrSize x = (fn a => CArrSize0 (x, a));

fun cAsmStmt x = (fn a => fn b => fn c => fn d => fn e => CAsmStmt0 (x, a, b, c, d, e));

fun cDeclExt x = CDeclExt0 x;

fun cDefault x = (fn a => CDefault0 (x, a));

fun cFDefExt x = CFDefExt0 x;

fun cFunSpec x = CFunSpec0 x;

fun cGotoPtr x = (fn a => CGotoPtr0 (x, a));

fun cIntType x = CIntType0 x;

fun cInteger x = (fn a => fn b => CInteger0 (x, a, b));

val cOrAssOp : cAssignOp = COrAssOp0;

fun cTypeDef x = (fn a => CTypeDef0 (x, a));

fun cTypedef x = CTypedef0 x;

val flagImag : cIntFlag = FlagImag0;

val flagLong : cIntFlag = FlagLong0;

fun namedRef x = NamedRef0 x;

fun nodeInfo x = (fn a => fn b => NodeInfo0 (x, a, b));

fun position x = (fn a => fn b => fn c => Position0 (x, a, b, c));

val cAddAssOp : cAssignOp = CAddAssOp0;

val cAndAssOp : cAssignOp = CAndAssOp0;

fun cArrDeclr x = (fn a => fn b => CArrDeclr0 (x, a, b));

fun cArrDesig x = (fn a => CArrDesig0 (x, a));

val cAssignOp : cAssignOp = CAssignOp0;

fun cAttrQual x = CAttrQual0 x;

fun cBoolType x = CBoolType0 x;

fun cCharType x = CCharType0 x;

fun cCompound x = (fn a => fn b => CCompound0 (x, a, b));

val cDivAssOp : cAssignOp = CDivAssOp0;

fun cEnumType x = (fn a => CEnumType0 (x, a));

fun cFunDeclr x = (fn a => fn b => CFunDeclr0 (x, a, b));

fun cInitExpr x = (fn a => CInitExpr0 (x, a));

fun cInitList x = (fn a => CInitList0 (x, a));

fun cIntConst x = (fn a => CIntConst0 (x, a));

fun cLongType x = CLongType0 x;

val cMulAssOp : cAssignOp = CMulAssOp0;

val cPreDecOp : cUnaryOp = CPreDecOp0;

val cPreIncOp : cUnaryOp = CPreIncOp0;

fun cPtrDeclr x = (fn a => CPtrDeclr0 (x, a));

fun cRegister x = CRegister0 x;

val cRmdAssOp : cAssignOp = CRmdAssOp0;

val cShlAssOp : cAssignOp = CShlAssOp0;

val cShrAssOp : cAssignOp = CShrAssOp0;

fun cStatExpr x = (fn a => CStatExpr0 (x, a));

fun cStrConst x = (fn a => CStrConst0 (x, a));

val cSubAssOp : cAssignOp = CSubAssOp0;

fun cTypeQual x = CTypeQual0 x;

fun cTypeSpec x = CTypeSpec0 x;

val cUnionTag : cStructTag = CUnionTag0;

fun cVoidType x = CVoidType0 x;

val cXorAssOp : cAssignOp = CXorAssOp0;

val octalRepr : cIntRepr = OctalRepr0;

fun rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 (Signed x1) = f1 x1
  | rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 (Unsigned x2) = f2 x2
  | rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 Bool = f3
  | rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 PlainChar = f4
  | rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 (StructTy x5) = f5 x5
  | rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 (UnionTy x6) = f6 x6
  | rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 (EnumTy x7) = f7 x7
  | rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 (Ptr x8) = f8 x8 (rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 x8)
  | rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 (Array (x91, x92)) = f9 x91 x92 (rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 x91)
  | rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 (Bitfield (x101, x102)) = f10 x101 x102
  | rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 (Identa x11) = f11 x11
  | rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 (Function (x121, x122)) =
    f12 x121 (mapa (fn ctype => (ctype, rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 ctype)) x122) (rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 x121)
  | rec_ctype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 Void = f13;

fun cAlignSpec x = CAlignSpec0 x;

fun cBlockDecl x = CBlockDecl0 x;

fun cBlockStmt x = CBlockStmt0 x;

fun cCharConst x = (fn a => CCharConst0 (x, a));

fun cConstQual x = CConstQual0 x;

fun cFloatType x = CFloatType0 x;

fun cNoArrSize x = CNoArrSize0 x;

val cPostDecOp : cUnaryOp = CPostDecOp0;

val cPostIncOp : cUnaryOp = CPostIncOp0;

fun cRestrQual x = CRestrQual0 x;

fun cShortType x = CShortType0 x;

val cStructTag : cStructTag = CStructTag0;

fun cUnsigType x = CUnsigType0 x;

fun cVolatQual x = CVolatQual0 x;

val noPosition : position = NoPosition0;

fun cAsmOperand x = (fn a => fn b => fn c => CAsmOperand0 (x, a, b, c));

fun cAtomicQual x = CAtomicQual0 x;

fun cAtomicType x = (fn a => CAtomicType0 (x, a));

fun cDoubleType x = CDoubleType0 x;

fun cFloatConst x = (fn a => CFloatConst0 (x, a));

fun cInlineQual x = CInlineQual0 x;

fun cInt128Type x = CInt128Type0 x;

fun cRangeDesig x = (fn a => fn b => CRangeDesig0 (x, a, b));

fun cSignedType x = CSignedType0 x;

fun cSizeofExpr x = (fn a => CSizeofExpr0 (x, a));

fun cSizeofType x = (fn a => CSizeofType0 (x, a));

fun cTranslUnit x = (fn a => CTranslUnit0 (x, a));

fun cTypeOfExpr x = (fn a => CTypeOfExpr0 (x, a));

fun cTypeOfType x = (fn a => CTypeOfType0 (x, a));

fun rec_Region f1 f2 Bogus = f1
  | rec_Region f1 f2 (T (x21, x22)) = f2 x21 x22;

fun rec_fnspec f1 f2 f3 f4 f5 (Fnspec x1) = f1 x1
  | rec_fnspec f1 f2 f3 f4 f5 (Relspec x2) = f2 x2
  | rec_fnspec f1 f2 f3 f4 f5 (Fn_modifies x3) = f3 x3
  | rec_fnspec f1 f2 f3 f4 f5 Didnt_translate = f4
  | rec_fnspec f1 f2 f3 f4 f5 (Gcc_attribs x5) = f5 x5;

fun anonymousRef x = AnonymousRef0 x;

fun cAlignAsExpr x = (fn a => CAlignAsExpr0 (x, a));

fun cAlignAsType x = (fn a => CAlignAsType0 (x, a));

fun cAlignofExpr x = (fn a => CAlignofExpr0 (x, a));

fun cAlignofType x = (fn a => CAlignofType0 (x, a));

fun cBuiltinExpr x = CBuiltinExpr0 x;

fun cComplexImag x = (fn a => CComplexImag0 (x, a));

fun cComplexReal x = (fn a => CComplexReal0 (x, a));

fun cComplexType x = CComplexType0 x;

fun cCompoundLit x = (fn a => fn b => CCompoundLit0 (x, a, b));

fun cLabAddrExpr x = (fn a => CLabAddrExpr0 (x, a));

fun cMemberDesig x = (fn a => CMemberDesig0 (x, a));

fun cNonnullQual x = CNonnullQual0 x;

fun cStorageSpec x = CStorageSpec0 x;

val flagLongLong : cIntFlag = FlagLongLong0;

val flagUnsigned : cIntFlag = FlagUnsigned0;

fun cBuiltinVaArg x = (fn a => fn b => CBuiltinVaArg0 (x, a, b));

fun cNestedFunDef x = CNestedFunDef0 x;

fun cNoreturnQual x = CNoreturnQual0 x;

fun cNullableQual x = CNullableQual0 x;

fun cStaticAssert x = (fn a => fn b => CStaticAssert0 (x, a, b));

fun clangCVersion x = ClangCVersion0 x;

val builtinPosition : position = BuiltinPosition0;

fun rec_ext_decl f1 f2 (FnDefn (x11, x12, x13, x14)) = f1 x11 x12 x13 x14
  | rec_ext_decl f1 f2 (Decl x2) = f2 x2;

fun rec_unoptype f1 f2 f3 f4 Negate = f1
  | rec_unoptype f1 f2 f3 f4 Not = f2
  | rec_unoptype f1 f2 f3 f4 Addr = f3
  | rec_unoptype f1 f2 f3 f4 BitNegate = f4;

fun cBuiltinOffsetOf x = (fn a => fn b => CBuiltinOffsetOf0 (x, a, b));

val internalPosition : position = InternalPosition0;

fun cGenericSelection x = (fn a => fn b => CGenericSelection0 (x, a, b));

fun rec_SourcePos f (Ta (x1, x2, x3)) = f x1 x2 x3;

fun rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 LogOr = f1
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 LogAnd = f2
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 Equals = f3
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 NotEquals = f4
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 BitwiseAnd = f5
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 BitwiseOr = f6
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 BitwiseXOr = f7
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 Lt = f8
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 Gt = f9
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 Leq = f10
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 Geq = f11
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 Plus = f12
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 Minus = f13
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 Times = f14
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 Divides = f15
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 Modulus = f16
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 RShift = f17
  | rec_binoptype f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 LShift = f18;

fun rec_more_info f1 f2 f3 (MungedVar (x11, x12)) = f1 x11 x12
  | rec_more_info f1 f2 f3 EnumC = f2
  | rec_more_info f1 f2 f3 FunctionName = f3;

fun rec_statement f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (Stmt x2) =
  f2 (map_Region_Wrap (fn statement_node => (statement_node, rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 statement_node)) x2)
and rec_block_item f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (BI_Stmt x31) =
  f31 x31 (rec_statement f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 x31)
  | rec_block_item f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (BI_Decl x32) = f32 x32
and rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (Assign (x111, x112)) = f11 x111 x112
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (AssignFnCall (x121, x122, x123)) = f12 x121 x122 x123
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (Chaos x13) = f13 x13
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (EmbFnCall (x141, x142, x143)) = f14 x141 x142 x143
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (Block x15) =
    f15 (mapa (fn block_item => (block_item, rec_block_item f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 block_item)) x15)
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (While (x161, x162, x163)) =
    f16 x161 x162 x163 (rec_statement f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 x163)
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (Trap (x171, x172)) =
    f17 x171 x172 (rec_statement f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 x172)
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (Return x18) = f18 x18
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (ReturnFnCall (x191, x192)) = f19 x191 x192
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 Break = f110
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 Continue = f111
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (IfStmt (x1121, x1122, x1123)) =
    f112 x1121 x1122 x1123 (rec_statement f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 x1122)
      (rec_statement f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 x1123)
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (Switch (x1131, x1132)) =
    f113 x1131 (mapa (map_prod id (mapa (fn block_item => (block_item, rec_block_item f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 block_item)))) x1132)
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 EmptyStmt = f114
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (Auxupd x115) = f115 x115
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (Ghostupd x116) = f116 x116
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (Spec x117) =
    f117 (map_prod id (map_prod (mapa (fn statement => (statement, rec_statement f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 statement))) id) x117)
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (AsmStmt (x1181, x1182)) = f118 x1181 x1182
  | rec_statement_node f11 f12 f13 f14 f15 f16 f17 f18 f19 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f2 f31 f32 (LocalInit x119) = f119 x119;

fun rec_trappable f1 f2 BreakT = f1
  | rec_trappable f1 f2 ContinueT = f2;

fun rec_Region_Wrap f (Tb (x1, x2)) = f x1 x2;

fun rec_declaration f1 f2 f3 f4 f5 (VarDecl x1) = f1 x1
  | rec_declaration f1 f2 f3 f4 f5 (StructDecl (x21, x22)) = f2 x21 x22
  | rec_declaration f1 f2 f3 f4 f5 (TypeDecl x3) = f3 x3
  | rec_declaration f1 f2 f3 f4 f5 (ExtFnDecl (x41, x42, x43, x44)) = f4 x41 x42 x43 x44
  | rec_declaration f1 f2 f3 f4 f5 (EnumDecl (x51, x52)) = f5 x51 x52;

fun cBuiltinTypesCompatible x = (fn a => fn b => CBuiltinTypesCompatible0 (x, a, b));

fun rec_base_inttype f1 f2 f3 f4 f5 f6 f7 Char = f1
  | rec_base_inttype f1 f2 f3 f4 f5 f6 f7 Short = f2
  | rec_base_inttype f1 f2 f3 f4 f5 f6 f7 Int = f3
  | rec_base_inttype f1 f2 f3 f4 f5 f6 f7 Long = f4
  | rec_base_inttype f1 f2 f3 f4 f5 f6 f7 LongLong = f5
  | rec_base_inttype f1 f2 f3 f4 f5 f6 f7 Double = f6
  | rec_base_inttype f1 f2 f3 f4 f5 f6 f7 Float = f7;

fun rec_gcc_attribute f1 f2 f3 (GCC_AttribID x1) = f1 x1
  | rec_gcc_attribute f1 f2 f3 (GCC_AttribFn (x21, x22)) = f2 x21 x22
  | rec_gcc_attribute f1 f2 f3 (OWNED_BY x3) = f3 x3;

fun rec_storage_class f1 f2 f3 f4 f5 SC_EXTERN = f1
  | rec_storage_class f1 f2 f3 f4 f5 SC_STATIC = f2
  | rec_storage_class f1 f2 f3 f4 f5 SC_AUTO = f3
  | rec_storage_class f1 f2 f3 f4 f5 SC_REGISTER = f4
  | rec_storage_class f1 f2 f3 f4 f5 SC_THRD_LOCAL = f5;

fun rec_StringCvt_radix f1 f2 f3 f4 BIN = f1
  | rec_StringCvt_radix f1 f2 f3 f4 OCT = f2
  | rec_StringCvt_radix f1 f2 f3 f4 DEC = f3
  | rec_StringCvt_radix f1 f2 f3 f4 HEX = f4;

fun rec_Unsynchronized_ref f (Unsynchronized_ref x) = f x;

fun rec_literalconstant_node f1 f2 (NUMCONST (x11, x12, x13)) = f1 x11 x12 x13
  | rec_literalconstant_node f1 f2 (STRING_LIT x2) = f2 x2;

end; (*struct C_ast*)
