structure C_Grammar_Rule = 
struct
(*#line 1.2 "c_grammar_fun.grm"*)open C_Ast open C_Grammar_Rule_Lib

type start_happy = (unit, (unit, (unit, (unit, unit) either) either) either) either

fun start_happy4 (x : start_happy) = case x of Right (Right (Right (Left x))) => SOME x | _ => NONE
fun start_happy3 (x : start_happy) = case x of Right (Right (Left x)) => SOME x | _ => NONE
fun start_happy2 (x : start_happy) = case x of Right (Left x) => SOME x | _ => NONE
fun start_happy1 (x : start_happy) = case x of Left x => SOME x | _ => NONE


(*#line 4818.1 "c_grammar_fun.grm.sml"*)
datatype svalue0 = VOID' | ntVOID of unit | XOR_ASSIGN of  (unit) | WHILE of  (unit) | VOLATILE of  (unit) | VOID of  (unit) | VARIABLE of  (unit) | UNSIGNED of  (unit) | UNION of  (unit) | TYPEDEF of  (unit) | TYPE of  (unit) | TILDE of  (unit) | THREAD_LOCAL of  (unit) | SWITCH of  (unit) | SUB_ASSIGN of  (unit) | STRUCT of  (unit) | STRING_LITERAL of  (unit) | STATIC_ASSERT of  (unit) | STATIC of  (unit) | STAR of  (unit) | SLASH of  (unit) | SIZEOF of  (unit) | SIGNED of  (unit) | SHORT of  (unit) | SEMICOLON of  (unit) | RPAREN of  (unit) | RIGHT_ASSIGN of  (unit) | RIGHT of  (unit) | RETURN of  (unit) | RESTRICT of  (unit) | REGISTER of  (unit) | RBRACK of  (unit) | RBRACE of  (unit) | QUESTION of  (unit) | PTR of  (unit) | PLUS of  (unit) | PERCENT of  (unit) | OR_ASSIGN of  (unit) | NORETURN of  (unit) | NEQ of  (unit) | NAME of  (string) | MUL_ASSIGN of  (unit) | MOD_ASSIGN of  (unit) | MINUS of  (unit) | LT of  (unit) | LPAREN of  (unit) | LONG of  (unit) | LEQ of  (unit) | LEFT_ASSIGN of  (unit) | LEFT of  (unit) | LBRACK of  (unit) | LBRACE of  (unit) | INT of  (unit) | INLINE of  (unit) | INC of  (unit) | IMAGINARY of  (unit) | IF of  (unit) | HAT of  (unit) | GT of  (unit) | GOTO of  (unit) | GEQ of  (unit) | GENERIC of  (unit) | FOR of  (unit) | FLOAT of  (unit) | EXTERN of  (unit) | EQEQ of  (unit) | EQ of  (unit) | EOF of  (unit) | ENUM of  (unit) | ELSE of  (unit) | ELLIPSIS of  (unit) | DOUBLE of  (unit) | DOT of  (unit) | DO of  (unit) | DIV_ASSIGN of  (unit) | DEFAULT of  (unit) | DEC of  (unit) | CONTINUE of  (unit) | CONSTANT of  (unit) | CONST of  (unit) | COMPLEX of  (unit) | COMMA of  (unit) | COLON of  (unit) | CHAR of  (unit) | CASE of  (unit) | BREAK of  (unit) | BOOL of  (unit) | BARBAR of  (unit) | BAR of  (unit) | BANG of  (unit) | AUTO of  (unit) | ATOMIC_LPAREN of  (unit) | ATOMIC of  (unit) | AND_ASSIGN of  (unit) | ANDAND of  (unit) | AND of  (unit) | ALIGNOF of  (unit) | ALIGNAS of  (unit) | ADD_ASSIGN of  (unit) | declaration_list of  (unit) | function_definition of  (unit) | function_definition_x31 of  (C_Grammar_Rule_Lib.c_context) | external_declaration of  (unit) | translation_unit of  (unit) | jump_statement of  (unit) | iteration_statement of  (unit) | selection_statement of  (unit) | expression_statement of  (unit) | block_item of  (unit) | block_item_list of  (unit) | compound_statement of  (unit) | labeled_statement of  (unit) | statement of  (unit) | static_assert_declaration of  (unit) | designator of  (unit) | designator_list of  (unit) | designation of  (unit) | initializer_list of  (unit) | c_initializer of  (unit) | direct_abstract_declarator of  (unit) | abstract_declarator of  (unit) | type_name of  (unit) | identifier_list of  (unit) | parameter_declaration of  (unit) | parameter_list of  (unit) | parameter_type_list of  (C_Grammar_Rule_Lib.c_context) | type_qualifier_list of  (unit) | pointer of  (unit) | direct_declarator of  (C_Grammar_Rule_Lib.c_declarator) | declarator of  (C_Grammar_Rule_Lib.c_declarator) | alignment_specifier of  (unit) | function_specifier of  (unit) | type_qualifier of  (unit) | atomic_type_specifier of  (unit) | enumeration_constant of  (string) | enumerator of  (unit) | enumerator_list of  (unit) | enum_specifier of  (unit) | struct_declarator of  (unit) | struct_declarator_list of  (unit) | specifier_qualifier_list of  (unit) | struct_declaration of  (unit) | struct_declaration_list of  (unit) | struct_or_union of  (unit) | struct_or_union_specifier of  (unit) | type_specifier_unique of  (unit) | type_specifier_nonunique of  (unit) | storage_class_specifier of  (unit) | init_declarator_declarator_varname_x5f of  (unit) | init_declarator_declarator_typedefname_x5f of  (unit) | init_declarator_list_declarator_varname_x5f of  (unit) | init_declarator_list_declarator_typedefname_x5f of  (unit) | declaration_specifiers_typedef of  (unit) | declaration_specifiers of  (unit) | declaration_specifier of  (unit) | declaration of  (unit) | constant_expression of  (unit) | expression of  (unit) | assignment_operator of  (unit) | assignment_expression of  (unit) | conditional_expression of  (unit) | logical_or_expression of  (unit) | logical_and_expression of  (unit) | inclusive_or_expression of  (unit) | exclusive_or_expression of  (unit) | and_expression of  (unit) | equality_expression of  (unit) | equality_operator of  (unit) | relational_expression of  (unit) | relational_operator of  (unit) | shift_expression of  (unit) | shift_operator of  (unit) | additive_expression of  (unit) | additive_operator of  (unit) | multiplicative_expression of  (unit) | multiplicative_operator of  (unit) | cast_expression of  (unit) | unary_operator of  (unit) | unary_expression of  (unit) | argument_expression_list of  (unit) | postfix_expression of  (unit) | generic_association of  (unit) | generic_assoc_list of  (unit) | generic_selection of  (unit) | primary_expression of  (unit) | declarator_typedefname of  (C_Grammar_Rule_Lib.c_declarator) | declarator_varname of  (C_Grammar_Rule_Lib.c_declarator) | scoped_statement_x5f of  (unit) | scoped_selection_statement_x5f of  (unit) | scoped_parameter_type_list_x5f of  (C_Grammar_Rule_Lib.c_context) | scoped_iteration_statement_x5f of  (unit) | scoped_compound_statement_x5f of  (unit) | save_context of  (C_Grammar_Rule_Lib.c_context) | general_identifier of  (string) | typedef_name_spec of  (unit) | var_name of  (string) | typedef_name of  (string) | list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f of  (unit) | list_eq1_eq1_TYPEDEF_type_specifier_unique_declaration_specifier_x5f of  (unit) | list_ge1_type_specifier_nonunique_declaration_specifier_x5f of  (unit) | list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f of  (unit) | list_eq1_type_specifier_unique_declaration_specifier_x5f of  (unit) | list_eq1_type_specifier_unique___anonymous_x5f_x30_x5f of  (unit) | list_eq1_TYPEDEF_declaration_specifier_x5f of  (unit) | list_declaration_specifier_x5f of  (unit) | list___anonymous_x5f_x31_x5f of  (unit) | list___anonymous_x5f_x30_x5f of  (unit) | option_type_qualifier_list_x5f of  (unit) | option_struct_declarator_list_x5f of  (unit) | option_scoped_parameter_type_list_x5f_x5f of  (unit) | option_pointer_x5f of  (unit) | option_init_declarator_list_declarator_varname_x5f_x5f of  (unit) | option_init_declarator_list_declarator_typedefname_x5f_x5f of  (unit) | option_identifier_list_x5f of  (unit) | option_general_identifier_x5f of  (unit) | option_expression_x5f of  (unit) | option_direct_abstract_declarator_x5f of  (unit) | option_designator_list_x5f of  (unit) | option_designation_x5f of  (unit) | option_declarator_x5f of  (unit) | option_declaration_list_x5f of  (unit) | option_block_item_list_x5f of  (unit) | option_assignment_expression_x5f of  (unit) | option_argument_expression_list_x5f of  (unit) | option_abstract_declarator_x5f of  (unit) | option___anonymous_x5f_x32_x5f of  (unit) | option_COMMA_x5f of  (unit) | start_happy of  ( ( unit, (unit, (unit, (unit, unit) either) either) either )  either)
fun find_list msg mk_name l =
  let val tab =
        fold (fn (name, occ) =>
               fold (fn name => fn (tab, nb) => (Inttab.update (nb, name) tab, nb + 1))
                    (if occ = 1 then [name]
                                else map_range (mk_name name) occ))
             l
             (Inttab.empty, 0)
        |> #1
  in
    fn i => case Inttab.lookup tab i of NONE => error msg | SOME name => name
  end
val type_reduce = find_list "reduce type not found" K [
  (" ( ( unit, (unit, (unit, (unit, unit) either) either) either )  either)", 4),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 3),
  (" (unit)", 3),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 3),
  (" (unit)", 2),
  (" (unit)", 4),
  (" (unit)", 3),
  (" (unit)", 3),
  (" (unit)", 4),
  (" (string)", 1),
  (" (string)", 1),
  (" (unit)", 1),
  (" (string)", 2),
  (" (C_Grammar_Rule_Lib.c_context)", 1),
  (" (unit)", 1),
  (" (unit)", 1),
  (" (C_Grammar_Rule_Lib.c_context)", 1),
  (" (unit)", 1),
  (" (unit)", 1),
  (" (C_Grammar_Rule_Lib.c_declarator)", 1),
  (" (C_Grammar_Rule_Lib.c_declarator)", 1),
  (" (unit)", 5),
  (" (unit)", 1),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 8),
  (" (unit)", 2),
  (" (unit)", 7),
  (" (unit)", 6),
  (" (unit)", 2),
  (" (unit)", 3),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 4),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 11),
  (" (unit)", 2),
  (" (unit)", 1),
  (" (unit)", 3),
  (" (unit)", 4),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 5),
  (" (unit)", 9),
  (" (unit)", 6),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (string)", 1),
  (" (unit)", 2),
  (" (unit)", 4),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (C_Grammar_Rule_Lib.c_declarator)", 2),
  (" (C_Grammar_Rule_Lib.c_declarator)", 8),
  (" (unit)", 1),
  (" (unit)", 1),
  (" (C_Grammar_Rule_Lib.c_context)", 1),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 1),
  (" (unit)", 3),
  (" (unit)", 8),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (unit)", 1),
  (" (unit)", 1),
  (" (unit)", 2),
  (" (unit)", 1),
  (" (unit)", 6),
  (" (unit)", 3),
  (" (unit)", 1),
  (" (unit)", 1),
  (" (unit)", 2),
  (" (unit)", 1),
  (" (unit)", 3),
  (" (unit)", 4),
  (" (unit)", 4),
  (" (unit)", 2),
  (" (unit)", 2),
  (" (C_Grammar_Rule_Lib.c_context)", 1),
  (" (unit)", 1),
  (" (unit)", 2),
  ("", 0)]
val string_reduce = find_list "reduce type not found" (fn name => fn occ => name ^ Int.toString (occ + 1)) [
  ("start_happy", 4),
  ("option_COMMA_x5f", 2),
  ("option___anonymous_x5f_x32_x5f", 2),
  ("option_abstract_declarator_x5f", 2),
  ("option_argument_expression_list_x5f", 2),
  ("option_assignment_expression_x5f", 2),
  ("option_block_item_list_x5f", 2),
  ("option_declaration_list_x5f", 2),
  ("option_declarator_x5f", 2),
  ("option_designation_x5f", 2),
  ("option_designator_list_x5f", 2),
  ("option_direct_abstract_declarator_x5f", 2),
  ("option_expression_x5f", 2),
  ("option_general_identifier_x5f", 2),
  ("option_identifier_list_x5f", 2),
  ("option_init_declarator_list_declarator_typedefname_x5f_x5f", 2),
  ("option_init_declarator_list_declarator_varname_x5f_x5f", 2),
  ("option_pointer_x5f", 2),
  ("option_scoped_parameter_type_list_x5f_x5f", 2),
  ("option_struct_declarator_list_x5f", 2),
  ("option_type_qualifier_list_x5f", 2),
  ("list___anonymous_x5f_x30_x5f", 3),
  ("list___anonymous_x5f_x31_x5f", 3),
  ("list_declaration_specifier_x5f", 2),
  ("list_eq1_TYPEDEF_declaration_specifier_x5f", 2),
  ("list_eq1_type_specifier_unique___anonymous_x5f_x30_x5f", 3),
  ("list_eq1_type_specifier_unique_declaration_specifier_x5f", 2),
  ("list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f", 4),
  ("list_ge1_type_specifier_nonunique_declaration_specifier_x5f", 3),
  ("list_eq1_eq1_TYPEDEF_type_specifier_unique_declaration_specifier_x5f", 3),
  ("list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f", 4),
  ("typedef_name", 1),
  ("var_name", 1),
  ("typedef_name_spec", 1),
  ("general_identifier", 2),
  ("save_context", 1),
  ("scoped_compound_statement_x5f", 1),
  ("scoped_iteration_statement_x5f", 1),
  ("scoped_parameter_type_list_x5f", 1),
  ("scoped_selection_statement_x5f", 1),
  ("scoped_statement_x5f", 1),
  ("declarator_varname", 1),
  ("declarator_typedefname", 1),
  ("primary_expression", 5),
  ("generic_selection", 1),
  ("generic_assoc_list", 2),
  ("generic_association", 2),
  ("postfix_expression", 8),
  ("argument_expression_list", 2),
  ("unary_expression", 7),
  ("unary_operator", 6),
  ("cast_expression", 2),
  ("multiplicative_operator", 3),
  ("multiplicative_expression", 2),
  ("additive_operator", 2),
  ("additive_expression", 2),
  ("shift_operator", 2),
  ("shift_expression", 2),
  ("relational_operator", 4),
  ("relational_expression", 2),
  ("equality_operator", 2),
  ("equality_expression", 2),
  ("and_expression", 2),
  ("exclusive_or_expression", 2),
  ("inclusive_or_expression", 2),
  ("logical_and_expression", 2),
  ("logical_or_expression", 2),
  ("conditional_expression", 2),
  ("assignment_expression", 2),
  ("assignment_operator", 11),
  ("expression", 2),
  ("constant_expression", 1),
  ("declaration", 3),
  ("declaration_specifier", 4),
  ("declaration_specifiers", 2),
  ("declaration_specifiers_typedef", 2),
  ("init_declarator_list_declarator_typedefname_x5f", 2),
  ("init_declarator_list_declarator_varname_x5f", 2),
  ("init_declarator_declarator_typedefname_x5f", 2),
  ("init_declarator_declarator_varname_x5f", 2),
  ("storage_class_specifier", 5),
  ("type_specifier_nonunique", 9),
  ("type_specifier_unique", 6),
  ("struct_or_union_specifier", 2),
  ("struct_or_union", 2),
  ("struct_declaration_list", 2),
  ("struct_declaration", 2),
  ("specifier_qualifier_list", 2),
  ("struct_declarator_list", 2),
  ("struct_declarator", 2),
  ("enum_specifier", 2),
  ("enumerator_list", 2),
  ("enumerator", 2),
  ("enumeration_constant", 1),
  ("atomic_type_specifier", 2),
  ("type_qualifier", 4),
  ("function_specifier", 2),
  ("alignment_specifier", 2),
  ("declarator", 2),
  ("direct_declarator", 8),
  ("pointer", 1),
  ("type_qualifier_list", 1),
  ("parameter_type_list", 1),
  ("parameter_list", 2),
  ("parameter_declaration", 2),
  ("identifier_list", 2),
  ("type_name", 1),
  ("abstract_declarator", 3),
  ("direct_abstract_declarator", 8),
  ("c_initializer", 2),
  ("initializer_list", 2),
  ("designation", 1),
  ("designator_list", 1),
  ("designator", 2),
  ("static_assert_declaration", 1),
  ("statement", 6),
  ("labeled_statement", 3),
  ("compound_statement", 1),
  ("block_item_list", 1),
  ("block_item", 2),
  ("expression_statement", 1),
  ("selection_statement", 3),
  ("iteration_statement", 4),
  ("jump_statement", 4),
  ("translation_unit", 2),
  ("external_declaration", 2),
  ("function_definition_x31", 1),
  ("function_definition", 1),
  ("declaration_list", 2),
  ("", 0)]
val reduce0 = fn start_happy x => x | _ => error "Only expecting start_happy"
val reduce1 = fn start_happy x => x | _ => error "Only expecting start_happy"
val reduce2 = fn start_happy x => x | _ => error "Only expecting start_happy"
val reduce3 = fn start_happy x => x | _ => error "Only expecting start_happy"
val reduce4 = fn option_COMMA_x5f x => x | _ => error "Only expecting option_COMMA_x5f"
val reduce5 = fn option_COMMA_x5f x => x | _ => error "Only expecting option_COMMA_x5f"
val reduce6 = fn option___anonymous_x5f_x32_x5f x => x | _ => error "Only expecting option___anonymous_x5f_x32_x5f"
val reduce7 = fn option___anonymous_x5f_x32_x5f x => x | _ => error "Only expecting option___anonymous_x5f_x32_x5f"
val reduce8 = fn option_abstract_declarator_x5f x => x | _ => error "Only expecting option_abstract_declarator_x5f"
val reduce9 = fn option_abstract_declarator_x5f x => x | _ => error "Only expecting option_abstract_declarator_x5f"
val reduce10 = fn option_argument_expression_list_x5f x => x | _ => error "Only expecting option_argument_expression_list_x5f"
val reduce11 = fn option_argument_expression_list_x5f x => x | _ => error "Only expecting option_argument_expression_list_x5f"
val reduce12 = fn option_assignment_expression_x5f x => x | _ => error "Only expecting option_assignment_expression_x5f"
val reduce13 = fn option_assignment_expression_x5f x => x | _ => error "Only expecting option_assignment_expression_x5f"
val reduce14 = fn option_block_item_list_x5f x => x | _ => error "Only expecting option_block_item_list_x5f"
val reduce15 = fn option_block_item_list_x5f x => x | _ => error "Only expecting option_block_item_list_x5f"
val reduce16 = fn option_declaration_list_x5f x => x | _ => error "Only expecting option_declaration_list_x5f"
val reduce17 = fn option_declaration_list_x5f x => x | _ => error "Only expecting option_declaration_list_x5f"
val reduce18 = fn option_declarator_x5f x => x | _ => error "Only expecting option_declarator_x5f"
val reduce19 = fn option_declarator_x5f x => x | _ => error "Only expecting option_declarator_x5f"
val reduce20 = fn option_designation_x5f x => x | _ => error "Only expecting option_designation_x5f"
val reduce21 = fn option_designation_x5f x => x | _ => error "Only expecting option_designation_x5f"
val reduce22 = fn option_designator_list_x5f x => x | _ => error "Only expecting option_designator_list_x5f"
val reduce23 = fn option_designator_list_x5f x => x | _ => error "Only expecting option_designator_list_x5f"
val reduce24 = fn option_direct_abstract_declarator_x5f x => x | _ => error "Only expecting option_direct_abstract_declarator_x5f"
val reduce25 = fn option_direct_abstract_declarator_x5f x => x | _ => error "Only expecting option_direct_abstract_declarator_x5f"
val reduce26 = fn option_expression_x5f x => x | _ => error "Only expecting option_expression_x5f"
val reduce27 = fn option_expression_x5f x => x | _ => error "Only expecting option_expression_x5f"
val reduce28 = fn option_general_identifier_x5f x => x | _ => error "Only expecting option_general_identifier_x5f"
val reduce29 = fn option_general_identifier_x5f x => x | _ => error "Only expecting option_general_identifier_x5f"
val reduce30 = fn option_identifier_list_x5f x => x | _ => error "Only expecting option_identifier_list_x5f"
val reduce31 = fn option_identifier_list_x5f x => x | _ => error "Only expecting option_identifier_list_x5f"
val reduce32 = fn option_init_declarator_list_declarator_typedefname_x5f_x5f x => x | _ => error "Only expecting option_init_declarator_list_declarator_typedefname_x5f_x5f"
val reduce33 = fn option_init_declarator_list_declarator_typedefname_x5f_x5f x => x | _ => error "Only expecting option_init_declarator_list_declarator_typedefname_x5f_x5f"
val reduce34 = fn option_init_declarator_list_declarator_varname_x5f_x5f x => x | _ => error "Only expecting option_init_declarator_list_declarator_varname_x5f_x5f"
val reduce35 = fn option_init_declarator_list_declarator_varname_x5f_x5f x => x | _ => error "Only expecting option_init_declarator_list_declarator_varname_x5f_x5f"
val reduce36 = fn option_pointer_x5f x => x | _ => error "Only expecting option_pointer_x5f"
val reduce37 = fn option_pointer_x5f x => x | _ => error "Only expecting option_pointer_x5f"
val reduce38 = fn option_scoped_parameter_type_list_x5f_x5f x => x | _ => error "Only expecting option_scoped_parameter_type_list_x5f_x5f"
val reduce39 = fn option_scoped_parameter_type_list_x5f_x5f x => x | _ => error "Only expecting option_scoped_parameter_type_list_x5f_x5f"
val reduce40 = fn option_struct_declarator_list_x5f x => x | _ => error "Only expecting option_struct_declarator_list_x5f"
val reduce41 = fn option_struct_declarator_list_x5f x => x | _ => error "Only expecting option_struct_declarator_list_x5f"
val reduce42 = fn option_type_qualifier_list_x5f x => x | _ => error "Only expecting option_type_qualifier_list_x5f"
val reduce43 = fn option_type_qualifier_list_x5f x => x | _ => error "Only expecting option_type_qualifier_list_x5f"
val reduce44 = fn list___anonymous_x5f_x30_x5f x => x | _ => error "Only expecting list___anonymous_x5f_x30_x5f"
val reduce45 = fn list___anonymous_x5f_x30_x5f x => x | _ => error "Only expecting list___anonymous_x5f_x30_x5f"
val reduce46 = fn list___anonymous_x5f_x30_x5f x => x | _ => error "Only expecting list___anonymous_x5f_x30_x5f"
val reduce47 = fn list___anonymous_x5f_x31_x5f x => x | _ => error "Only expecting list___anonymous_x5f_x31_x5f"
val reduce48 = fn list___anonymous_x5f_x31_x5f x => x | _ => error "Only expecting list___anonymous_x5f_x31_x5f"
val reduce49 = fn list___anonymous_x5f_x31_x5f x => x | _ => error "Only expecting list___anonymous_x5f_x31_x5f"
val reduce50 = fn list_declaration_specifier_x5f x => x | _ => error "Only expecting list_declaration_specifier_x5f"
val reduce51 = fn list_declaration_specifier_x5f x => x | _ => error "Only expecting list_declaration_specifier_x5f"
val reduce52 = fn list_eq1_TYPEDEF_declaration_specifier_x5f x => x | _ => error "Only expecting list_eq1_TYPEDEF_declaration_specifier_x5f"
val reduce53 = fn list_eq1_TYPEDEF_declaration_specifier_x5f x => x | _ => error "Only expecting list_eq1_TYPEDEF_declaration_specifier_x5f"
val reduce54 = fn list_eq1_type_specifier_unique___anonymous_x5f_x30_x5f x => x | _ => error "Only expecting list_eq1_type_specifier_unique___anonymous_x5f_x30_x5f"
val reduce55 = fn list_eq1_type_specifier_unique___anonymous_x5f_x30_x5f x => x | _ => error "Only expecting list_eq1_type_specifier_unique___anonymous_x5f_x30_x5f"
val reduce56 = fn list_eq1_type_specifier_unique___anonymous_x5f_x30_x5f x => x | _ => error "Only expecting list_eq1_type_specifier_unique___anonymous_x5f_x30_x5f"
val reduce57 = fn list_eq1_type_specifier_unique_declaration_specifier_x5f x => x | _ => error "Only expecting list_eq1_type_specifier_unique_declaration_specifier_x5f"
val reduce58 = fn list_eq1_type_specifier_unique_declaration_specifier_x5f x => x | _ => error "Only expecting list_eq1_type_specifier_unique_declaration_specifier_x5f"
val reduce59 = fn list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f x => x | _ => error "Only expecting list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f"
val reduce60 = fn list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f x => x | _ => error "Only expecting list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f"
val reduce61 = fn list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f x => x | _ => error "Only expecting list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f"
val reduce62 = fn list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f x => x | _ => error "Only expecting list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f"
val reduce63 = fn list_ge1_type_specifier_nonunique_declaration_specifier_x5f x => x | _ => error "Only expecting list_ge1_type_specifier_nonunique_declaration_specifier_x5f"
val reduce64 = fn list_ge1_type_specifier_nonunique_declaration_specifier_x5f x => x | _ => error "Only expecting list_ge1_type_specifier_nonunique_declaration_specifier_x5f"
val reduce65 = fn list_ge1_type_specifier_nonunique_declaration_specifier_x5f x => x | _ => error "Only expecting list_ge1_type_specifier_nonunique_declaration_specifier_x5f"
val reduce66 = fn list_eq1_eq1_TYPEDEF_type_specifier_unique_declaration_specifier_x5f x => x | _ => error "Only expecting list_eq1_eq1_TYPEDEF_type_specifier_unique_declaration_specifier_x5f"
val reduce67 = fn list_eq1_eq1_TYPEDEF_type_specifier_unique_declaration_specifier_x5f x => x | _ => error "Only expecting list_eq1_eq1_TYPEDEF_type_specifier_unique_declaration_specifier_x5f"
val reduce68 = fn list_eq1_eq1_TYPEDEF_type_specifier_unique_declaration_specifier_x5f x => x | _ => error "Only expecting list_eq1_eq1_TYPEDEF_type_specifier_unique_declaration_specifier_x5f"
val reduce69 = fn list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f x => x | _ => error "Only expecting list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f"
val reduce70 = fn list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f x => x | _ => error "Only expecting list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f"
val reduce71 = fn list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f x => x | _ => error "Only expecting list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f"
val reduce72 = fn list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f x => x | _ => error "Only expecting list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f"
val reduce73 = fn typedef_name x => x | _ => error "Only expecting typedef_name"
val reduce74 = fn var_name x => x | _ => error "Only expecting var_name"
val reduce75 = fn typedef_name_spec x => x | _ => error "Only expecting typedef_name_spec"
val reduce76 = fn general_identifier x => x | _ => error "Only expecting general_identifier"
val reduce77 = fn general_identifier x => x | _ => error "Only expecting general_identifier"
val reduce78 = fn save_context x => x | _ => error "Only expecting save_context"
val reduce79 = fn scoped_compound_statement_x5f x => x | _ => error "Only expecting scoped_compound_statement_x5f"
val reduce80 = fn scoped_iteration_statement_x5f x => x | _ => error "Only expecting scoped_iteration_statement_x5f"
val reduce81 = fn scoped_parameter_type_list_x5f x => x | _ => error "Only expecting scoped_parameter_type_list_x5f"
val reduce82 = fn scoped_selection_statement_x5f x => x | _ => error "Only expecting scoped_selection_statement_x5f"
val reduce83 = fn scoped_statement_x5f x => x | _ => error "Only expecting scoped_statement_x5f"
val reduce84 = fn declarator_varname x => x | _ => error "Only expecting declarator_varname"
val reduce85 = fn declarator_typedefname x => x | _ => error "Only expecting declarator_typedefname"
val reduce86 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce87 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce88 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce89 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce90 = fn primary_expression x => x | _ => error "Only expecting primary_expression"
val reduce91 = fn generic_selection x => x | _ => error "Only expecting generic_selection"
val reduce92 = fn generic_assoc_list x => x | _ => error "Only expecting generic_assoc_list"
val reduce93 = fn generic_assoc_list x => x | _ => error "Only expecting generic_assoc_list"
val reduce94 = fn generic_association x => x | _ => error "Only expecting generic_association"
val reduce95 = fn generic_association x => x | _ => error "Only expecting generic_association"
val reduce96 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce97 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce98 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce99 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce100 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce101 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce102 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce103 = fn postfix_expression x => x | _ => error "Only expecting postfix_expression"
val reduce104 = fn argument_expression_list x => x | _ => error "Only expecting argument_expression_list"
val reduce105 = fn argument_expression_list x => x | _ => error "Only expecting argument_expression_list"
val reduce106 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce107 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce108 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce109 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce110 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce111 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce112 = fn unary_expression x => x | _ => error "Only expecting unary_expression"
val reduce113 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce114 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce115 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce116 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce117 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce118 = fn unary_operator x => x | _ => error "Only expecting unary_operator"
val reduce119 = fn cast_expression x => x | _ => error "Only expecting cast_expression"
val reduce120 = fn cast_expression x => x | _ => error "Only expecting cast_expression"
val reduce121 = fn multiplicative_operator x => x | _ => error "Only expecting multiplicative_operator"
val reduce122 = fn multiplicative_operator x => x | _ => error "Only expecting multiplicative_operator"
val reduce123 = fn multiplicative_operator x => x | _ => error "Only expecting multiplicative_operator"
val reduce124 = fn multiplicative_expression x => x | _ => error "Only expecting multiplicative_expression"
val reduce125 = fn multiplicative_expression x => x | _ => error "Only expecting multiplicative_expression"
val reduce126 = fn additive_operator x => x | _ => error "Only expecting additive_operator"
val reduce127 = fn additive_operator x => x | _ => error "Only expecting additive_operator"
val reduce128 = fn additive_expression x => x | _ => error "Only expecting additive_expression"
val reduce129 = fn additive_expression x => x | _ => error "Only expecting additive_expression"
val reduce130 = fn shift_operator x => x | _ => error "Only expecting shift_operator"
val reduce131 = fn shift_operator x => x | _ => error "Only expecting shift_operator"
val reduce132 = fn shift_expression x => x | _ => error "Only expecting shift_expression"
val reduce133 = fn shift_expression x => x | _ => error "Only expecting shift_expression"
val reduce134 = fn relational_operator x => x | _ => error "Only expecting relational_operator"
val reduce135 = fn relational_operator x => x | _ => error "Only expecting relational_operator"
val reduce136 = fn relational_operator x => x | _ => error "Only expecting relational_operator"
val reduce137 = fn relational_operator x => x | _ => error "Only expecting relational_operator"
val reduce138 = fn relational_expression x => x | _ => error "Only expecting relational_expression"
val reduce139 = fn relational_expression x => x | _ => error "Only expecting relational_expression"
val reduce140 = fn equality_operator x => x | _ => error "Only expecting equality_operator"
val reduce141 = fn equality_operator x => x | _ => error "Only expecting equality_operator"
val reduce142 = fn equality_expression x => x | _ => error "Only expecting equality_expression"
val reduce143 = fn equality_expression x => x | _ => error "Only expecting equality_expression"
val reduce144 = fn and_expression x => x | _ => error "Only expecting and_expression"
val reduce145 = fn and_expression x => x | _ => error "Only expecting and_expression"
val reduce146 = fn exclusive_or_expression x => x | _ => error "Only expecting exclusive_or_expression"
val reduce147 = fn exclusive_or_expression x => x | _ => error "Only expecting exclusive_or_expression"
val reduce148 = fn inclusive_or_expression x => x | _ => error "Only expecting inclusive_or_expression"
val reduce149 = fn inclusive_or_expression x => x | _ => error "Only expecting inclusive_or_expression"
val reduce150 = fn logical_and_expression x => x | _ => error "Only expecting logical_and_expression"
val reduce151 = fn logical_and_expression x => x | _ => error "Only expecting logical_and_expression"
val reduce152 = fn logical_or_expression x => x | _ => error "Only expecting logical_or_expression"
val reduce153 = fn logical_or_expression x => x | _ => error "Only expecting logical_or_expression"
val reduce154 = fn conditional_expression x => x | _ => error "Only expecting conditional_expression"
val reduce155 = fn conditional_expression x => x | _ => error "Only expecting conditional_expression"
val reduce156 = fn assignment_expression x => x | _ => error "Only expecting assignment_expression"
val reduce157 = fn assignment_expression x => x | _ => error "Only expecting assignment_expression"
val reduce158 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce159 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce160 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce161 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce162 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce163 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce164 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce165 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce166 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce167 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce168 = fn assignment_operator x => x | _ => error "Only expecting assignment_operator"
val reduce169 = fn expression x => x | _ => error "Only expecting expression"
val reduce170 = fn expression x => x | _ => error "Only expecting expression"
val reduce171 = fn constant_expression x => x | _ => error "Only expecting constant_expression"
val reduce172 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce173 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce174 = fn declaration x => x | _ => error "Only expecting declaration"
val reduce175 = fn declaration_specifier x => x | _ => error "Only expecting declaration_specifier"
val reduce176 = fn declaration_specifier x => x | _ => error "Only expecting declaration_specifier"
val reduce177 = fn declaration_specifier x => x | _ => error "Only expecting declaration_specifier"
val reduce178 = fn declaration_specifier x => x | _ => error "Only expecting declaration_specifier"
val reduce179 = fn declaration_specifiers x => x | _ => error "Only expecting declaration_specifiers"
val reduce180 = fn declaration_specifiers x => x | _ => error "Only expecting declaration_specifiers"
val reduce181 = fn declaration_specifiers_typedef x => x | _ => error "Only expecting declaration_specifiers_typedef"
val reduce182 = fn declaration_specifiers_typedef x => x | _ => error "Only expecting declaration_specifiers_typedef"
val reduce183 = fn init_declarator_list_declarator_typedefname_x5f x => x | _ => error "Only expecting init_declarator_list_declarator_typedefname_x5f"
val reduce184 = fn init_declarator_list_declarator_typedefname_x5f x => x | _ => error "Only expecting init_declarator_list_declarator_typedefname_x5f"
val reduce185 = fn init_declarator_list_declarator_varname_x5f x => x | _ => error "Only expecting init_declarator_list_declarator_varname_x5f"
val reduce186 = fn init_declarator_list_declarator_varname_x5f x => x | _ => error "Only expecting init_declarator_list_declarator_varname_x5f"
val reduce187 = fn init_declarator_declarator_typedefname_x5f x => x | _ => error "Only expecting init_declarator_declarator_typedefname_x5f"
val reduce188 = fn init_declarator_declarator_typedefname_x5f x => x | _ => error "Only expecting init_declarator_declarator_typedefname_x5f"
val reduce189 = fn init_declarator_declarator_varname_x5f x => x | _ => error "Only expecting init_declarator_declarator_varname_x5f"
val reduce190 = fn init_declarator_declarator_varname_x5f x => x | _ => error "Only expecting init_declarator_declarator_varname_x5f"
val reduce191 = fn storage_class_specifier x => x | _ => error "Only expecting storage_class_specifier"
val reduce192 = fn storage_class_specifier x => x | _ => error "Only expecting storage_class_specifier"
val reduce193 = fn storage_class_specifier x => x | _ => error "Only expecting storage_class_specifier"
val reduce194 = fn storage_class_specifier x => x | _ => error "Only expecting storage_class_specifier"
val reduce195 = fn storage_class_specifier x => x | _ => error "Only expecting storage_class_specifier"
val reduce196 = fn type_specifier_nonunique x => x | _ => error "Only expecting type_specifier_nonunique"
val reduce197 = fn type_specifier_nonunique x => x | _ => error "Only expecting type_specifier_nonunique"
val reduce198 = fn type_specifier_nonunique x => x | _ => error "Only expecting type_specifier_nonunique"
val reduce199 = fn type_specifier_nonunique x => x | _ => error "Only expecting type_specifier_nonunique"
val reduce200 = fn type_specifier_nonunique x => x | _ => error "Only expecting type_specifier_nonunique"
val reduce201 = fn type_specifier_nonunique x => x | _ => error "Only expecting type_specifier_nonunique"
val reduce202 = fn type_specifier_nonunique x => x | _ => error "Only expecting type_specifier_nonunique"
val reduce203 = fn type_specifier_nonunique x => x | _ => error "Only expecting type_specifier_nonunique"
val reduce204 = fn type_specifier_nonunique x => x | _ => error "Only expecting type_specifier_nonunique"
val reduce205 = fn type_specifier_unique x => x | _ => error "Only expecting type_specifier_unique"
val reduce206 = fn type_specifier_unique x => x | _ => error "Only expecting type_specifier_unique"
val reduce207 = fn type_specifier_unique x => x | _ => error "Only expecting type_specifier_unique"
val reduce208 = fn type_specifier_unique x => x | _ => error "Only expecting type_specifier_unique"
val reduce209 = fn type_specifier_unique x => x | _ => error "Only expecting type_specifier_unique"
val reduce210 = fn type_specifier_unique x => x | _ => error "Only expecting type_specifier_unique"
val reduce211 = fn struct_or_union_specifier x => x | _ => error "Only expecting struct_or_union_specifier"
val reduce212 = fn struct_or_union_specifier x => x | _ => error "Only expecting struct_or_union_specifier"
val reduce213 = fn struct_or_union x => x | _ => error "Only expecting struct_or_union"
val reduce214 = fn struct_or_union x => x | _ => error "Only expecting struct_or_union"
val reduce215 = fn struct_declaration_list x => x | _ => error "Only expecting struct_declaration_list"
val reduce216 = fn struct_declaration_list x => x | _ => error "Only expecting struct_declaration_list"
val reduce217 = fn struct_declaration x => x | _ => error "Only expecting struct_declaration"
val reduce218 = fn struct_declaration x => x | _ => error "Only expecting struct_declaration"
val reduce219 = fn specifier_qualifier_list x => x | _ => error "Only expecting specifier_qualifier_list"
val reduce220 = fn specifier_qualifier_list x => x | _ => error "Only expecting specifier_qualifier_list"
val reduce221 = fn struct_declarator_list x => x | _ => error "Only expecting struct_declarator_list"
val reduce222 = fn struct_declarator_list x => x | _ => error "Only expecting struct_declarator_list"
val reduce223 = fn struct_declarator x => x | _ => error "Only expecting struct_declarator"
val reduce224 = fn struct_declarator x => x | _ => error "Only expecting struct_declarator"
val reduce225 = fn enum_specifier x => x | _ => error "Only expecting enum_specifier"
val reduce226 = fn enum_specifier x => x | _ => error "Only expecting enum_specifier"
val reduce227 = fn enumerator_list x => x | _ => error "Only expecting enumerator_list"
val reduce228 = fn enumerator_list x => x | _ => error "Only expecting enumerator_list"
val reduce229 = fn enumerator x => x | _ => error "Only expecting enumerator"
val reduce230 = fn enumerator x => x | _ => error "Only expecting enumerator"
val reduce231 = fn enumeration_constant x => x | _ => error "Only expecting enumeration_constant"
val reduce232 = fn atomic_type_specifier x => x | _ => error "Only expecting atomic_type_specifier"
val reduce233 = fn atomic_type_specifier x => x | _ => error "Only expecting atomic_type_specifier"
val reduce234 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce235 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce236 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce237 = fn type_qualifier x => x | _ => error "Only expecting type_qualifier"
val reduce238 = fn function_specifier x => x | _ => error "Only expecting function_specifier"
val reduce239 = fn function_specifier x => x | _ => error "Only expecting function_specifier"
val reduce240 = fn alignment_specifier x => x | _ => error "Only expecting alignment_specifier"
val reduce241 = fn alignment_specifier x => x | _ => error "Only expecting alignment_specifier"
val reduce242 = fn declarator x => x | _ => error "Only expecting declarator"
val reduce243 = fn declarator x => x | _ => error "Only expecting declarator"
val reduce244 = fn direct_declarator x => x | _ => error "Only expecting direct_declarator"
val reduce245 = fn direct_declarator x => x | _ => error "Only expecting direct_declarator"
val reduce246 = fn direct_declarator x => x | _ => error "Only expecting direct_declarator"
val reduce247 = fn direct_declarator x => x | _ => error "Only expecting direct_declarator"
val reduce248 = fn direct_declarator x => x | _ => error "Only expecting direct_declarator"
val reduce249 = fn direct_declarator x => x | _ => error "Only expecting direct_declarator"
val reduce250 = fn direct_declarator x => x | _ => error "Only expecting direct_declarator"
val reduce251 = fn direct_declarator x => x | _ => error "Only expecting direct_declarator"
val reduce252 = fn pointer x => x | _ => error "Only expecting pointer"
val reduce253 = fn type_qualifier_list x => x | _ => error "Only expecting type_qualifier_list"
val reduce254 = fn parameter_type_list x => x | _ => error "Only expecting parameter_type_list"
val reduce255 = fn parameter_list x => x | _ => error "Only expecting parameter_list"
val reduce256 = fn parameter_list x => x | _ => error "Only expecting parameter_list"
val reduce257 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce258 = fn parameter_declaration x => x | _ => error "Only expecting parameter_declaration"
val reduce259 = fn identifier_list x => x | _ => error "Only expecting identifier_list"
val reduce260 = fn identifier_list x => x | _ => error "Only expecting identifier_list"
val reduce261 = fn type_name x => x | _ => error "Only expecting type_name"
val reduce262 = fn abstract_declarator x => x | _ => error "Only expecting abstract_declarator"
val reduce263 = fn abstract_declarator x => x | _ => error "Only expecting abstract_declarator"
val reduce264 = fn abstract_declarator x => x | _ => error "Only expecting abstract_declarator"
val reduce265 = fn direct_abstract_declarator x => x | _ => error "Only expecting direct_abstract_declarator"
val reduce266 = fn direct_abstract_declarator x => x | _ => error "Only expecting direct_abstract_declarator"
val reduce267 = fn direct_abstract_declarator x => x | _ => error "Only expecting direct_abstract_declarator"
val reduce268 = fn direct_abstract_declarator x => x | _ => error "Only expecting direct_abstract_declarator"
val reduce269 = fn direct_abstract_declarator x => x | _ => error "Only expecting direct_abstract_declarator"
val reduce270 = fn direct_abstract_declarator x => x | _ => error "Only expecting direct_abstract_declarator"
val reduce271 = fn direct_abstract_declarator x => x | _ => error "Only expecting direct_abstract_declarator"
val reduce272 = fn direct_abstract_declarator x => x | _ => error "Only expecting direct_abstract_declarator"
val reduce273 = fn c_initializer x => x | _ => error "Only expecting c_initializer"
val reduce274 = fn c_initializer x => x | _ => error "Only expecting c_initializer"
val reduce275 = fn initializer_list x => x | _ => error "Only expecting initializer_list"
val reduce276 = fn initializer_list x => x | _ => error "Only expecting initializer_list"
val reduce277 = fn designation x => x | _ => error "Only expecting designation"
val reduce278 = fn designator_list x => x | _ => error "Only expecting designator_list"
val reduce279 = fn designator x => x | _ => error "Only expecting designator"
val reduce280 = fn designator x => x | _ => error "Only expecting designator"
val reduce281 = fn static_assert_declaration x => x | _ => error "Only expecting static_assert_declaration"
val reduce282 = fn statement x => x | _ => error "Only expecting statement"
val reduce283 = fn statement x => x | _ => error "Only expecting statement"
val reduce284 = fn statement x => x | _ => error "Only expecting statement"
val reduce285 = fn statement x => x | _ => error "Only expecting statement"
val reduce286 = fn statement x => x | _ => error "Only expecting statement"
val reduce287 = fn statement x => x | _ => error "Only expecting statement"
val reduce288 = fn labeled_statement x => x | _ => error "Only expecting labeled_statement"
val reduce289 = fn labeled_statement x => x | _ => error "Only expecting labeled_statement"
val reduce290 = fn labeled_statement x => x | _ => error "Only expecting labeled_statement"
val reduce291 = fn compound_statement x => x | _ => error "Only expecting compound_statement"
val reduce292 = fn block_item_list x => x | _ => error "Only expecting block_item_list"
val reduce293 = fn block_item x => x | _ => error "Only expecting block_item"
val reduce294 = fn block_item x => x | _ => error "Only expecting block_item"
val reduce295 = fn expression_statement x => x | _ => error "Only expecting expression_statement"
val reduce296 = fn selection_statement x => x | _ => error "Only expecting selection_statement"
val reduce297 = fn selection_statement x => x | _ => error "Only expecting selection_statement"
val reduce298 = fn selection_statement x => x | _ => error "Only expecting selection_statement"
val reduce299 = fn iteration_statement x => x | _ => error "Only expecting iteration_statement"
val reduce300 = fn iteration_statement x => x | _ => error "Only expecting iteration_statement"
val reduce301 = fn iteration_statement x => x | _ => error "Only expecting iteration_statement"
val reduce302 = fn iteration_statement x => x | _ => error "Only expecting iteration_statement"
val reduce303 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce304 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce305 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce306 = fn jump_statement x => x | _ => error "Only expecting jump_statement"
val reduce307 = fn translation_unit x => x | _ => error "Only expecting translation_unit"
val reduce308 = fn translation_unit x => x | _ => error "Only expecting translation_unit"
val reduce309 = fn external_declaration x => x | _ => error "Only expecting external_declaration"
val reduce310 = fn external_declaration x => x | _ => error "Only expecting external_declaration"
val reduce311 = fn function_definition_x31 x => x | _ => error "Only expecting function_definition_x31"
val reduce312 = fn function_definition x => x | _ => error "Only expecting function_definition"
val reduce313 = fn declaration_list x => x | _ => error "Only expecting declaration_list"
val reduce314 = fn declaration_list x => x | _ => error "Only expecting declaration_list"
end
structure C_Grammar_Rule_Wrap = 
struct
(*#line 1.2 "c_grammar_fun.grm"*)open C_Ast open C_Grammar_Rule_Lib

type start_happy = (unit, (unit, (unit, (unit, unit) either) either) either) either

fun start_happy4 (x : start_happy) = case x of Right (Right (Right (Left x))) => SOME x | _ => NONE
fun start_happy3 (x : start_happy) = case x of Right (Right (Left x)) => SOME x | _ => NONE
fun start_happy2 (x : start_happy) = case x of Right (Left x) => SOME x | _ => NONE
fun start_happy1 (x : start_happy) = case x of Left x => SOME x | _ => NONE


(*#line 4818.1 "c_grammar_fun.grm.sml"*)
fun update_env _ = K (return ())
val start_happy1 : ( ( unit, (unit, (unit, (unit, unit) either) either) either )  either) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val start_happy2 : ( ( unit, (unit, (unit, (unit, unit) either) either) either )  either) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val start_happy3 : ( ( unit, (unit, (unit, (unit, unit) either) either) either )  either) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val start_happy4 : ( ( unit, (unit, (unit, (unit, unit) either) either) either )  either) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_COMMA_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_COMMA_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option___anonymous_x5f_x32_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option___anonymous_x5f_x32_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_abstract_declarator_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_abstract_declarator_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_argument_expression_list_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_argument_expression_list_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_assignment_expression_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_assignment_expression_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_block_item_list_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_block_item_list_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_declaration_list_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_declaration_list_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_declarator_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_declarator_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_designation_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_designation_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_designator_list_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_designator_list_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_direct_abstract_declarator_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_direct_abstract_declarator_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_expression_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_expression_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_general_identifier_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_general_identifier_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_identifier_list_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_identifier_list_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_init_declarator_list_declarator_typedefname_x5f_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_init_declarator_list_declarator_typedefname_x5f_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_init_declarator_list_declarator_varname_x5f_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_init_declarator_list_declarator_varname_x5f_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_pointer_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_pointer_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_scoped_parameter_type_list_x5f_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_scoped_parameter_type_list_x5f_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_struct_declarator_list_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_struct_declarator_list_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_type_qualifier_list_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val option_type_qualifier_list_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list___anonymous_x5f_x30_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list___anonymous_x5f_x30_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list___anonymous_x5f_x30_x5f3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list___anonymous_x5f_x31_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list___anonymous_x5f_x31_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list___anonymous_x5f_x31_x5f3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_declaration_specifier_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_declaration_specifier_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_TYPEDEF_declaration_specifier_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_TYPEDEF_declaration_specifier_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_type_specifier_unique___anonymous_x5f_x30_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_type_specifier_unique___anonymous_x5f_x30_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_type_specifier_unique___anonymous_x5f_x30_x5f3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_type_specifier_unique_declaration_specifier_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_type_specifier_unique_declaration_specifier_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_ge1_type_specifier_nonunique___anonymous_x5f_x31_x5f4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_ge1_type_specifier_nonunique_declaration_specifier_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_ge1_type_specifier_nonunique_declaration_specifier_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_ge1_type_specifier_nonunique_declaration_specifier_x5f3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_eq1_TYPEDEF_type_specifier_unique_declaration_specifier_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_eq1_TYPEDEF_type_specifier_unique_declaration_specifier_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_eq1_TYPEDEF_type_specifier_unique_declaration_specifier_x5f3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val list_eq1_ge1_TYPEDEF_type_specifier_nonunique_declaration_specifier_x5f4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_name : (string) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val var_name : (string) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val typedef_name_spec : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val general_identifier1 : (string) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val general_identifier2 : (string) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val save_context : (C_Grammar_Rule_Lib.c_context) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val scoped_compound_statement_x5f : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val scoped_iteration_statement_x5f : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val scoped_parameter_type_list_x5f : (C_Grammar_Rule_Lib.c_context) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val scoped_selection_statement_x5f : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val scoped_statement_x5f : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declarator_varname : (C_Grammar_Rule_Lib.c_declarator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declarator_typedefname : (C_Grammar_Rule_Lib.c_declarator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val primary_expression5 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val generic_selection : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val generic_assoc_list1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val generic_assoc_list2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val generic_association1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val generic_association2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression5 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression6 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression7 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val postfix_expression8 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val argument_expression_list1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val argument_expression_list2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression5 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression6 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_expression7 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_operator1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_operator2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_operator3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_operator4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_operator5 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val unary_operator6 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val cast_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val cast_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val multiplicative_operator1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val multiplicative_operator2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val multiplicative_operator3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val multiplicative_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val multiplicative_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val additive_operator1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val additive_operator2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val additive_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val additive_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val shift_operator1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val shift_operator2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val shift_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val shift_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val relational_operator1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val relational_operator2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val relational_operator3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val relational_operator4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val relational_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val relational_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val equality_operator1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val equality_operator2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val equality_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val equality_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val and_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val and_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val exclusive_or_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val exclusive_or_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val inclusive_or_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val inclusive_or_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val logical_and_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val logical_and_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val logical_or_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val logical_or_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val conditional_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val conditional_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator5 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator6 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator7 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator8 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator9 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator10 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val assignment_operator11 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val expression1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val expression2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val constant_expression : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_specifier1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_specifier2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_specifier3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_specifier4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_specifiers1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_specifiers2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_specifiers_typedef1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_specifiers_typedef2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val init_declarator_list_declarator_typedefname_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val init_declarator_list_declarator_typedefname_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val init_declarator_list_declarator_varname_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val init_declarator_list_declarator_varname_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val init_declarator_declarator_typedefname_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val init_declarator_declarator_typedefname_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val init_declarator_declarator_varname_x5f1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val init_declarator_declarator_varname_x5f2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val storage_class_specifier1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val storage_class_specifier2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val storage_class_specifier3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val storage_class_specifier4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val storage_class_specifier5 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_nonunique1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_nonunique2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_nonunique3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_nonunique4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_nonunique5 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_nonunique6 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_nonunique7 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_nonunique8 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_nonunique9 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_unique1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_unique2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_unique3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_unique4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_unique5 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_specifier_unique6 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_or_union_specifier1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_or_union_specifier2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_or_union1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_or_union2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaration_list1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaration_list2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaration1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declaration2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val specifier_qualifier_list1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val specifier_qualifier_list2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declarator_list1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declarator_list2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declarator1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val struct_declarator2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enum_specifier1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enum_specifier2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enumerator_list1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enumerator_list2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enumerator1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enumerator2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val enumeration_constant : (string) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val atomic_type_specifier1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val atomic_type_specifier2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_specifier1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_specifier2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val alignment_specifier1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val alignment_specifier2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declarator1 : (C_Grammar_Rule_Lib.c_declarator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declarator2 : (C_Grammar_Rule_Lib.c_declarator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_declarator1 : (C_Grammar_Rule_Lib.c_declarator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_declarator2 : (C_Grammar_Rule_Lib.c_declarator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_declarator3 : (C_Grammar_Rule_Lib.c_declarator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_declarator4 : (C_Grammar_Rule_Lib.c_declarator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_declarator5 : (C_Grammar_Rule_Lib.c_declarator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_declarator6 : (C_Grammar_Rule_Lib.c_declarator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_declarator7 : (C_Grammar_Rule_Lib.c_declarator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_declarator8 : (C_Grammar_Rule_Lib.c_declarator) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val pointer : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_qualifier_list : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_type_list : (C_Grammar_Rule_Lib.c_context) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_list1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_list2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val parameter_declaration2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val identifier_list1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val identifier_list2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val type_name : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val abstract_declarator1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val abstract_declarator2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val abstract_declarator3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_abstract_declarator1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_abstract_declarator2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_abstract_declarator3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_abstract_declarator4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_abstract_declarator5 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_abstract_declarator6 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_abstract_declarator7 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val direct_abstract_declarator8 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val c_initializer1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val c_initializer2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val initializer_list1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val initializer_list2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val designation : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val designator_list : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val designator1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val designator2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val static_assert_declaration : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement5 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val statement6 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val labeled_statement1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val labeled_statement2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val labeled_statement3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val compound_statement : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val block_item_list : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val block_item1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val block_item2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val expression_statement : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val selection_statement1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val selection_statement2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val selection_statement3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val iteration_statement1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val iteration_statement2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val iteration_statement3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val iteration_statement4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val jump_statement1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val jump_statement2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val jump_statement3 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val jump_statement4 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val translation_unit1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val translation_unit2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val external_declaration1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val external_declaration2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition_x31 : (C_Grammar_Rule_Lib.c_context) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val function_definition : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_list1 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
val declaration_list2 : (unit) -> unit monad = update_env (fn _ => fn env => fn context => (env, context))
end
signature C_Grammar_TOKENS =
sig
type ('a,'b) token
type arg
type svalue0
type svalue = arg -> svalue0 * arg
val x25_eof:  'a * 'a -> (svalue,'a) token
val XOR_ASSIGN: (unit) *  'a * 'a -> (svalue,'a) token
val WHILE: (unit) *  'a * 'a -> (svalue,'a) token
val VOLATILE: (unit) *  'a * 'a -> (svalue,'a) token
val VOID: (unit) *  'a * 'a -> (svalue,'a) token
val VARIABLE: (unit) *  'a * 'a -> (svalue,'a) token
val UNSIGNED: (unit) *  'a * 'a -> (svalue,'a) token
val UNION: (unit) *  'a * 'a -> (svalue,'a) token
val TYPEDEF: (unit) *  'a * 'a -> (svalue,'a) token
val TYPE: (unit) *  'a * 'a -> (svalue,'a) token
val TILDE: (unit) *  'a * 'a -> (svalue,'a) token
val THREAD_LOCAL: (unit) *  'a * 'a -> (svalue,'a) token
val SWITCH: (unit) *  'a * 'a -> (svalue,'a) token
val SUB_ASSIGN: (unit) *  'a * 'a -> (svalue,'a) token
val STRUCT: (unit) *  'a * 'a -> (svalue,'a) token
val STRING_LITERAL: (unit) *  'a * 'a -> (svalue,'a) token
val STATIC_ASSERT: (unit) *  'a * 'a -> (svalue,'a) token
val STATIC: (unit) *  'a * 'a -> (svalue,'a) token
val STAR: (unit) *  'a * 'a -> (svalue,'a) token
val SLASH: (unit) *  'a * 'a -> (svalue,'a) token
val SIZEOF: (unit) *  'a * 'a -> (svalue,'a) token
val SIGNED: (unit) *  'a * 'a -> (svalue,'a) token
val SHORT: (unit) *  'a * 'a -> (svalue,'a) token
val SEMICOLON: (unit) *  'a * 'a -> (svalue,'a) token
val RPAREN: (unit) *  'a * 'a -> (svalue,'a) token
val RIGHT_ASSIGN: (unit) *  'a * 'a -> (svalue,'a) token
val RIGHT: (unit) *  'a * 'a -> (svalue,'a) token
val RETURN: (unit) *  'a * 'a -> (svalue,'a) token
val RESTRICT: (unit) *  'a * 'a -> (svalue,'a) token
val REGISTER: (unit) *  'a * 'a -> (svalue,'a) token
val RBRACK: (unit) *  'a * 'a -> (svalue,'a) token
val RBRACE: (unit) *  'a * 'a -> (svalue,'a) token
val QUESTION: (unit) *  'a * 'a -> (svalue,'a) token
val PTR: (unit) *  'a * 'a -> (svalue,'a) token
val PLUS: (unit) *  'a * 'a -> (svalue,'a) token
val PERCENT: (unit) *  'a * 'a -> (svalue,'a) token
val OR_ASSIGN: (unit) *  'a * 'a -> (svalue,'a) token
val NORETURN: (unit) *  'a * 'a -> (svalue,'a) token
val NEQ: (unit) *  'a * 'a -> (svalue,'a) token
val NAME: (string) *  'a * 'a -> (svalue,'a) token
val MUL_ASSIGN: (unit) *  'a * 'a -> (svalue,'a) token
val MOD_ASSIGN: (unit) *  'a * 'a -> (svalue,'a) token
val MINUS: (unit) *  'a * 'a -> (svalue,'a) token
val LT: (unit) *  'a * 'a -> (svalue,'a) token
val LPAREN: (unit) *  'a * 'a -> (svalue,'a) token
val LONG: (unit) *  'a * 'a -> (svalue,'a) token
val LEQ: (unit) *  'a * 'a -> (svalue,'a) token
val LEFT_ASSIGN: (unit) *  'a * 'a -> (svalue,'a) token
val LEFT: (unit) *  'a * 'a -> (svalue,'a) token
val LBRACK: (unit) *  'a * 'a -> (svalue,'a) token
val LBRACE: (unit) *  'a * 'a -> (svalue,'a) token
val INT: (unit) *  'a * 'a -> (svalue,'a) token
val INLINE: (unit) *  'a * 'a -> (svalue,'a) token
val INC: (unit) *  'a * 'a -> (svalue,'a) token
val IMAGINARY: (unit) *  'a * 'a -> (svalue,'a) token
val IF: (unit) *  'a * 'a -> (svalue,'a) token
val HAT: (unit) *  'a * 'a -> (svalue,'a) token
val GT: (unit) *  'a * 'a -> (svalue,'a) token
val GOTO: (unit) *  'a * 'a -> (svalue,'a) token
val GEQ: (unit) *  'a * 'a -> (svalue,'a) token
val GENERIC: (unit) *  'a * 'a -> (svalue,'a) token
val FOR: (unit) *  'a * 'a -> (svalue,'a) token
val FLOAT: (unit) *  'a * 'a -> (svalue,'a) token
val EXTERN: (unit) *  'a * 'a -> (svalue,'a) token
val EQEQ: (unit) *  'a * 'a -> (svalue,'a) token
val EQ: (unit) *  'a * 'a -> (svalue,'a) token
val EOF: (unit) *  'a * 'a -> (svalue,'a) token
val ENUM: (unit) *  'a * 'a -> (svalue,'a) token
val ELSE: (unit) *  'a * 'a -> (svalue,'a) token
val ELLIPSIS: (unit) *  'a * 'a -> (svalue,'a) token
val DOUBLE: (unit) *  'a * 'a -> (svalue,'a) token
val DOT: (unit) *  'a * 'a -> (svalue,'a) token
val DO: (unit) *  'a * 'a -> (svalue,'a) token
val DIV_ASSIGN: (unit) *  'a * 'a -> (svalue,'a) token
val DEFAULT: (unit) *  'a * 'a -> (svalue,'a) token
val DEC: (unit) *  'a * 'a -> (svalue,'a) token
val CONTINUE: (unit) *  'a * 'a -> (svalue,'a) token
val CONSTANT: (unit) *  'a * 'a -> (svalue,'a) token
val CONST: (unit) *  'a * 'a -> (svalue,'a) token
val COMPLEX: (unit) *  'a * 'a -> (svalue,'a) token
val COMMA: (unit) *  'a * 'a -> (svalue,'a) token
val COLON: (unit) *  'a * 'a -> (svalue,'a) token
val CHAR: (unit) *  'a * 'a -> (svalue,'a) token
val CASE: (unit) *  'a * 'a -> (svalue,'a) token
val BREAK: (unit) *  'a * 'a -> (svalue,'a) token
val BOOL: (unit) *  'a * 'a -> (svalue,'a) token
val BARBAR: (unit) *  'a * 'a -> (svalue,'a) token
val BAR: (unit) *  'a * 'a -> (svalue,'a) token
val BANG: (unit) *  'a * 'a -> (svalue,'a) token
val AUTO: (unit) *  'a * 'a -> (svalue,'a) token
val ATOMIC_LPAREN: (unit) *  'a * 'a -> (svalue,'a) token
val ATOMIC: (unit) *  'a * 'a -> (svalue,'a) token
val AND_ASSIGN: (unit) *  'a * 'a -> (svalue,'a) token
val ANDAND: (unit) *  'a * 'a -> (svalue,'a) token
val AND: (unit) *  'a * 'a -> (svalue,'a) token
val ALIGNOF: (unit) *  'a * 'a -> (svalue,'a) token
val ALIGNAS: (unit) *  'a * 'a -> (svalue,'a) token
val ADD_ASSIGN: (unit) *  'a * 'a -> (svalue,'a) token
val error:  'a * 'a -> (svalue,'a) token
val below_ELSE:  'a * 'a -> (svalue,'a) token
val start_translation_unit:  'a * 'a -> (svalue,'a) token
val start_statement:  'a * 'a -> (svalue,'a) token
val start_external_declaration:  'a * 'a -> (svalue,'a) token
val start_expression:  'a * 'a -> (svalue,'a) token
end
signature C_Grammar_LRVALS=
sig
structure Tokens : C_Grammar_TOKENS
structure ParserData:PARSER_DATA1
sharing type ParserData.Token.token = Tokens.token
end
