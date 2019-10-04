(*
Jacques-Henri Jourdan, Inria Paris
François Pottier, Inria Paris

Copyright (c) 2016-2017, Inria
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of Inria nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL INRIA BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(* WARNING. When processing this grammar, Menhir should announce that
   ONE shift/reduce conflict was silently solved and that ONE state
   has 3 reduce/reduce conflicts on RPAREN, LPAREN, and LBRACK. If you
   modify the grammar, you should check that this is still the case. *)

(* This file contains a variant of the parser in parser.mly that
   accepts ANSI C implicit declarations. See [allow_implicit_int] in
   options.ml *)

%{
  open Context
  open Options
  open Declarator
%}

%token<string> NAME
%token VARIABLE TYPE
%token CONSTANT STRING_LITERAL
%token
   ALIGNAS ALIGNOF ATOMIC BOOL COMPLEX IMAGINARY GENERIC NORETURN STATIC_ASSERT
   THREAD_LOCAL AUTO BREAK CASE CHAR CONST CONTINUE DEFAULT DO DOUBLE ELSE ENUM
   EXTERN FLOAT FOR GOTO IF INLINE INT LONG REGISTER RESTRICT RETURN SHORT
   SIGNED SIZEOF STATIC STRUCT SWITCH TYPEDEF UNION UNSIGNED VOID VOLATILE WHILE
%token
   PTR INC DEC LEFT RIGHT LEQ GEQ EQEQ EQ NEQ LT GT ANDAND BARBAR PLUS MINUS
   STAR TILDE BANG SLASH PERCENT HAT BAR QUESTION COLON AND MUL_ASSIGN
   DIV_ASSIGN MOD_ASSIGN ADD_ASSIGN SUB_ASSIGN LEFT_ASSIGN RIGHT_ASSIGN
   AND_ASSIGN XOR_ASSIGN OR_ASSIGN LPAREN ATOMIC_LPAREN RPAREN LBRACK RBRACK
   LBRACE RBRACE DOT COMMA SEMICOLON ELLIPSIS
%token EOF

%type<context> save_context parameter_type_list function_definition1
%type<string> typedef_name var_name general_identifier enumeration_constant

(* There is a reduce/reduce conflict in the grammar. It corresponds to
   the conflict in the second declaration in the following snippet:

     typedef int T;
     int f(int(T));

   It is specified by 6.7.6.3 11: 'T' should be taken as the type of
   parameter of the anonymous function taken as parameter by f (thus,
   f has type (T -> int) -> int).

   The reduce/reduce conflict is solved by letting menhir reduce the
   production appearing first in this file. This is the reason why we
   have the [typedef_name_spec] proxy: it is here just to make sure the
   conflicting production appears before the other (which concerns
   [general_identifier]).

 *)

(* These precedence declarations solve the dangling else conflict. *)
%nonassoc below_ELSE
%nonassoc ELSE

%start<unit> translation_unit_file

%%

(* Helpers *)

empty:
| /* nothing */
      {}

(* Note that, by convention, [X?] is syntactic sugar for [option(X)].
   [option(X)] represents a choice between nothing and [X].
   [ioption(X)] is the same thing, but is inlined at its use site,
   which in some cases is necessary in order to avoid a conflict. *)

%inline ioption(X):
| /* nothing */
| X
    {}

option(X):
| o = ioption(X)
    { o }

(* A list of A's, with suffix suff: *)

list_suff(A, suff):
| x = suff
| x = ne_list_suff(A, suff)
    { x }

ne_list_suff(A, suff):
| A x = list_suff(A, suff)
    { x }

(* A list of A's and B's that contains exactly one A, with suffix: *)

list_eq1(A, B, suff):
| A x = list_suff(B, suff)
| B x = list_eq1(A, B, suff)
    { x }

(* A list of A's and B's that contains at least one A, with suffix: *)

list_ge1(A, B, suff):
| A x = list_suff(B, suff)
| A x = list_ge1(A, B, suff)
| B x = list_ge1(A, B, suff)
    { x }

(* A list of A's, B's and C's that contains exactly one A and exactly one B, with suffix: *)

list_eq1_eq1(A, B, C, suff):
| A list_eq1(B, C, suff)
| B list_eq1(A, C, suff)
| C list_eq1_eq1(A, B, C, suff)
    {}

(* A list of A's, B's and C's that contains exactly one A and at least one B, with suffix: *)

list_eq1_ge1(A, B, C, suff):
| A list_ge1(B, C, suff)
| B list_eq1(A, C, suff)
| B list_eq1_ge1(A, B, C, suff)
| C list_eq1_ge1(A, B, C, suff)
    {}

(* The kind of an identifier should not be determined when looking
   ahead, because the context may not be up to date. For this reason,
   when reading an identifier, the lexer emits two tokens: the first
   one (NAME) is eaten as a lookahead token, the second one is the
   actual identifier.
*)

typedef_name:
| i = NAME TYPE
    { i }

(* We need [typedef_name_spec] to be declared before [general_identifier],
   so that the reduce/reduce conflict is solved the right way.  *)

typedef_name_spec:
| typedef_name
    {}

var_name:
| i = NAME VARIABLE
    { i }

general_identifier:
| i = typedef_name
| i = var_name
    { i }

save_context:
| (* empty *)
    { save_context () }

scoped(X):
| ctx = save_context x = X
    { restore_context ctx;
      x }

c99_scoped(X):
| ctx = save_context x = X
    { if !c99_scoping then restore_context ctx;
      x }

(* [declarator_varname] and [declarator_typedefname] are like [declarator].
   In addition, they have the side effect of introducing the declared identifier
   as a new variable or typedef name in the current context. *)

declarator_varname(ident):
| d = declarator(ident)
    { declare_varname (identifier d); d }

declarator_typedefname(ident):
| d = declarator(ident)
    { declare_typedefname (identifier d); d }

(* Actual grammar *)

primary_expression:
| var_name
| CONSTANT
| STRING_LITERAL
| LPAREN expression RPAREN
| generic_selection
    {}

generic_selection:
| GENERIC LPAREN assignment_expression COMMA generic_assoc_list RPAREN
    {}

generic_assoc_list:
| generic_association
| generic_assoc_list COMMA generic_association
    {}

generic_association:
| type_name COLON assignment_expression
| DEFAULT COLON assignment_expression
    {}

postfix_expression:
| primary_expression
| postfix_expression LBRACK expression RBRACK
| postfix_expression LPAREN argument_expression_list? RPAREN
| postfix_expression DOT general_identifier
| postfix_expression PTR general_identifier
| postfix_expression INC
| postfix_expression DEC
| LPAREN type_name RPAREN LBRACE initializer_list COMMA? RBRACE
    {}

argument_expression_list:
| assignment_expression
| argument_expression_list COMMA assignment_expression
    {}

unary_expression:
| postfix_expression
| INC unary_expression
| DEC unary_expression
| unary_operator cast_expression
| SIZEOF unary_expression
| SIZEOF LPAREN type_name RPAREN
| ALIGNOF LPAREN type_name RPAREN
    {}

unary_operator:
| AND
| STAR
| PLUS
| MINUS
| TILDE
| BANG
    {}

cast_expression:
| unary_expression
| LPAREN type_name RPAREN cast_expression
    {}

multiplicative_operator:
  STAR | SLASH | PERCENT {}

multiplicative_expression:
| cast_expression
| multiplicative_expression multiplicative_operator cast_expression
    {}

additive_operator:
  PLUS | MINUS {}

additive_expression:
| multiplicative_expression
| additive_expression additive_operator multiplicative_expression
    {}

shift_operator:
  LEFT | RIGHT {}

shift_expression:
| additive_expression
| shift_expression shift_operator additive_expression
    {}

relational_operator:
  LT | GT | LEQ | GEQ {}

relational_expression:
| shift_expression
| relational_expression relational_operator shift_expression
    {}

equality_operator:
  EQEQ | NEQ {}

equality_expression:
| relational_expression
| equality_expression equality_operator relational_expression
    {}

and_expression:
| equality_expression
| and_expression AND equality_expression
    {}

exclusive_or_expression:
| and_expression
| exclusive_or_expression HAT and_expression
    {}

inclusive_or_expression:
| exclusive_or_expression
| inclusive_or_expression BAR exclusive_or_expression
    {}

logical_and_expression:
| inclusive_or_expression
| logical_and_expression ANDAND inclusive_or_expression
    {}

logical_or_expression:
| logical_and_expression
| logical_or_expression BARBAR logical_and_expression
    {}

conditional_expression:
| logical_or_expression
| logical_or_expression QUESTION expression COLON conditional_expression
    {}

assignment_expression:
| conditional_expression
| unary_expression assignment_operator assignment_expression
    {}

assignment_operator:
| EQ
| MUL_ASSIGN
| DIV_ASSIGN
| MOD_ASSIGN
| ADD_ASSIGN
| SUB_ASSIGN
| LEFT_ASSIGN
| RIGHT_ASSIGN
| AND_ASSIGN
| XOR_ASSIGN
| OR_ASSIGN
    {}

expression:
| assignment_expression
| expression COMMA assignment_expression
    {}

constant_expression:
| conditional_expression
    {}

(* We distinguish four kinds of declarations, depending on:
   - whether they have a type specifier or use the "implicit int" rule
   - whether they are declaring typedef names or normal variables

  Moreover, at the end of the declaration specifiers list, it is not
  always to determine, using only the lookahead token, whether the
  list is finished or not. Therefore, we must avoid a reduction to
  happen at the end of the list (so that the multiple possibilities
  can be tried in parallel).

  To this end, we define non-terminals of lists of declaration
  specifiers, taking a suffix as parameter (the suffix being either
  empty when the declarator list is empty or being the first
  declarator). Then, [pref_init_declarator_list_opt] is a (possibly
  empty) list of init-declarators, whose first declarator is deeply
  embedded as a suffix of the declaration specifiers list.
 *)
declaration:
| pref_init_declarator_list_opt(declaration_specifiers,         declarator_varname(general_identifier))     SEMICOLON
| pref_init_declarator_list_opt(declaration_specifiers_typedef, declarator_typedefname(general_identifier)) SEMICOLON
| pref_init_declarator_list_opt(declaration_specifiers_nots,         declarator_varname(var_name))          SEMICOLON
| pref_init_declarator_list_opt(declaration_specifiers_nots_typedef, declarator_typedefname(var_name))      SEMICOLON
| static_assert_declaration
    {}

(* [declaration_specifier] corresponds to declaration-specifier
   in the C18 standard, deprived of TYPEDEF and of type specifiers. *)

%inline declaration_specifier:
| storage_class_specifier (* deprived of TYPEDEF *)
| type_qualifier
| function_specifier
| alignment_specifier
    {}

(* [declaration_specifiers] makes sure one type specifier is given,
   and, if a unique type specifier is given, then no other type
   specifier is given.

   This is a weaker condition than 6.7.2 2 (except for the case where
   no type specifier is given, which is treated separately, see
   [declaration_specifiers_nots]). It is necessary to enforce this in
   the grammar to disambiguate the example in 6.7.7 6:

   typedef signed int t;
   struct tag {
     unsigned t:4;
     const t:5;
   };

   The first field is a named t, while the second is unnamed of type t.

   [declaration_specifiers] forbids the [TYPEDEF] keyword.
 *)
declaration_specifiers(suff):
| x = list_eq1(type_specifier_unique, declaration_specifier, suff)
| x = list_ge1(type_specifier_nonunique, declaration_specifier, suff)
    { x }

(* [declaration_specifiers_typedef] is analogous to [declaration_specifiers],
   but requires the [TYPEDEF] keyword to be present (exactly once). *)
declaration_specifiers_typedef(suff):
| list_eq1_eq1(TYPEDEF, type_specifier_unique, declaration_specifier, suff)
| list_eq1_ge1(TYPEDEF, type_specifier_nonunique, declaration_specifier, suff)
    {}

(* [declaration_specifiers_nots] is the same as
   [declaration_specifiers], except that it forbids any type
   specifier. *)
declaration_specifiers_nots(suff):
| x = ne_list_suff(declaration_specifier, suff)
    { x }

(* [declaration_specifiers_nots_typedef] is the same as
   [declaration_specifiers_typedef], except that it forbids any type
   specifier. *)
declaration_specifiers_nots_typedef(suff):
| list_eq1(TYPEDEF, declaration_specifier, suff)
    {}

pref_init_declarator_list(pref, declarator):
| pref(init_declarator(declarator))
| pref_init_declarator_list(pref, declarator) COMMA init_declarator(declarator)
    {}

pref_init_declarator_list_opt(pref, declarator):
| pref(empty)
| pref_init_declarator_list(pref, declarator)
  {}

init_declarator(declarator):
| declarator
| declarator EQ c_initializer
  {}

(* [storage_class_specifier] corresponds to storage-class-specifier in the
   C18 standard, deprived of TYPEDEF (which receives special treatment). *)

storage_class_specifier:
| EXTERN
| STATIC
| THREAD_LOCAL
| AUTO
| REGISTER
    {}

(* A type specifier which can be associated with others. *)

type_specifier_nonunique:
| CHAR
| SHORT
| INT
| LONG
| FLOAT
| DOUBLE
| SIGNED
| UNSIGNED
| COMPLEX
    {}

(* A type specifier which cannot appear with other type specifiers. *)

type_specifier_unique:
| VOID
| BOOL
| atomic_type_specifier
| struct_or_union_specifier
| enum_specifier
| typedef_name_spec
    {}

struct_or_union_specifier:
| struct_or_union general_identifier? LBRACE struct_declaration_list RBRACE
| struct_or_union general_identifier
    {}

struct_or_union:
| STRUCT
| UNION
    {}

struct_declaration_list:
| struct_declaration
| struct_declaration_list struct_declaration
    {}

(* To avoid complicating the grammar, we do not allow using alignment
   specifiers in structs (which is a C18 feature) when no type specifier is
   present (this is a C89 feature). *)

struct_declaration:
| specifier_qualifier_list(empty) SEMICOLON
| type_qualifier_list(empty)      SEMICOLON
| pref_struct_declarator_list(specifier_qualifier_list, general_identifier) SEMICOLON
| pref_struct_declarator_list(type_qualifier_list, var_name)                SEMICOLON
| static_assert_declaration
    {}

(* As in the standard, except it also encodes the constraint described
   in the comment above [declaration_specifiers]. *)

specifier_qualifier_list(suff):
| list_eq1(type_specifier_unique, type_qualifier | alignment_specifier {}, suff)
| list_ge1(type_specifier_nonunique, type_qualifier | alignment_specifier {}, suff)
    {}

pref_struct_declarator_list(pref, ident):
| pref(struct_declarator(ident))
| pref_struct_declarator_list(pref, ident) COMMA struct_declarator(ident)
    {}

struct_declarator(ident):
| declarator(ident)
| declarator(ident)? COLON constant_expression
    {}

enum_specifier:
| ENUM general_identifier? LBRACE enumerator_list COMMA? RBRACE
| ENUM general_identifier
    {}

enumerator_list:
| enumerator
| enumerator_list COMMA enumerator
    {}

enumerator:
| i = enumeration_constant
| i = enumeration_constant EQ constant_expression
    { declare_varname i }

enumeration_constant:
| i = general_identifier
    { i }

atomic_type_specifier:
| ATOMIC LPAREN save_context type_name RPAREN
| ATOMIC ATOMIC_LPAREN type_name RPAREN
    { }

%inline type_qualifier:
| CONST
| RESTRICT
| VOLATILE
| ATOMIC
    {}

function_specifier:
| INLINE
| NORETURN
    {}

alignment_specifier:
| ALIGNAS LPAREN type_name RPAREN
| ALIGNAS LPAREN constant_expression RPAREN
    {}

declarator(ident):
| d = direct_declarator(ident)
    { d }
| pointer d = direct_declarator(ident)
    { other_declarator d }

(* The occurrences of [save_context] inside [direct_declarator] and
   [direct_abstract_declarator] seem to serve no purpose. In fact, they are
   required in order to avoid certain conflicts. In other words, we must save
   the context at this point because the LR automaton is exploring multiple
   avenues in parallel and some of them do require saving the context. *)

direct_declarator(ident):
| i = ident
    { identifier_declarator i }
| LPAREN save_context d = declarator(ident) RPAREN
    { d }
| d = direct_declarator(ident) LBRACK type_qualifier_list(empty)? assignment_expression? RBRACK
| d = direct_declarator(ident) LBRACK STATIC type_qualifier_list(empty)? assignment_expression RBRACK
| d = direct_declarator(ident) LBRACK type_qualifier_list(empty) STATIC assignment_expression RBRACK
| d = direct_declarator(ident) LBRACK type_qualifier_list(empty)? STAR RBRACK
    { other_declarator d }
| d = direct_declarator(ident) LPAREN ctx = scoped(parameter_type_list) RPAREN
    { function_declarator d ctx }
| d = direct_declarator(ident) LPAREN save_context identifier_list? RPAREN
    { other_declarator d }

pointer:
| STAR type_qualifier_list(empty)? pointer?
    {}

type_qualifier_list(suff):
| type_qualifier suff
| type_qualifier type_qualifier_list(suff)
    {}

parameter_type_list:
| parameter_list option(COMMA ELLIPSIS {}) ctx = save_context
    { ctx }

parameter_list:
| parameter_declaration
| parameter_list COMMA parameter_declaration
    {}

parameter_declaration:
| declaration_specifiers(declarator_varname(general_identifier))
| declaration_specifiers_nots(declarator_varname(var_name))
| declaration_specifiers(abstract_declarator?)
    {}

identifier_list:
| var_name
| identifier_list COMMA var_name
    {}

type_name:
| specifier_qualifier_list(empty) abstract_declarator?
    {}

abstract_declarator:
| pointer
| ioption(pointer) direct_abstract_declarator
    {}

direct_abstract_declarator:
| LPAREN save_context abstract_declarator RPAREN
| direct_abstract_declarator? LBRACK ioption(type_qualifier_list(empty)) assignment_expression? RBRACK
| direct_abstract_declarator? LBRACK STATIC type_qualifier_list(empty)? assignment_expression RBRACK
| direct_abstract_declarator? LBRACK type_qualifier_list(empty) STATIC assignment_expression RBRACK
| direct_abstract_declarator? LBRACK STAR RBRACK
| ioption(direct_abstract_declarator) LPAREN scoped(parameter_type_list)? RPAREN
    {}

c_initializer:
| assignment_expression
| LBRACE initializer_list COMMA? RBRACE
    {}

initializer_list:
| designation? c_initializer
| initializer_list COMMA designation? c_initializer
    {}

designation:
| designator_list EQ
    {}

designator_list:
| designator_list? designator
    {}

designator:
| LBRACK constant_expression RBRACK
| DOT general_identifier
    {}

static_assert_declaration:
| STATIC_ASSERT LPAREN constant_expression COMMA STRING_LITERAL RPAREN SEMICOLON
    {}

statement:
| labeled_statement
| (* scope: block *) scoped(compound_statement)
| expression_statement
| (* scope: block *) c99_scoped(selection_statement)
| (* scope: block *) c99_scoped(iteration_statement)
| jump_statement
    {}

labeled_statement:
| general_identifier COLON statement
| CASE constant_expression COLON statement
| DEFAULT COLON statement
    {}

compound_statement:
| LBRACE block_item_list? RBRACE
    {}

block_item_list:
| block_item_list? block_item
    {}

block_item:
| declaration
| statement
    {}

expression_statement:
| expression? SEMICOLON
    {}

selection_statement:
| IF LPAREN expression RPAREN (* scope: block *) c99_scoped(statement) ELSE (* scope: block *) c99_scoped(statement)
| IF LPAREN expression RPAREN (* scope: block *) c99_scoped(statement) %prec below_ELSE
| SWITCH LPAREN expression RPAREN (* scope: block *) c99_scoped(statement)
    {}

iteration_statement:
| WHILE LPAREN expression RPAREN (* scope: block *) c99_scoped(statement)
| DO (* scope: block *) c99_scoped(statement) WHILE LPAREN expression RPAREN SEMICOLON
| FOR LPAREN expression? SEMICOLON expression? SEMICOLON expression? RPAREN (* scope: block *) c99_scoped(statement)
| FOR LPAREN declaration expression? SEMICOLON expression? RPAREN (* scope: block *) c99_scoped(statement)
    {}

jump_statement:
| GOTO general_identifier SEMICOLON
| CONTINUE SEMICOLON
| BREAK SEMICOLON
| RETURN expression? SEMICOLON
    {}

translation_unit_file:
| external_declaration translation_unit_file
| external_declaration EOF
    {}

external_declaration:
| function_definition
| declaration
    {}

function_definition1:
| d = declaration_specifiers(declarator_varname(general_identifier))
| d = declaration_specifiers_nots(declarator_varname(var_name))
| d = declarator_varname(var_name)
    { let ctx = save_context () in
      reinstall_function_context d;
      ctx }

function_definition:
| ctx = function_definition1 declaration_list? compound_statement
    { restore_context ctx }

declaration_list:
| declaration
| declaration_list declaration
    {}
