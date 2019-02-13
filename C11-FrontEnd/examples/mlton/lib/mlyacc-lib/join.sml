(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* functor Join creates a user parser by putting together a Lexer structure,
   an LrValues structure, and a polymorphic parser structure.  Note that
   the Lexer and LrValues structure must share the type pos (i.e. the type
   of line numbers), the type svalues for semantic values, and the type
   of tokens.
*)

functor Join2 (structure Lex : LEXER
               structure ParserData: PARSER_DATA2
               structure LrParser : LR_PARSER2
               sharing ParserData.LrTable = LrParser.LrTable
               sharing ParserData.Token = LrParser.Token
               sharing type Lex.UserDeclarations.svalue = ParserData.svalue
               sharing type Lex.UserDeclarations.pos = ParserData.pos
               sharing type Lex.UserDeclarations.token = ParserData.Token.token)
                 : PARSER2 =
struct
    structure Token = ParserData.Token
    structure Stream = LrParser.Stream

    exception ParseError = LrParser.ParseError

    type arg = ParserData.arg
    type pos = ParserData.pos
    type result = ParserData.result
    type svalue = ParserData.svalue
    val makeLexer = LrParser.Stream.streamify o Lex.makeLexer
    val parse = fn (lookahead,lexer,error,arg) =>
        (fn (a,b) => (ParserData.Actions.extract a,b))
     (LrParser.parse {table = ParserData.table,
                lexer=lexer,
                lookahead=lookahead,
                saction = ParserData.Actions.actions,
                arg=arg,
                void= ParserData.Actions.void,
                ec = {is_keyword = ParserData.EC.is_keyword,
                      noShift = ParserData.EC.noShift,
                      preferred_change = ParserData.EC.preferred_change,
                      errtermvalue = ParserData.EC.errtermvalue,
                      error=error,
                      showTerminal = ParserData.EC.showTerminal,
                      terms = ParserData.EC.terms}}
      )
     val sameToken = Token.sameToken
end

(* functor JoinWithArg creates a variant of the parser structure produced
   above.  In this case, the makeLexer take an additional argument before
   yielding a value of type unit -> (svalue,pos) token
 *)

functor JoinWithArg1(structure Lex : ARG_LEXER1
             structure ParserData: PARSER_DATA1
             structure LrParser : LR_PARSER1
             sharing ParserData.LrTable = LrParser.LrTable
             sharing ParserData.Token = LrParser.Token
             sharing type Lex.UserDeclarations.arg = ParserData.arg
             sharing type Lex.UserDeclarations.svalue0 = ParserData.svalue0
             sharing type Lex.UserDeclarations.pos = ParserData.pos
             sharing type Lex.UserDeclarations.token = ParserData.Token.token)
                 : ARG_PARSER1  =
struct
    structure Token = ParserData.Token
    structure Stream = LrParser.Stream

    exception ParseError = LrParser.ParseError

    type arg = ParserData.arg
    type pos = ParserData.pos
    type result = ParserData.result
    type svalue0 = ParserData.svalue0
    type svalue = arg -> svalue0 * arg
    type token0 = Lex.UserDeclarations.token0

    val makeLexer = LrParser.Stream.streamify o Lex.makeLexer

    val parse = fn (lookahead,error) =>
      LrParser.parse {table = ParserData.table,
                      lookahead=lookahead,
                      saction = ParserData.Actions.actions,
                      void= ParserData.Actions.void,
                      ec = {is_keyword = ParserData.EC.is_keyword,
                            noShift = ParserData.EC.noShift,
                            preferred_change = ParserData.EC.preferred_change,
                            errtermvalue = ParserData.EC.errtermvalue,
                            error=error,
                            showTerminal = ParserData.EC.showTerminal,
                            terms = ParserData.EC.terms}}
      #>> ParserData.Actions.extract

    val sameToken = Token.sameToken
end

functor JoinWithArg2(structure Lex : ARG_LEXER2
             structure ParserData: PARSER_DATA2
             structure LrParser : LR_PARSER2
             sharing ParserData.LrTable = LrParser.LrTable
             sharing ParserData.Token = LrParser.Token
             sharing type Lex.UserDeclarations.arg = ParserData.arg
             sharing type Lex.UserDeclarations.svalue = ParserData.svalue
             sharing type Lex.UserDeclarations.pos = ParserData.pos
             sharing type Lex.UserDeclarations.token = ParserData.Token.token)
                 : ARG_PARSER2  =
struct
    structure Token = ParserData.Token
    structure Stream = LrParser.Stream

    exception ParseError = LrParser.ParseError

    type arg = ParserData.arg
    type pos = ParserData.pos
    type result = ParserData.result
    type svalue = ParserData.svalue

    val makeLexer = LrParser.Stream.streamify oo Lex.makeLexer
    val parse = fn (lookahead,lexer,error,arg) =>
        (fn (a,b) => (ParserData.Actions.extract a,b))
     (LrParser.parse {table = ParserData.table,
                lexer=lexer,
                lookahead=lookahead,
                saction = ParserData.Actions.actions,
                arg=arg,
                void= ParserData.Actions.void,
                ec = {is_keyword = ParserData.EC.is_keyword,
                      noShift = ParserData.EC.noShift,
                      preferred_change = ParserData.EC.preferred_change,
                      errtermvalue = ParserData.EC.errtermvalue,
                      error=error,
                      showTerminal = ParserData.EC.showTerminal,
                      terms = ParserData.EC.terms}}
      )
    val sameToken = Token.sameToken
end;
