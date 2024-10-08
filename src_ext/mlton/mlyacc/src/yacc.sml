(* Modified by Frédéric Tuong
 * Isabelle/C
 * (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *)
(* Modified by Matthew Fluet on 2011-06-17.
 * Use simple file name (rather than absolute paths) in line directives in output.
 *)
(* Modified by Vesa Karvonen on 2007-12-18.
 * Create line directives in output.
 *)
(* ML-Yacc Parser Generator (c) 1989, 1990 Andrew W. Appel, David R. Tarditi *)

functor ParseGenFun(structure ParseGenParser : PARSE_GEN_PARSER
                    structure MakeTable : MAKE_LR_TABLE
                    structure Verbose : VERBOSE
                    structure PrintStruct : PRINT_STRUCT

                    sharing MakeTable.LrTable = PrintStruct.LrTable
                    sharing MakeTable.Errs = Verbose.Errs

                    structure Absyn : ABSYN
                    ) : PARSE_GEN =
  struct
    val sub = Array.sub
    infix 9 sub
    structure Grammar = MakeTable.Grammar
    structure Header = ParseGenParser.Header

    open Header Grammar

    (* approx. maximum length of a line *)

    val lineLength = 70

    (* record type describing names of structures in the program being
        generated *)

    datatype names = NAMES
                        of {miscStruct : string,  (* Misc{n} struct name *)
                            tableStruct : string, (* LR table structure *)
                            tokenStruct : string, (* Tokens{n} struct name *)
                            actionsStruct : string, (* Actions structure *)
                            valueStruct: string, (* semantic value structure *)
                            valueMonadStruct: string, (* semantic value structure *)
                            ecStruct : string,  (* error correction structure *)
                            arg: string, (* user argument for parser *)
                            tokenSig : string,  (* TOKENS{n} signature *)
                            miscSig :string, (* Signature for Misc structure *)
                            dataStruct:string, (* name of structure in Misc *)
                                                (* which holds parser data *)
                            dataSig:string (* signature for this structure *)

                            }

    val DEBUG = true
    exception Semantic

    (* common functions and values used in printing out program *)

    datatype values = VALS
                      of {say : string -> unit,
                          saydot : string -> unit,
                          sayln : string -> unit,
                          fmtPos : {line : int, col : int} option -> string,
                          pureActions: bool,
                          pos_type : string,
                          arg_type : string,
                          ntvoid : string,
                          termvoid : string,
                          start : Grammar.nonterm,
                          hasType : Grammar.symbol -> bool,

                          (* actual (user) name of terminal *)

                          termToString : Grammar.term -> string,
                          symbolToString : Grammar.symbol -> string,

                          (* type symbol comes from the HDR structure,
                             and is now abstract *)

                          term : (Header.symbol * ty option) list,
                          nonterm : (Header.symbol * ty option) list,
                          terms : Grammar.term list,

                          (* tokenInfo is the user inserted spec in
                             the *_TOKEN sig*)
                          tokenInfo : string option}

    structure SymbolHash = Hash(type elem = string
                                val gt = (op >) : string*string -> bool)

    structure TermTable = Table(type key = Grammar.term
                                val gt = fn (T i,T j) => i > j)

    structure SymbolTable = Table(
        type key = Grammar.symbol
        val gt = fn (TERM(T i),TERM(T j)) => i>j
                  | (NONTERM(NT i),NONTERM(NT j)) => i>j
                  | (NONTERM _,TERM _) => true
                  | (TERM _,NONTERM _) => false)

    (* printTypes: function to print the following types in the LrValues
       structure and a structure containing the datatype svalue:

                type svalue -- it holds semantic values on the parse
                                   stack
                type pos -- the type of line numbers
                type result -- the type of the value that results
                                   from the parse

        The type svalue is set equal to the datatype svalue declared
        in the structure named by valueStruct.  The datatype svalue
        is declared inside the structure named by valueStruct to deal
        with the scope of constructors.
    *)

    fun mk_name_rulenum' hasType saySym ntvoid {lhs, rulenum' = (rulenum', total), ...} =
      (if hasType (NONTERM lhs)
       then saySym(NONTERM lhs)
       else ntvoid)
      ^ (if total = 1 then "" else Int.toString rulenum')
    val printTypes1 = fn (rules,
                          VALS {term,nonterm,symbolToString,pos_type,
                                arg_type,
                                termvoid,ntvoid,saydot,hasType,start,
                                pureActions,...},
                          NAMES {valueStruct, valueMonadStruct, ...},
                          say, fmtPos, header) =>
     let val sayln = fn t => (say t; say "\n")

         val addConstr = fn (symbol,SOME s) =>
           Symtab.insert (op =) ((symbolName symbol), (if pureActions then "" else "unit -> ") ^
                                " (" ^ tyName s ^ ")")
                         | _ => I
         val tytab = fold (fold addConstr) [term, nonterm] Symtab.empty
         val saySym = symbolToString

         val prConstr = fn (symbol,SOME s) =>
                           say (" | " ^ (symbolName symbol) ^ " of " ^
                                  (if pureActions then "" else "unit -> ") ^
                                " (" ^ tyName s ^ ")"
                                )
                         | _ => ()
         fun prDestr0' lhs = if hasType (NONTERM lhs)
                             then saySym(NONTERM lhs)
                             else ntvoid
         fun prDestr0 f {lhs, rulenum, ...} = sayln (f (Int.toString rulenum) (prDestr0' lhs))
         fun prDestrTy {lhs, rulenum' = (rulen, total), ...} =
           if rulen = 1
           then sayln ("  (\"" ^ (Symtab.lookup tytab (prDestr0' lhs) |> the) ^ "\", " ^ Int.toString total ^ "),")
           else ()
         fun prDestrTy' {lhs, rulenum' = (rulen, total), ...} =
           if rulen = 1
           then sayln ("  (\"" ^ prDestr0' lhs ^ "\", " ^ Int.toString total ^ "),")
           else ()
         val prDestr = prDestr0 (fn rulen => fn constr =>
                                   "val reduce" ^ rulen ^ " = fn " ^ 
                                     constr ^ " x => x | _ => error \"Only expecting " ^ constr ^ "\"")
         fun prDestr' rule = 
           sayln ("val " ^ mk_name_rulenum' hasType saySym ntvoid rule
                         ^ " :"
                         ^ the (Symtab.lookup tytab (prDestr0' (#lhs rule)))
                         ^ " -> unit monad = update_env (fn _ => fn env => fn context => (env, context))")

     in sayln ("structure " ^ valueStruct ^ " = ");
        sayln "struct";
        say (fmtPos (SOME {line = 1, col = 1}));
        sayln header;
        say (fmtPos NONE);
        say (if pureActions then
               "datatype svalue0 = " ^ termvoid ^ " | " ^ ntvoid ^ " of unit"
             else
               "datatype svalue = " ^ termvoid ^ " | " ^ ntvoid ^ " of unit -> unit");
        app prConstr term;
        app prConstr nonterm;
        app sayln [ ""
                  , "fun find_list msg mk_name l ="
                  , "  let val tab ="
                  , "        fold (fn (name, occ) =>"
                  , "               fold (fn name => fn (tab, nb) => (Inttab.update (nb, name) tab, nb + 1))"
                  , "                    (if occ = 1 then [name]"
                  , "                                else map_range (mk_name name) occ))"
                  , "             l"
                  , "             (Inttab.empty, 0)"
                  , "        |> #1"
                  , "  in"
                  , "    fn i => case Inttab.lookup tab i of NONE => error msg | SOME name => name"
                  , "  end" ];
        (sayln "val type_reduce = find_list \"reduce type not found\" K [";
         app prDestrTy rules;
         sayln "  (\"\", 0)]");
        (sayln "val string_reduce = find_list \"reduce type not found\" (fn name => fn occ => name ^ Int.toString (occ + 1)) [";
         app prDestrTy' rules;
         sayln "  (\"\", 0)]");
        app prDestr rules;
        sayln "end";

        sayln ("structure " ^ valueMonadStruct ^ " = ");
        sayln "struct";
        say (fmtPos (SOME {line = 1, col = 1}));
        sayln header;
        say (fmtPos NONE);
        sayln "fun update_env _ = K (return ())";
        app prDestr' rules;
        sayln "end"
    end

    val printTypes2 = fn (VALS {say,sayln,term,nonterm,symbolToString,pos_type,
                                 arg_type,
                                 termvoid,ntvoid,saydot,hasType,start,
                                 pureActions,...},
                           NAMES {valueStruct,...},symbolType) =>
       (sayln "local open Header in";
        sayln ("type pos = " ^ pos_type);
        sayln ("type arg = " ^ arg_type);
        (if pureActions then
           (sayln ("type svalue0 = " ^ valueStruct ^ ".svalue0");
            sayln "type svalue = arg -> svalue0 * arg")
         else
           sayln ("type svalue = " ^ valueStruct ^ ".svalue"));
        say "type result = ";
        case symbolType (NONTERM start)
        of NONE => sayln "unit"
         | SOME t => (say (tyName t); sayln "");
        sayln "end")

     (* function to print Tokens{n} structure *)

    val printTokenStruct =
     fn (VALS {say, sayln, termToString, hasType,termvoid,terms,
               pureActions,tokenInfo,...},
         NAMES {miscStruct,tableStruct,valueStruct,
                tokenStruct,tokenSig,dataStruct,...}) =>
                (sayln ("structure " ^ tokenStruct ^ " : " ^ tokenSig ^ " =");
                 sayln "struct";
                 (if tokenInfo = NONE andalso not pureActions
                  then ()
                  else sayln ("open Header"));
                 (if pureActions then
                   (sayln ("type arg = " ^ dataStruct ^ ".arg");
                    sayln ("type svalue0 = " ^ dataStruct ^ ".svalue0");
                    sayln "type svalue = arg -> svalue0 * arg")
                  else
                    sayln ("type svalue = " ^ dataStruct ^ ".svalue"));
                 sayln "type ('a,'b) token = ('a,'b) Token.token";
                 let val f = fn term as T i =>
                        (say "fun "; say (termToString term);
                         say " (";
                         if (hasType (TERM term)) then say "i," else ();
                         say "p1,p2) = Token.TOKEN (";
                         say (dataStruct ^ "." ^ tableStruct ^ ".T ");
                         say (Int.toString i);
                         say ",(";
                         let val s = 
                           valueStruct ^ "."
                           ^ (if (hasType (TERM term)) then
                              (termToString term ^
                               (if pureActions then " i"
                                else " (fn () => i)"))
                           else termvoid)
                         in say (if pureActions then "return (" ^ s ^ ")" else s)
                         end;
                         say ",";
                         sayln "p1,p2))")
                in app f terms
                end;
                sayln "end")

    (* function to print signatures out - takes print function which
        does not need to insert line breaks *)

    val printSigs = fn (rules,
                        values as VALS {term,tokenInfo,pureActions,...},
                        names as NAMES {tokenSig,tokenStruct,miscSig,
                                        dataStruct, dataSig, ...},
                        say, fmtPos, header) =>
      let in printTypes1 (rules, values, names, say, fmtPos, header);
          say  ("signature " ^ tokenSig ^ " =\nsig\n"^
                (case tokenInfo of NONE => "" | SOME s => (s^"\n"))^
                "type ('a,'b) token\n"^
                (if pureActions then
                   "type arg\ntype svalue0\ntype svalue = arg -> svalue0 * arg\n"
                 else "type svalue\n") ^
                (List.foldr (fn ((s,ty),r) => String.concat [
                    "val ", symbolName s,
                    (case ty
                     of NONE => ": "
                      | SOME l => ": (" ^ (tyName l) ^ ") * "),
                    " 'a * 'a -> (svalue,'a) token\n", r]) "" term) ^
                "end\nsignature " ^ miscSig ^
                "=\nsig\nstructure Tokens : " ^ tokenSig ^
                "\nstructure " ^ dataStruct ^ ":" ^ dataSig ^
                "\nsharing type " ^ dataStruct ^
                ".Token.token = Tokens.token\n"^
                (if pureActions then ""
                 else "sharing type " ^ dataStruct ^ ".svalue = Tokens.svalue\n") ^
                "end\n")
      end

    (* function to print structure for error correction *)

    val printEC = fn (keyword : term list,
                      preferred_change : (term list * term list) list,
                      noshift : term list,
                      value : (term * string) list,
                      VALS {termToString, say,sayln,terms,saydot,hasType,
                            termvoid,pureActions,...},
                      NAMES {ecStruct,tableStruct,valueStruct,...}) =>
       let

         val sayterm = fn (T i) => (say "(T "; say (Int.toString i); say ")")

         val printBoolCase = fn ( l : term list) =>
            (say "fn ";
             app (fn t => (sayterm t; say " => true"; say " | ")) l;
             sayln "_ => false")

         val printTermList = fn (l : term list) =>
           (sayln "nil"; app (fn t => (say " $$ "; sayterm t)) (rev l))


         fun printChange () =
            (sayln "val preferred_change : (term list * term list) list = ";
             app (fn (d,i) =>
                    (say"("; printTermList d; say ","; printTermList i;
                     sayln ")::"
                    )
                 ) preferred_change;
             sayln "nil")

         val printErrValues = fn (l : (term * string) list) =>
            (sayln "local open Header in";
             sayln "val errtermvalue=";
             say ((if pureActions then "return o" else "") ^ " (fn ");
             app (fn (t,s) =>
                    (sayterm t; say " => ";
                     saydot valueStruct; say (termToString t);
                     say "(";
                     if pureActions then () else say "fn () => ";
                     say "("; say s; say "))";
                     sayln " | "
                    )
                 ) l;
            say "_ => ";
            say (valueStruct ^ ".");
            sayln termvoid; sayln ") end")


          val printNames = fn () =>
                let val f = fn term => (
                        sayterm term; say " => ";
                        sayln (String.concat["\"", termToString term, "\""]);
                        say "  | ")
                in (sayln "val showTerminal =";
                    say "fn ";
                    app f terms;
                    sayln "_ => \"bogus-term\"")
                end

           val ecTerms =
                List.foldr (fn (t,r) =>
                  if hasType (TERM t) orelse List.exists (fn (a,_)=>a=t) value
                    then r
                    else t::r)
                [] terms

        in  say "structure ";
            say ecStruct;
            sayln "=";
            sayln "struct";
            say "open ";
            sayln tableStruct;
            sayln "infix 5 $$";
            sayln "fun x $$ y = y::x";
            sayln "val is_keyword =";
            printBoolCase keyword;
            printChange();
            sayln "val noShift = ";
            printBoolCase noshift;
            printNames ();
            printErrValues value;
            say "val terms : term list = ";
            printTermList ecTerms;
            sayln "end"
        end

val printAction = fn (rules,
                          VALS {hasType,say,sayln,fmtPos,termvoid,ntvoid,
                                symbolToString,saydot,start,pureActions,...},
                          NAMES {actionsStruct,valueStruct,valueMonadStruct,tableStruct,arg,...}) =>
let val printAbsynRule = Absyn.printRule(say,sayln,fmtPos)
    val is_nonterm = fn (NONTERM i) => true | _ => false
    val numberRhs = fn r =>
        List.foldl (fn (e,(r,table)) =>
                let val num = case SymbolTable.find(e,table)
                               of SOME i => i
                                | NONE => 1
                 in ((e,num,hasType e orelse is_nonterm e)::r,
                     SymbolTable.insert((e,num+1),table))
                 end) (nil,SymbolTable.empty) r

    val saySym = symbolToString

    val printCase = fn (i:int, r as {lhs=lhs as (NT lhsNum),prec,
                                        rhs,code=code0,rulenum,rulenum'}) =>

       (* mkToken: Build an argument *)

       let open Absyn
           val mkToken = fn (sym,num : int,typed) =>
             let val symString = symbolToString sym
               val symNum = symString ^ (Int.toString num)
             in PTUPLE[WILD,
                     PTUPLE[if not (hasType sym) then
                              (if is_nonterm sym then
                                   PAPP(valueStruct^"."^ntvoid,
                                        PVAR symNum)
                              else WILD)
                           else
                               PAPP(valueStruct^"."^symString,
                                 if num=1 andalso pureActions
                                     then AS(symNum,PVAR symString)
                                 else PVAR symNum),
                             if num=1 then AS(symString^"left",
                                              PVAR(symNum^"left"))
                             else PVAR(symNum^"left"),
                             if num=1 then AS(symString^"right",
                                              PVAR(symNum^"right"))
                             else PVAR(symNum^"right")]]
             end

            val numberedRhs = #1 (numberRhs rhs)

        (* construct case pattern *)

           val pat = PTUPLE[PINT i,PLIST(map mkToken numberedRhs,
                                         SOME (PVAR "rest671"))]

        (* remove terminals in argument list w/o types *)

           val argsWithTypes =
                  List.foldr (fn ((_,_,false),r) => r
                         | (s as (_,_,true),r) => s::r) nil numberedRhs

        (* construct case body *)

           val defaultPos = EVAR "defaultPos"
           val explicit_monad = case explode (#text code0) of #"(" :: #"*" :: #"%" :: #"*" :: #")" :: _ => true | _ => false
           val resultexp = EVAR "result"
           val resultpat = PVAR "result"
           val code = CODE code0
           val rest = EVAR "rest671"
           val cons_name = EVAR(valueStruct^"."^
                                 (if hasType (NONTERM lhs)
                                      then saySym(NONTERM lhs)
                                      else ntvoid))
           val cons_name_monad = EVAR(valueMonadStruct^"."^ mk_name_rulenum' hasType saySym ntvoid r)

           val body =
             LET([VB(resultpat,
                   if pureActions
                     then EAPP (EVAR "op #>>", ETUPLE [EAPP (EAPP (EVAR "bind'", if explicit_monad then code else EAPP (EVAR "return", code)), cons_name_monad), cons_name])
                     else
                       EAPP(cons_name,
                          if argsWithTypes=nil then FN(WILD,code)
                          else
                           FN(WILD,
                             let val body =
                                LET(map (fn (sym,num:int,_) =>
                                  let val symString = symbolToString sym
                                      val symNum = symString ^ Int.toString num
                                  in VB(if num=1 then
                                             AS(symString,PVAR symNum)
                                        else PVAR symNum,
                                        EAPP(EVAR symNum,UNIT))
                                  end) (rev argsWithTypes),
                                      code)
                             in if hasType (NONTERM lhs) then
                                    body else SEQ(body,UNIT)
                             end)))],
                   ETUPLE[EAPP(EVAR(tableStruct^".NT"),EINT(lhsNum)),
                          case rhs
                          of nil => ETUPLE[resultexp,defaultPos,defaultPos]
                           | r =>let val (rsym,rnum,_) = hd(numberedRhs)
                                     val (lsym,lnum,_) = hd(rev numberedRhs)
                                 in ETUPLE[resultexp,
                                           EVAR (symbolToString lsym ^
                                                 Int.toString lnum ^ "left"),
                                           EVAR (symbolToString rsym ^
                                                  Int.toString rnum ^ "right")]
                                 end,
                           rest])
    in printAbsynRule (RULE(pat,body))
    end

          val prRules = fn () =>
             (sayln "fn (i392,defaultPos,stack,";
              say   "    ("; say arg; sayln "):arg) =>";
              sayln "case (i392,stack)";
              say "of ";
              app (fn (rule as {rulenum,...}) =>
                   (printCase(rulenum,rule); say "| ")) rules;
             sayln "_ => raise (mlyAction i392)")

        in say "structure ";
           say actionsStruct;
           sayln " =";
           sayln "struct ";
           sayln "exception mlyAction of int";
           sayln "local open Header in";
           sayln "val actions = ";
           prRules();
           say ("val void = " ^ (if pureActions then "return " else ""));
           saydot valueStruct;
           sayln termvoid;
           sayln "end";
           say "val extract = ";
           say "fn a => (fn ";
           saydot valueStruct;
           if hasType (NONTERM start)
              then say (symbolToString (NONTERM start))
              else say "ntVOID";
           sayln " x => x";
           sayln "| _ => let exception ParseInternal";
           say "\tin raise ParseInternal end) a ";
           sayln (if pureActions then "" else "()");
           sayln "end"
        end

    val make_parser = fn ((header,
         DECL {eop,change,keyword,nonterm,prec,
               term, control,value} : declData,
               rules : rule list list),spec,error : pos -> string -> unit,
               wasError : unit -> bool) =>
     let
        val verbose = List.exists (fn VERBOSE=>true | _ => false) control
        val defaultReductions = not (List.exists (fn NODEFAULT=>true | _ => false) control)
        val pos_type =
           let fun f nil = NONE
                 | f ((POS s)::r) = SOME s
                 | f (_::r) = f r
           in f control
           end
        val start =
           let fun f nil = NONE
                 | f ((START_SYM s)::r) = SOME s
                 | f (_::r) = f r
           in f control
           end
        val name =
           let fun f nil = NONE
                 | f ((PARSER_NAME s)::r) = SOME s
                 | f (_::r) = f r
           in f control
           end
        val header_decl =
           let fun f nil = NONE
                 | f ((FUNCTOR s)::r) = SOME s
                 | f (_::r) = f r
           in f control
           end

        val token_sig_info_decl =
            let fun f nil = NONE
                  | f ((TOKEN_SIG_INFO s)::_) = SOME s
                  | f (_::r) = f r
            in f control
            end

        val arg_decl =
           let fun f nil = ("()","unit")
                 | f ((PARSE_ARG s)::r) = s
                 | f (_::r) = f r
           in f control
           end

        val noshift =
           let fun f nil = nil
                 | f ((NSHIFT s)::r) = s
                 | f (_::r) = f r
           in f control
           end

        val pureActions =
           let fun f nil = false
                 | f ((PURE)::r) = true
                 | f (_::r) = f r
           in f control
           end

        val term =
         case term
           of NONE => (error {line = 1, col = 0} "missing %term definition"; nil)
            | SOME l => l

        val nonterm =
         case nonterm
          of NONE => (error {line = 1, col = 0} "missing %nonterm definition"; nil)
           | SOME l => l

        val pos_type =
         case pos_type
          of NONE => (error {line = 1, col = 0} "missing %pos definition"; "")
           | SOME l => l


        val termHash =
          List.foldr (fn ((symbol,_),table) =>
              let val name = symbolName symbol
              in if SymbolHash.exists(name,table) then
                   (error (symbolPos symbol)
                          ("duplicate definition of " ^ name ^ " in %term");
                    table)
                else SymbolHash.add(name,table)
              end) SymbolHash.empty term

        val isTerm = fn name => SymbolHash.exists(name,termHash)

        val symbolHash =
          List.foldr (fn ((symbol,_),table) =>
            let val name = symbolName symbol
            in if SymbolHash.exists(name,table) then
                 (error (symbolPos symbol)
                     (if isTerm name then
                          name ^ " is defined as a terminal and a nonterminal"
                      else
                          "duplicate definition of " ^ name ^ " in %nonterm");
                     table)
             else SymbolHash.add(name,table)
            end) termHash nonterm

        fun makeUniqueId s =
                if SymbolHash.exists(s,symbolHash) then makeUniqueId (s ^ "'")
                else s

        val _ = if wasError() then raise Semantic else ()

        val numTerms = SymbolHash.size termHash
        val numNonterms = SymbolHash.size symbolHash - numTerms

        val symError = fn sym => fn err => fn symbol =>
          error (symbolPos symbol)
                (symbolName symbol^" in "^err^" is not defined as a " ^ sym)

        val termNum : string -> Header.symbol -> term =
          let val termError = symError "terminal"
          in fn stmt =>
             let val stmtError = termError stmt
             in fn symbol =>
                case SymbolHash.find(symbolName symbol,symbolHash)
                of NONE => (stmtError symbol; T ~1)
                 | SOME i => T (if i<numTerms then i
                                else (stmtError symbol; ~1))
             end
          end

        val nontermNum : string -> Header.symbol -> nonterm =
          let val nontermError = symError "nonterminal"
          in fn stmt =>
             let val stmtError = nontermError stmt
             in fn symbol =>
                case SymbolHash.find(symbolName symbol,symbolHash)
                of NONE => (stmtError symbol; NT ~1)
                 | SOME i => if i>=numTerms then NT (i-numTerms)
                             else (stmtError symbol;NT ~1)
             end
          end

        val symbolNum : string -> Header.symbol -> Grammar.symbol =
          let val symbolError = symError "symbol"
          in fn stmt =>
             let val stmtError = symbolError stmt
             in fn symbol =>
                case SymbolHash.find(symbolName symbol,symbolHash)
                of NONE => (stmtError symbol; NONTERM (NT ~1))
                 | SOME i => if i>=numTerms then NONTERM(NT (i-numTerms))
                             else TERM(T i)
             end
          end

(* map all symbols in the following values to terminals and check that
   the symbols are defined as terminals:

        eop : symbol list
        keyword: symbol list
        prec: (lexvalue * (symbol list)) list
        change: (symbol list * symbol list) list
*)

        val eop = map (termNum "%eop") eop
        val keyword = map (termNum "%keyword") keyword
        val prec = map (fn (a,l) =>
                        (a,case a
                           of LEFT => map (termNum "%left") l
                            | RIGHT => map (termNum "%right") l
                            | NONASSOC => map (termNum "%nonassoc") l
                        )) prec
        val change =
         let val mapTerm = termNum "%prefer, %subst, or %change"
         in map (fn (a,b) => (map mapTerm a, map mapTerm b)) change
         end
        val noshift = map (termNum "%noshift") noshift
        val value =
          let val mapTerm = termNum "%value"
          in map (fn (a,b) => (mapTerm a,b)) value
          end
        val (rules,_) =
           let val symbolNum = symbolNum "rule"
               val nontermNum = nontermNum "rule"
               val termNum = termNum "%prec tag"
           in List.foldr
                 (fn (rules, acc) =>
                   let val len = length rules in
                     List.foldr (fn ((RULE {lhs,rhs,code,prec},((l,n),n'))) =>
                                  (({lhs=nontermNum lhs,rhs=map symbolNum rhs,
                                     code=code,prec=case prec
                                                     of NONE => NONE
                                                      | SOME t => SOME (termNum t),
                                     rulenum=n, rulenum' = (n', len)} :: l, n - 1), n' - 1))
                                (acc, len)
                                rules
                     |> #1
                   end)
                 (nil, fold (curry op +) (map length rules) ~1)
                 rules
        end

        val _ = if wasError() then raise Semantic else ()

        (* termToString: map terminals back to strings *)

        val termToString =
           let val data = Array.array(numTerms,"")
               val unmap = fn (symbol,_) =>
                   let val name = symbolName symbol
                   in Array.update(data,
                             case SymbolHash.find(name,symbolHash) of
                                 SOME i => i
                               | NONE => raise Fail "termToString",
                             name)
                   end
               val _ = app unmap term
           in fn T i =>
                if DEBUG andalso (i<0 orelse i>=numTerms)
                  then "bogus-num" ^ (Int.toString i)
                  else data sub i
           end

        val nontermToString =
           let val data = Array.array(numNonterms,"")
               val unmap = fn (symbol,_) =>
                    let val name = symbolName symbol
                    in Array.update(data,
                              case SymbolHash.find(name,symbolHash) of
                                  SOME i => i-numTerms
                                | NONE => raise Fail "nontermToString",
                              name)
                    end
               val _ = app unmap nonterm
           in fn NT i =>
                if DEBUG andalso (i<0 orelse i>=numNonterms)
                  then "bogus-num" ^ (Int.toString i)
                  else data sub i
           end

(* create functions mapping terminals to precedence numbers and rules to
  precedence numbers.

  Precedence statements are listed in order of ascending (tighter binding)
  precedence in the specification.   We receive a list composed of pairs
  containing the kind of precedence (left,right, or assoc) and a list of
  terminals associated with that precedence.  The list has the same order as
  the corresponding declarations did in the specification.

  Internally, a tighter binding has a higher precedence number.  We give
  precedences using multiples of 3:

                p+2 = right associative (force shift of symbol)
                p+1 = precedence for rule
                p = left associative (force reduction of rule)

  Nonassociative terminals are given also given a precedence of p+1.  The
table generator detects when the associativity of a nonassociative terminal
is being used to resolve a shift/reduce conflict by checking if the
precedences of the rule and the terminal are equal.

  A rule is given the precedence of its rightmost terminal *)

        val termPrec =
            let val precData = Array.array(numTerms, NONE : int option)
                val addPrec = fn termPrec => fn term as (T i) =>
                   case precData sub i
                   of SOME _ =>
                     error {line = 1, col = 0} ("multiple precedences specified for terminal " ^
                            (termToString term))
                    | NONE => Array.update(precData,i,termPrec)
                val termPrec = fn ((LEFT,_) ,i) => i
                              | ((RIGHT,_),i) => i+2
                              | ((NONASSOC,l),i) => i+1
                val _ = List.foldl (fn (args as ((_,l),i)) =>
                                (app (addPrec (SOME (termPrec args))) l; i+3))
                          0 prec
           in fn (T i) =>
                if  DEBUG andalso (i < 0 orelse i >= numTerms) then
                        NONE
                else precData sub i
           end

        val elimAssoc =  fn i => (i - (i mod 3) + 1)
        val rulePrec =
           let fun findRightTerm (nil,r) = r
                 | findRightTerm (TERM t :: tail,r) =
                                 findRightTerm(tail,SOME t)
                 | findRightTerm (_ :: tail,r) = findRightTerm(tail,r)
           in fn rhs =>
                 case findRightTerm(rhs,NONE)
                 of NONE => NONE
                  | SOME term =>
                       case termPrec term
                       of SOME i => SOME  (elimAssoc i)
                        | a => a
           end

        val grammarRules =
          let val conv = fn {lhs,rhs,code,prec,rulenum,rulenum'} =>
                {lhs=lhs,rhs =rhs,precedence=
                        case prec
                          of SOME t => (case termPrec t
                                        of SOME i => SOME(elimAssoc i)
                                         | a => a)
                           | _ => rulePrec rhs,
                 rulenum=rulenum, rulenum' = rulenum'}
          in map conv rules
          end

    (* get start symbol *)

        val start =
         case start
           of NONE => #lhs (hd grammarRules)
            | SOME name =>
                nontermNum "%start" name

        val symbolType =
           let val data = Array.array(numTerms+numNonterms,NONE : ty option)
               fun unmap (symbol,ty) =
                   Array.update(data,
                          case SymbolHash.find(symbolName symbol,symbolHash) of
                              SOME i => i
                            | NONE => raise Fail "symbolType",
                          ty)
               val _ = (app unmap term; app unmap nonterm)
           in fn NONTERM(NT i) =>
                if DEBUG andalso (i<0 orelse i>=numNonterms)
                  then NONE
                  else data sub (i+numTerms)
               | TERM (T i) =>
                if DEBUG andalso (i<0 orelse i>=numTerms)
                  then NONE
                  else data sub i
           end

        val symbolToString =
             fn NONTERM i => nontermToString i
              | TERM i => termToString i

        val grammar  = GRAMMAR {rules=grammarRules,
                                 terms=numTerms,nonterms=numNonterms,
                                 eop = eop, start=start,noshift=noshift,
                                 termToString = termToString,
                                 nontermToString = nontermToString,
                                 precedence = termPrec}

        val name' = case name
                    of NONE => ""
                     | SOME s => symbolName s

        val names = NAMES {miscStruct=name' ^ "_Fun",
                           valueStruct=name' ^ "_Rule",
                           valueMonadStruct=name' ^ "_Rule_Wrap",
                           tableStruct="LALR_Table",
                           tokenStruct="Tokens",
                           actionsStruct="Actions",
                           ecStruct="EC",
                           arg= #1 arg_decl,
                           tokenSig = name' ^ "_TOKENS",
                           miscSig = name' ^ "_LRVALS",
                           dataStruct = "ParserData",
                           dataSig = if pureActions then "PARSER_DATA1" else "PARSER_DATA2"}

        val (table,stateErrs,corePrint,errs) =
                 MakeTable.mkTable(grammar,defaultReductions)

        val entries = ref 0 (* save number of action table entries here *)

    in  let val result = TextIO.openOut (spec ^ ".sml")
            val sigs = TextIO.openOut (spec ^ ".sig")
            val specFile = OS.Path.file spec
            val resultFile = specFile ^ ".sml"
            val line = ref 1
            val col = ref 0
            val pr = fn s => TextIO.output(result,s)
            val say = fn s =>
               (CharVector.app (fn #"\n" => (line := !line + 1 ; col := 0)
                                 | _     => col := !col + 1)
                               s
                ; pr s)
            val saydot = fn s => (say (s ^ "."))
            val sayln = fn t => (say t; say "\n")
            fun fmtLineDir {line, col} path =
               String.concat ["(*#line ", Int.toString line, ".",
                              Int.toString (col+1), " \"", path, "\"*)"]
            val fmtPos =
               fn NONE => (fmtLineDir {line = !line, col = 0} resultFile) ^ "\n"
                | SOME pos => fmtLineDir pos specFile
            val termvoid = makeUniqueId "VOID"
            val ntvoid = makeUniqueId "ntVOID"
            val hasType = fn s => case symbolType s
                                  of NONE => false
                                   | _ => true
            val terms = let fun f n = if n=numTerms then nil
                                      else (T n) :: f(n+1)
                        in f 0
                        end
            val values = VALS {say=say,sayln=sayln,saydot=saydot,fmtPos=fmtPos,
                               termvoid=termvoid, ntvoid = ntvoid,
                               hasType=hasType, pos_type = pos_type,
                               arg_type = #2 arg_decl,
                               start=start,pureActions=pureActions,
                               termToString=termToString,
                               symbolToString=symbolToString,term=term,
                               nonterm=nonterm,terms=terms,
                               tokenInfo=token_sig_info_decl}

            val (NAMES {miscStruct,tableStruct,dataStruct,tokenSig,tokenStruct,dataSig,...}) = names
         in case header_decl
            of NONE => (say "functor "; say miscStruct;
                        sayln "(structure Token : TOKEN)";
                        say " : sig structure ";
                        say dataStruct;
                        say " : "; sayln dataSig;
                        say "       structure ";
                        say tokenStruct; say " : "; sayln tokenSig;
                        sayln "   end")
             | SOME s => say s;
            sayln " = ";
            sayln "struct";
            sayln "structure Header = ";
            sayln "struct";
            say (fmtPos (SOME {line = 1, col = 1}));
            sayln header;
            say (fmtPos NONE);
            sayln "end";
            sayln ("structure " ^ dataStruct ^ "=");
            sayln "struct";
            sayln "structure LALR_Table = Token.LALR_Table";
            sayln "structure Token = Token";
            sayln "local open LALR_Table in ";
            entries := PrintStruct.makeStruct{table=table,print=say,
                                              name = "table",
                                              verbose=verbose};
            sayln "end";
            printTypes2(values,names,symbolType);
            printEC (keyword,change,noshift,value,values,names);
            printAction(rules,values,names);
            sayln "end";
            printTokenStruct(values,names);
            sayln "end";
            printSigs(rules,values,names,fn s => TextIO.output(sigs,s), fmtPos, header);
            TextIO.closeOut sigs;
            TextIO.closeOut result;
            MakeTable.Errs.printSummary (fn s => TextIO.output(TextIO.stdOut,s)) errs
        end;
        if verbose then
         let val f = TextIO.openOut (spec ^ ".desc")
             val say = fn s=> TextIO.output(f,s)
             val printRule =
                let val rules = Array.fromList grammarRules
                in fn say =>
                   let val prRule = fn {lhs,rhs,precedence,rulenum,rulenum'} =>
                     ((say o nontermToString) lhs; say " : ";
                      app (fn s => (say (symbolToString s); say " ")) rhs)
                   in fn i => prRule (rules sub i)
                   end
                end
         in Verbose.printVerbose
            {termToString=termToString,nontermToString=nontermToString,
             table=table, stateErrs=stateErrs,errs = errs,entries = !entries,
             print=say, printCores=corePrint,printRule=printRule};
            TextIO.closeOut f
         end
        else ()
    end

    val parseGen = fn spec =>
                let val (result,inputSource) = ParseGenParser.parse spec
                in make_parser(getResult result,spec,Header.error inputSource,
                                errorOccurred inputSource)
                end
end;
