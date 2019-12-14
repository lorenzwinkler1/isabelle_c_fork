(*
 * Portions Copyright 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 * Portions Copyright 2016-2017 Nanyang Technological University, Singapore
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure StrictCParser =
struct

structure StrictCLrVals = StrictCLrValsFun(structure Token = LrParser.Token)

structure StrictCLex = StrictCLexFun(structure Tokens = StrictCLrVals.Tokens);

structure StrictCParser =
  JoinWithArg(structure LrParser = LrParser
              structure ParserData = StrictCLrVals.ParserData
              structure Lex = StrictCLex)

fun invoke lookahead pi lexstream = let
  fun print_error (s,lpos,rpos) = Feedback.errorStr'(lpos,rpos,s)
in
  (#1 (StrictCParser.parse(lookahead,lexstream,print_error,pi)), !Feedback.numErrors)
end

val last_parsed = Synchronized.var "last parsed" ("", [])
val last_parsed' = Synchronized.var "last parsed'" []

datatype input = File of Token.file * string (* filename *)
               | Filename of string (* filename *)
               | Source of Input.source

fun parse maybe_c11 docpp0 error_lookahead (includes : string list) (input : input) thy =
  let
    fun docpp f =
      let val cpped_input = docpp0 { includes = includes, input = input }
          val res = f (case cpped_input of NONE => (NONE, input) | SOME fname => (SOME input, Filename fname))
          val _ = case cpped_input of
                    SOME cpped_fname => OS.FileSys.remove cpped_fname
                  | _ => ()
      in res end

    fun drain lines =
      let val lines = ref lines
      in fn _ => case !lines of [] => ""
                              | x :: xs => (lines := xs; x)
      end

    fun open_close f =
      fn (_, File (file, fname)) =>
          f (drain (map (fn x => x ^ "\n") (#lines file)))
            fname
       | (_, Filename fic) =>
          let val istream = TextIO.openIn fic
              val res = f (fn _ => inputLine istream) fic
              val _ = TextIO.closeIn istream
          in res end
       | (_, Source src) =>
          f (drain [Input.source_content src |> #1]) (C_Env.encode_positions [Input.pos_of src])

    fun parse_without_c11 thy = 
      docpp
        (open_close (fn istream => fn fname =>
          let
            val _ = Feedback.numErrors := 0 (* FIXME - global reference *)
            val lexarg = StrictCLex.UserDeclarations.new_state fname
            val lexer = StrictCParser.makeLexer istream lexarg
            val pos = #source lexarg
          in invoke error_lookahead pos lexer |>> pair fname end))
      |>> (fn (fname, v) => Synchronized.change_result last_parsed (K (v, (fname, v))))
      |> curry swap thy

    (* Command.read_file_node' *)
    fun read_file_node' src_path =
      let
        val full_path = File.check_file src_path;
        val text = File.read full_path;
        val lines = split_lines text;
        val digest = SHA1.digest text;
      in {src_path = src_path, lines = lines, digest = digest, pos = Path.position full_path} end

    fun parse_with_c11 thy =
      docpp
        (fn (input, cpped_input) =>
          let val C_exec =
                Context.theory_map o (fn Filename cpped_fname =>
                                           C_Outer_File.command_c (read_file_node' (Path.explode cpped_fname))
                                       | File (file, _) => C_Outer_File.command_c file
                                       | Source src => C_Module.C src)
              val thy = (case input of SOME input => C_exec input | NONE => I) thy
              val f_accept = C_Module.Data_Accept.get (Context.Theory thy)
          in thy
             |> Context.theory_map
                  (C_Module.Data_Accept.map
                    (fn f => fn ast => fn env_lang =>
                      f ast env_lang
                      #> tap (fn _ =>
                              Synchronized.change
                                last_parsed'
                                (K (C_Ast.main ( ast |> C_Grammar_Rule.start_happy1 |> the
                                               , ( map_filter (fn C_Scan.Left {body_begin, body, body_end, range, ...} =>
                                                                  SOME (C_Grammar_Rule_Lib.make_comment body_begin body body_end range)
                                                                | _ => NONE)
                                                              (#stream_ignored env_lang |> rev)
                                                 , [])))))))
              |> C_exec cpped_input
              |> pair (Synchronized.value last_parsed') o Context.theory_map (C_Module.Data_Accept.put f_accept)
          end)
      |>> (fn x => (IsarPreInstall.of_c_ast x, 0))
  in
    case maybe_c11 of
      SOME true => 
        let val ((res2, err2), thy) = parse_with_c11 thy
            val ((res1, err1), thy) = parse_without_c11 thy
            val rm = StmtDecl.rm_region_ext_decl_list
            val r1 = rm res1
            val r2 = rm res2
        in if #2 (fold2 (fn r1 => fn r2 => fn (n, b) => 
                          (n + 1,
                           if r1 = r2 then b
                           else if ((@{make_string}) r1) = ((@{make_string}) r2)
                           then let val _ = tracing ("Equal with make_string comparison at " ^ Int.toString n)
                                in b end
                           else let val _ = Output.information ("Differing at " ^ Int.toString n)
                                in false end))
                        r1 r2 (0, true))
           then ((res1, err1 + err2), thy)
           else error "Parsed values are not similar." end
    | SOME false => parse_without_c11 thy
    | _ => parse_with_c11 thy
  end


end;
