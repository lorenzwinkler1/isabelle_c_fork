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

fun parse maybe_c11 docpp0 error_lookahead (includes : string list) (file, fname) thy =
  let
    fun docpp files f =
      let val cpped_fname = docpp0 files
          val res = f cpped_fname
          val _ = if cpped_fname <> fname then
                    OS.FileSys.remove cpped_fname
                  else ()
      in res end
  
    fun open_close f fic =
      let val istream = TextIO.openIn fic
          val res = f istream
          val _ = TextIO.closeIn istream
      in res end
  
    fun parse_without_c11 thy = 
      docpp {includes=includes,filename=fname}
        (open_close (fn istream =>
          let
            val _ = Feedback.numErrors := 0 (* FIXME - global reference *)
            val lexarg = StrictCLex.UserDeclarations.new_state fname
            val lexer = StrictCParser.makeLexer (fn _ => inputLine istream) lexarg
            val pos = #source lexarg
          in invoke error_lookahead pos lexer end))
      |>> (fn v => Synchronized.change_result last_parsed (K (v, (fname, v))))
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
      docpp {includes=includes,filename=fname}
        (fn cpped_fname =>
          let val thy = Context.theory_map (C_Outer_File.command0 file) thy
              val thy = Context.theory_map (C_Outer_File.command0 (read_file_node' (Path.explode cpped_fname))) thy
              val (res, l_comm) = hd (C_Module.get_module thy |> #1)
          in (C_Ast.main (res, (map_filter (fn C_Scan.Left {body_begin, body, body_end, range, ...} =>
                                               SOME (C_Grammar_Rule_Lib.make_comment body_begin body body_end range)
                                             | _ => NONE) l_comm, [])), thy) end)
      |>> (fn x => (IsarPreInstall.of_c_ast x, 0))
  in
    case maybe_c11 of
      SOME true => 
        let val ((res1, err1), thy) = parse_without_c11 thy
            val ((res2, err2), thy) = parse_with_c11 thy
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
