(******************************************************************************
 * Citadelle
 *
 * Copyright (c) 2011-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
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

section\<open>Initializing the Printer\<close>

theory  Printer_init
imports Isabelle_Meta_Model.Init
        Isabelle_Meta_Model.Isabelle_code_runtime
  keywords "lazy_code_printing" "apply_code_printing" "apply_code_printing_reflect"
           :: thy_decl
begin

ML \<open>
structure Isabelle_Code_Target =
struct
(*  Title:      Tools/Code/code_target.ML
    Author:     Florian Haftmann, TU Muenchen

Generic infrastructure for target language data.
*)

open Basic_Code_Symbol;
open Basic_Code_Thingol;







(** checking and parsing of symbols **)






val parse_classrel_ident = Parse.class --| \<^keyword>\<open><\<close> -- Parse.class;



val parse_inst_ident = Parse.name --| \<^keyword>\<open>::\<close> -- Parse.class;







(** theory data **)









(** serializers **)



(** serializer usage **)

(* technical aside: pretty printing width *)



(* montage *)



(* code generation *)

fun prep_destination (location, source) =
  let
    val s = Input.string_of source
    val pos = Input.pos_of source
    val delimited = Input.is_delimited source
  in
    if location = {physical = false}
    then (location, Path.explode_pos (s, pos))
    else
      let
        val _ =
          if s = ""
          then error ("Bad bad empty " ^ Markup.markup Markup.keyword2 "file" ^ " argument")
          else ();
        val _ =
          legacy_feature
            (Markup.markup Markup.keyword1 "export_code" ^ " with " ^
              Markup.markup Markup.keyword2 "file" ^ " argument" ^ Position.here pos);
        val _ = Position.report pos (Markup.language_path delimited);
        val path = #1 (Path.explode_pos (s, pos));
        val _ = Position.report pos (Markup.path (Path.implode_symbolic path));
      in (location, (path, pos)) end
  end;


fun export_code_cmd all_public raw_cs seris lthy =
  let
    val cs = Code_Thingol.read_const_exprs lthy raw_cs;
  in Code_Target.export_code all_public cs ((map o apfst o apsnd o Option.map) prep_destination seris) lthy end;



(** serializer configuration **)

(* reserved symbol names *)



(* checking of syntax *)



(* custom symbol names *)



(* custom printings *)



(* concrete syntax *)



(** Isar setup **)

val (constantK, type_constructorK, type_classK, class_relationK, class_instanceK, code_moduleK) =
  (\<^keyword>\<open>constant\<close>, \<^keyword>\<open>type_constructor\<close>, \<^keyword>\<open>type_class\<close>,
    \<^keyword>\<open>class_relation\<close>, \<^keyword>\<open>class_instance\<close>, \<^keyword>\<open>code_module\<close>);

val parse_constants = constantK |-- Scan.repeat1 Parse.term >> map Constant;

val parse_type_constructors = type_constructorK |-- Scan.repeat1 Parse.type_const >> map Type_Constructor;

val parse_classes = type_classK |-- Scan.repeat1 Parse.class >> map Type_Class;

val parse_class_relations = class_relationK |-- Scan.repeat1 parse_classrel_ident >> map Class_Relation;

val parse_instances = class_instanceK |-- Scan.repeat1 parse_inst_ident >> map Class_Instance;

val parse_simple_symbols : (string, string, string, string * string, string * string, string)
                           Basic_Code_Symbol.attr list parser
                         = Scan.repeats1 (parse_constants || parse_type_constructors || parse_classes
  || parse_class_relations || parse_instances);

fun parse_single_symbol_pragma parse_keyword parse_isa parse_target =
  parse_keyword |-- Parse.!!! (parse_isa --| (\<^keyword>\<open>\<rightharpoonup>\<close> || \<^keyword>\<open>=>\<close>)
    -- Parse.and_list1 (\<^keyword>\<open>(\<close> |-- (Parse.name --| \<^keyword>\<open>)\<close> -- Scan.option parse_target)));

fun parse_symbol_pragma parse_const parse_tyco parse_class parse_classrel parse_inst parse_module =
  parse_single_symbol_pragma constantK Parse.term parse_const
    >> Constant
  || parse_single_symbol_pragma type_constructorK Parse.type_const parse_tyco
    >> Type_Constructor
  || parse_single_symbol_pragma type_classK Parse.class parse_class
    >> Type_Class
  || parse_single_symbol_pragma class_relationK parse_classrel_ident parse_classrel
    >> Class_Relation
  || parse_single_symbol_pragma class_instanceK parse_inst_ident parse_inst
    >> Class_Instance
  || parse_single_symbol_pragma code_moduleK Parse.name parse_module
    >> Module;

fun parse_symbol_pragmas parse_const parse_tyco parse_class parse_classrel parse_inst parse_module =
  Parse.enum1 "|" (Parse.group (fn () => "code symbol pragma")
    (parse_symbol_pragma parse_const parse_tyco parse_class parse_classrel parse_inst parse_module));

end
\<close>

ML \<open>
structure Code_printing = struct
datatype code_printing = Code_printing of
     (string * (string * Code_Printer.raw_const_syntax option) list,
      string * (string * Code_Printer.tyco_syntax option) list,
      string * (string * string option) list,
      (string * string) * (string * unit option) list,
      (string * string) * (string * unit option) list,
      string * (string * (string * (string, string, string, string * string, string * string, string)
                                   Basic_Code_Symbol.attr list)
                         option)
               list)
      Basic_Code_Symbol.attr
      list

structure Data_code = Theory_Data
  (type T = code_printing list Symtab.table
   val empty = Symtab.empty
   val merge = Symtab.merge (K true))

val code_empty = ""

val () =
  Outer_Syntax.command @{command_keyword lazy_code_printing} "declare dedicated printing for code symbols"
    (Isabelle_Code_Target.parse_symbol_pragmas (Code_Printer.parse_const_syntax) (Code_Printer.parse_tyco_syntax)
      Parse.string (Parse.minus >> K ()) (Parse.minus >> K ())
      (Parse.text -- Scan.optional (\<^keyword>\<open>for\<close> |-- Isabelle_Code_Target.parse_simple_symbols) [])
      >> (fn code =>
            Toplevel.theory (Data_code.map (Symtab.map_default (code_empty, []) (fn l => Code_printing code :: l)))))

fun apply_code_printing thy =
    (case Symtab.lookup (Data_code.get thy) code_empty of SOME l => rev l | _ => [])
 |> (fn l => fold (fn Code_printing l => fold Code_Target.set_printings l) l thy)

val () =
  Outer_Syntax.command @{command_keyword apply_code_printing} "apply dedicated printing for code symbols"
    (Parse.$$$ "(" -- Parse.$$$ ")" >> K (Toplevel.theory apply_code_printing))

fun reflect_ml source thy =
  case ML_Context.exec (fn () =>
            ML_Context.eval_source (ML_Compiler.verbose false ML_Compiler.flags) source) (Context.Theory thy) of
    Context.Theory thy => thy

fun apply_code_printing_reflect thy =
    (case Symtab.lookup (Data_code.get thy) code_empty of SOME l => rev l | _ => [])
 |> (fn l => fold (fn Code_printing l =>
      fold (fn Code_Symbol.Module (_, l) =>
                 fold (fn ("SML", SOME (txt, _)) => reflect_ml (Input.source false txt (Position.none, Position.none))
                        | _ => I) l
             | _ => I) l) l thy)

val () =
  Outer_Syntax.command @{command_keyword apply_code_printing_reflect} "apply dedicated printing for code symbols"
    (Parse.ML_source >> (fn src => Toplevel.theory (apply_code_printing_reflect o reflect_ml src)))

end
\<close>

ML_file "~~/src/Doc/antiquote_setup.ML"

text \<open>
\begin{matharray}{rcl}
  @{command_def lazy_code_printing} & : & @{text "theory \<rightarrow> theory"} \\
  @{command_def apply_code_printing} & : & @{text "theory \<rightarrow> theory"} \\
  @{command_def apply_code_printing_reflect} & : & @{text "local_theory \<rightarrow> local_theory"}
\end{matharray}

@{rail \<open>
  @@{command lazy_code_printing}
      ( ( printing_const | printing_typeconstructor
      | printing_class | printing_class_relation | printing_class_instance
      | printing_module ) + '|' )
  ;
  @@{command apply_code_printing} '(' ')'
  ;
  @@{command apply_code_printing_reflect} text
  ;
\<close>}
\<close>

text\<open>
@{command lazy_code_printing} has the same semantics as @{command code_printing}
or @{command ML},
except that no side effects occur until we give more details about its intended future semantics:
this will be precised by calling
@{command apply_code_printing} or @{command apply_code_printing_reflect}.
\<close>

text\<open>
@{command apply_code_printing} repeatedly calls @{command code_printing}
to all previously registered elements with @{command lazy_code_printing} (the order is preserved).
\<close>

text\<open>
@{command apply_code_printing_reflect} repeatedly calls @{command ML}
to all previously registered elements with @{command lazy_code_printing} (the order is preserved).
As a consequence, code for other targets (Haskell, OCaml, Scala) are ignored.
Moreover before the execution of the overall,
it is possible to give an additional piece of SML code as argument to priorly execute.
\<close>

text\<open>At the time of writing, the following target languages supported
     by Isabelle are also supported by the meta-compiler:
     Haskell, OCaml, Scala, SML.\<close>

subsection\<open>Kernel Code for Target Languages\<close>

  (* We put in 'CodeConst' functions using characters
     not allowed in a Isabelle 'code_const' expr
     (e.g. '_', '"', ...) *)

lazy_code_printing code_module "CodeType" \<rightharpoonup> (Haskell) \<open>
  type MlInt = Integer
; type MlMonad a = IO a
\<close> | code_module "CodeConst" \<rightharpoonup> (Haskell) \<open>
  import System.Directory
; import System.IO
; import qualified CodeConst.Printf

; outFile1 f file = (do
  fileExists <- doesFileExist file
  if fileExists then error ("File exists " ++ file ++ "\n") else do
    h <- openFile file WriteMode
    f (\pat -> hPutStr h . CodeConst.Printf.sprintf1 pat)
    hClose h)

; outStand1 :: ((String -> String -> IO ()) -> IO ()) -> IO ()
; outStand1 f = f (\pat -> putStr . CodeConst.Printf.sprintf1 pat)
\<close> | code_module "CodeConst.Monad" \<rightharpoonup> (Haskell) \<open>
  bind a = (>>=) a
; return :: a -> IO a
; return = Prelude.return
\<close> | code_module "CodeConst.Printf" \<rightharpoonup> (Haskell) \<open>
  import Text.Printf
; sprintf0 = id

; sprintf1 :: PrintfArg a => String -> a -> String
; sprintf1 = printf

; sprintf2 :: PrintfArg a => PrintfArg b => String -> a -> b -> String
; sprintf2 = printf

; sprintf3 :: PrintfArg a => PrintfArg b => PrintfArg c => String -> a -> b -> c -> String
; sprintf3 = printf

; sprintf4 :: PrintfArg a => PrintfArg b => PrintfArg c => PrintfArg d => String -> a -> b -> c -> d -> String
; sprintf4 = printf

; sprintf5 :: PrintfArg a => PrintfArg b => PrintfArg c => PrintfArg d => PrintfArg e => String -> a -> b -> c -> d -> e -> String
; sprintf5 = printf
\<close> | code_module "CodeConst.String" \<rightharpoonup> (Haskell) \<open>
  concat s [] = []
; concat s (x : xs) = x ++ concatMap ((++) s) xs
\<close> | code_module "CodeConst.Sys" \<rightharpoonup> (Haskell) \<open>
  import System.Directory
; isDirectory2 = doesDirectoryExist
\<close> | code_module "CodeConst.To" \<rightharpoonup> (Haskell) \<open>
  nat = id

\<close> | code_module "" \<rightharpoonup> (OCaml) \<open>
module CodeType = struct
  type mlInt = int

  type 'a mlMonad = 'a option
end

module CodeConst = struct
  let outFile1 f file =
    try
      let () = if Sys.file_exists file then Printf.eprintf "File exists \"%S\"\n" file else () in
      let oc = open_out file in
      let b = f (fun s a -> try Some (Printf.fprintf oc s a) with _ -> None) in
      let () = close_out oc in
      b
    with _ -> None

  let outStand1 f =
    f (fun s a -> try Some (Printf.fprintf stdout s a) with _ -> None)

  module Monad = struct
    let bind = function
        None -> fun _ -> None
      | Some a -> fun f -> f a
    let return a = Some a
  end

  module Printf = struct
    include Printf
    let sprintf0 = sprintf
    let sprintf1 = sprintf
    let sprintf2 = sprintf
    let sprintf3 = sprintf
    let sprintf4 = sprintf
    let sprintf5 = sprintf
  end

  module String = String

  module Sys = struct open Sys
    let isDirectory2 s = try Some (is_directory s) with _ -> None
  end

  module To = struct
    let nat big_int x = Big_int.int_of_big_int (big_int x)
  end
end

\<close> | code_module "" \<rightharpoonup> (Scala) \<open>
object CodeType {
  type mlMonad [A] = Option [A]
  type mlInt = Int
}

object CodeConst {
  def outFile1 [A] (f : (String => A => Option [Unit]) => Option [Unit], file0 : String) : Option [Unit] = {
    val file = new java.io.File (file0)
    if (file .isFile) {
      None
    } else {
      val writer = new java.io.PrintWriter (file)
      f ((fmt : String) => (s : A) => Some (writer .write (fmt .format (s))))
      Some (writer .close ())
    }
  }

  def outStand1 [A] (f : (String => A => Option [Unit]) => Option [Unit]) : Option[Unit] = {
    f ((fmt : String) => (s : A) => Some (print (fmt .format (s))))
  }

  object Monad {
    def bind [A, B] (x : Option [A], f : A => Option [B]) : Option [B] = x match {
      case None => None
      case Some (a) => f (a)
    }
    def Return [A] (a : A) = Some (a)
  }
  object Printf {
    def sprintf0 (x0 : String) = x0
    def sprintf1 [A1] (fmt : String, x1 : A1) = fmt .format (x1)
    def sprintf2 [A1, A2] (fmt : String, x1 : A1, x2 : A2) = fmt .format (x1, x2)
    def sprintf3 [A1, A2, A3] (fmt : String, x1 : A1, x2 : A2, x3 : A3) = fmt .format (x1, x2, x3)
    def sprintf4 [A1, A2, A3, A4] (fmt : String, x1 : A1, x2 : A2, x3 : A3, x4 : A4) = fmt .format (x1, x2, x3, x4)
    def sprintf5 [A1, A2, A3, A4, A5] (fmt : String, x1 : A1, x2 : A2, x3 : A3, x4 : A4, x5 : A5) = fmt .format (x1, x2, x3, x4, x5)
  }
  object String {
    def concat (s : String, l : List [String]) = l filter (_ .nonEmpty) mkString s
  }
  object Sys {
    def isDirectory2 (s : String) = Some (new java.io.File (s) .isDirectory)
  }
  object To {
    def nat [A] (f : A => BigInt, x : A) = f (x) .intValue ()
  }
}

\<close> | code_module "" \<rightharpoonup> (SML) \<open>
structure CodeType = struct
  type mlInt = string
  type 'a mlMonad = 'a option
end

structure CodeConst = struct
  structure Monad = struct
    val bind = fn
        NONE => (fn _ => NONE)
      | SOME a => fn f => f a
    val return = SOME
  end

  structure Printf = struct
    local
      fun sprintf s l =
        case String.fields (fn #"%" => true | _ => false) s of
          [] => ""
        | [x] => x
        | x :: xs =>
            let fun aux acc l_pat l_s =
              case l_pat of
                [] => rev acc
              | x :: xs => aux (String.extract (x, 1, NONE) :: hd l_s :: acc) xs (tl l_s) in
            String.concat (x :: aux [] xs l)
      end
    in
      fun sprintf0 s_pat = s_pat
      fun sprintf1 s_pat s1 = sprintf s_pat [s1]
      fun sprintf2 s_pat s1 s2 = sprintf s_pat [s1, s2]
      fun sprintf3 s_pat s1 s2 s3 = sprintf s_pat [s1, s2, s3]
      fun sprintf4 s_pat s1 s2 s3 s4 = sprintf s_pat [s1, s2, s3, s4]
      fun sprintf5 s_pat s1 s2 s3 s4 s5 = sprintf s_pat [s1, s2, s3, s4, s5]
    end
  end

  structure String = struct
    val concat = String.concatWith
  end

  structure Sys = struct
    val isDirectory2 = SOME o File.is_dir o Path.explode handle ERROR _ => K NONE
  end

  structure To = struct
    fun nat f = Int.toString o f
  end

  fun outFile1 f file =
    let
      val pfile = Path.explode file
      val () = if File.exists pfile then error ("File exists \"" ^ file ^ "\"\n") else ()
      val oc = Unsynchronized.ref []
      val _ = f (fn a => fn b => SOME (oc := Printf.sprintf1 a b :: (Unsynchronized.! oc))) in
      SOME (File.write_list pfile (rev (Unsynchronized.! oc))) handle _ => NONE
    end

  fun outStand1 f = outFile1 f (Unsynchronized.! stdout_file)
end

\<close>

subsection\<open>Interface with Types\<close>

datatype ml_int = ML_int
code_printing type_constructor ml_int \<rightharpoonup> (Haskell) "CodeType.MlInt" \<comment> \<open>syntax!\<close>
            | type_constructor ml_int \<rightharpoonup> (OCaml) "CodeType.mlInt"
            | type_constructor ml_int \<rightharpoonup> (Scala) "CodeType.mlInt"
            | type_constructor ml_int \<rightharpoonup> (SML) "CodeType.mlInt"

datatype 'a ml_monad = ML_monad 'a
code_printing type_constructor ml_monad \<rightharpoonup> (Haskell) "CodeType.MlMonad _" \<comment> \<open>syntax!\<close>
            | type_constructor ml_monad \<rightharpoonup> (OCaml) "_ CodeType.mlMonad"
            | type_constructor ml_monad \<rightharpoonup> (Scala) "CodeType.mlMonad [_]"
            | type_constructor ml_monad \<rightharpoonup> (SML) "_ CodeType.mlMonad"

(* *)

type_synonym ml_string = String.literal

subsection\<open>Interface with Constants\<close>

text\<open>module CodeConst\<close>

consts out_file1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit ml_monad) \<comment> \<open>fprintf\<close> \<Rightarrow> unit ml_monad) \<Rightarrow> ml_string \<Rightarrow> unit ml_monad"
code_printing constant out_file1 \<rightharpoonup> (Haskell) "CodeConst.outFile1"
            | constant out_file1 \<rightharpoonup> (OCaml) "CodeConst.outFile1"
            | constant out_file1 \<rightharpoonup> (Scala) "CodeConst.outFile1"
            | constant out_file1 \<rightharpoonup> (SML) "CodeConst.outFile1"

consts out_stand1 :: "((ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> unit ml_monad) \<comment> \<open>fprintf\<close> \<Rightarrow> unit ml_monad) \<Rightarrow> unit ml_monad"
code_printing constant out_stand1 \<rightharpoonup> (Haskell) "CodeConst.outStand1"
            | constant out_stand1 \<rightharpoonup> (OCaml) "CodeConst.outStand1"
            | constant out_stand1 \<rightharpoonup> (Scala) "CodeConst.outStand1"
            | constant out_stand1 \<rightharpoonup> (SML) "CodeConst.outStand1"

text\<open>module Monad\<close>

consts bind :: "'a ml_monad \<Rightarrow> ('a \<Rightarrow> 'b ml_monad) \<Rightarrow> 'b ml_monad"
code_printing constant bind \<rightharpoonup> (Haskell) "CodeConst.Monad.bind"
            | constant bind \<rightharpoonup> (OCaml) "CodeConst.Monad.bind"
            | constant bind \<rightharpoonup> (Scala) "CodeConst.Monad.bind"
            | constant bind \<rightharpoonup> (SML) "CodeConst.Monad.bind"

consts return :: "'a \<Rightarrow> 'a ml_monad"
code_printing constant return \<rightharpoonup> (Haskell) "CodeConst.Monad.return"
            | constant return \<rightharpoonup> (OCaml) "CodeConst.Monad.return"
            | constant return \<rightharpoonup> (Scala) "CodeConst.Monad.Return" \<comment> \<open>syntax!\<close>
            | constant return \<rightharpoonup> (SML) "CodeConst.Monad.return"

text\<open>module Printf\<close>

consts sprintf0 :: "ml_string \<Rightarrow> ml_string"
code_printing constant sprintf0 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf0"
            | constant sprintf0 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf0"
            | constant sprintf0 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf0"
            | constant sprintf0 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf0"

consts sprintf1 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> ml_string"
code_printing constant sprintf1 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf1"
            | constant sprintf1 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf1"
            | constant sprintf1 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf1"
            | constant sprintf1 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf1"

consts sprintf2 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> ml_string"
code_printing constant sprintf2 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf2"
            | constant sprintf2 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf2"
            | constant sprintf2 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf2"
            | constant sprintf2 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf2"

consts sprintf3 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> ml_string"
code_printing constant sprintf3 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf3"
            | constant sprintf3 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf3"
            | constant sprintf3 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf3"
            | constant sprintf3 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf3"

consts sprintf4 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> ml_string"
code_printing constant sprintf4 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf4"
            | constant sprintf4 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf4"
            | constant sprintf4 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf4"
            | constant sprintf4 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf4"

consts sprintf5 :: "ml_string \<Rightarrow> '\<alpha>1 \<Rightarrow> '\<alpha>2 \<Rightarrow> '\<alpha>3 \<Rightarrow> '\<alpha>4 \<Rightarrow> '\<alpha>5 \<Rightarrow> ml_string"
code_printing constant sprintf5 \<rightharpoonup> (Haskell) "CodeConst.Printf.sprintf5"
            | constant sprintf5 \<rightharpoonup> (OCaml) "CodeConst.Printf.sprintf5"
            | constant sprintf5 \<rightharpoonup> (Scala) "CodeConst.Printf.sprintf5"
            | constant sprintf5 \<rightharpoonup> (SML) "CodeConst.Printf.sprintf5"

text\<open>module String\<close>

consts String_concat :: "ml_string \<Rightarrow> ml_string list \<Rightarrow> ml_string"
code_printing constant String_concat \<rightharpoonup> (Haskell) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (OCaml) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (Scala) "CodeConst.String.concat"
            | constant String_concat \<rightharpoonup> (SML) "CodeConst.String.concat"

text\<open>module Sys\<close>

consts Sys_is_directory2 :: "ml_string \<Rightarrow> bool ml_monad"
code_printing constant Sys_is_directory2 \<rightharpoonup> (Haskell) "CodeConst.Sys.isDirectory2"
            | constant Sys_is_directory2 \<rightharpoonup> (OCaml) "CodeConst.Sys.isDirectory2"
            | constant Sys_is_directory2 \<rightharpoonup> (Scala) "CodeConst.Sys.isDirectory2"
            | constant Sys_is_directory2 \<rightharpoonup> (SML) "CodeConst.Sys.isDirectory2"

text\<open>module To\<close>

consts ToNat :: "(nat \<Rightarrow> integer) \<Rightarrow> nat \<Rightarrow> ml_int"
code_printing constant ToNat \<rightharpoonup> (Haskell) "CodeConst.To.nat"
            | constant ToNat \<rightharpoonup> (OCaml) "CodeConst.To.nat"
            | constant ToNat \<rightharpoonup> (Scala) "CodeConst.To.nat"
            | constant ToNat \<rightharpoonup> (SML) "CodeConst.To.nat"

subsection\<open>Some Notations (I): Raw Translations\<close>

syntax "_sprint0" :: "_ \<Rightarrow> ml_string" ("sprint0 (_)\<acute>")
translations "sprint0 x\<acute>" \<rightleftharpoons> "CONST sprintf0 x"

syntax "_sprint1" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint1 (_)\<acute>")
translations "sprint1 x\<acute>" \<rightleftharpoons> "CONST sprintf1 x"

syntax "_sprint2" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint2 (_)\<acute>")
translations "sprint2 x\<acute>" \<rightleftharpoons> "CONST sprintf2 x"

syntax "_sprint3" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint3 (_)\<acute>")
translations "sprint3 x\<acute>" \<rightleftharpoons> "CONST sprintf3 x"

syntax "_sprint4" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint4 (_)\<acute>")
translations "sprint4 x\<acute>" \<rightleftharpoons> "CONST sprintf4 x"

syntax "_sprint5" :: "_ \<Rightarrow> _ \<Rightarrow> ml_string" ("sprint5 (_)\<acute>")
translations "sprint5 x\<acute>" \<rightleftharpoons> "CONST sprintf5 x"

subsection\<open>Some Notations (II): Polymorphic Cartouches\<close>

syntax "_cartouche_string'" :: String.literal
translations "_cartouche_string" \<rightleftharpoons> "_cartouche_string'"

parse_translation \<open>
  [( @{syntax_const "_cartouche_string'"}
   , parse_translation_cartouche
       @{binding cartouche_type'}
       (( "fun\<^sub>p\<^sub>r\<^sub>i\<^sub>n\<^sub>t\<^sub>f"
        , ( Cartouche_Grammar.nil1
          , Cartouche_Grammar.cons1
          , let fun f c x = Syntax.const c $ x in
            fn (0, x) => x
             | (1, x) => f @{const_syntax sprintf1} x
             | (2, x) => f @{const_syntax sprintf2} x
             | (3, x) => f @{const_syntax sprintf3} x
             | (4, x) => f @{const_syntax sprintf4} x
             | (5, x) => f @{const_syntax sprintf5} x
            end))
        :: Cartouche_Grammar.default)
       (fn 37 \<comment> \<open>\<^verbatim>\<open>#"%"\<close>\<close> => (fn x => x + 1)
         | _ => I)
       0)]
\<close>

subsection\<open>Generic Locale for Printing\<close>

locale Print =
  fixes To_string :: "string \<Rightarrow> ml_string"
  fixes To_nat :: "nat \<Rightarrow> ml_int"
begin
  declare[[cartouche_type' = "fun\<^sub>p\<^sub>r\<^sub>i\<^sub>n\<^sub>t\<^sub>f"]]
end

text\<open>As remark, printing functions (like @{term sprintf5}...) are currently
weakly typed in Isabelle, we will continue the typing using the type system of target languages.\<close>

end
