(******************************************************************************
 * A Meta-Model for the Language.C Haskell Library
 *
 * Copyright (c) 2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
 *               2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
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

theory C_Model_ex_meta
  imports "Citadelle_C_shallow-dirty.C_Model_core"
begin

section \<open>Type definition (at ML level)\<close>

meta_command' \<comment>\<open>\<^theory_text>\<open>code_reflect' open META2 functions SingleLine MultiLine Comment\<close>\<close> \<open>
let
  open META
  fun meta_command {shallow, deep = _, syntax_print = _} =
    [(META_semi_theories o Theories_one o Theory_code_reflect)
      (Code_reflect
        ( true
        , From.string "META2"
        , map From.string [ "SingleLine", "MultiLine", "Comment" ]
         @ (shallow
            |> hd
            |> fst
            |> d_hsk_constr
            |> map (flattenb (From.string "C_Model_core.") o to_String))))]
in meta_command
end
\<close>

meta_command'\<open>
let
  open META
  fun b s = SML_basic [s]
  fun meta_command {shallow, deep = _, syntax_print = _} =
    [(META_semi_theories o Theories_one o Theory_ML o SMLa o SML_top)
      (shallow
       |> hd
       |> fst
       |> d_hsk_constr
       |> map_filter
            (fn s =>
              let val s' = s |> to_String |> To_string0 in
              if List.exists (fn s0 => s0 = s') ["ClangCVersion", "CString"] then NONE
              else
                  SOME
                    (SML_val_fun
                      ( SOME Sval
                      , SML_rewrite ( b (to_String s)
                                    , From.string "="
                                    , b (case String.explode s' of
                                           c :: s => c :: s |> String.implode |> (fn x => "META2." ^ x ^ "0") |> From.string))))
              end))]
in meta_command
end
\<close>

ML\<open>open META2\<close>

section \<open>Initialization of the parsing code\<close>

meta_language C
  base_path "../../../src/compiler_generic/isabelle_home/contrib/haskabelle"
  [Prelude, Option]
  where imports \<open>Language.C\<close>
          (load \<open>Importer.Conversion.Haskell\<close>)
          (load \<open>Importer.Conversion.Haskell.C\<close>)
  where defines \<open>\s -> do { (r, acc) <- parseC' (inputStreamFromString s) ; return (gshows r "", acc) }\<close>

section \<open>Parsing\<close>

definition increment_method :: unit where \<open>
  increment_method = ()
\<close>

definition even_count_gen :: unit where \<open>
  even_count_gen = ()
\<close>

definition max_program_correct :: unit where \<open>
  max_program_correct = ()
\<close>

(*
language meta increment_method :: C where \<open>/* ASSUMES \<open>\<guillemotleft>a\<guillemotright> >\<^sub>u 0\<close> */ f () {
  int x = 0;
  /* INVAR \<open>\<guillemotleft>a\<guillemotright> >\<^sub>u 0 \<and> \<guillemotleft>a\<guillemotright> \<ge>\<^sub>u &x\<close>
     VRT \<open>(measure o Rep_uexpr) (\<guillemotleft>a\<guillemotright> - &x)\<close> */
  while (x < a) {
    x = x + 1;
  }
} /* ENSURES \<open>\<guillemotleft>a\<guillemotright> =\<^sub>u &x\<close> */\<close>

language meta even_count_gen :: C where \<open>/* ASSUMES \<open>\<guillemotleft>a\<guillemotright> >\<^sub>u 0\<close> */ f () {
  int i = 0;
  int j = 0;
  /* INVAR \<open>&j =\<^sub>u (&i + 1) div \<guillemotleft>2\<guillemotright> \<and> &i \<le>\<^sub>u \<guillemotleft>a\<guillemotright>\<close>
     VRT \<open>measure (nat o (Rep_uexpr (\<guillemotleft>a\<guillemotright> - &i)))\<close> */
  while (i < a) {
    if (i % 2 == 0) {
      j = j + 1;
    } else skip;
    i = i + 1;
  }
} /* ENSURES \<open>&j =\<^sub>u (\<guillemotleft>a\<guillemotright> + 1)div \<guillemotleft>2\<guillemotright>\<close> */\<close>

language meta max_program_correct :: C where \<open>/* ASSUMES \<open>uop length \<guillemotleft>a\<guillemotright> \<ge>\<^sub>u1 \<and> &i =\<^sub>u 1 \<and> &r =\<^sub>u bop nth \<guillemotleft>a:: int list\<guillemotright> 0\<close> */ f () {
  /* INVAR \<open>0 <\<^sub>u &i \<and> &i \<le>\<^sub>u uop length \<guillemotleft>a\<guillemotright> \<and> &r =\<^sub>u uop Max (uop set (bop take (&i) \<guillemotleft>a\<guillemotright>))\<close>
     VRT \<open>measure (Rep_uexpr (uop length \<guillemotleft>a\<guillemotright> - (&i)))\<close> */
  while (! (i < length(a))) {
    if (r < nth(a, i)) {
      r = nth(a, i);
    } else skip;
    i = i + 1;
  }
} /* ENSURES \<open>&r =\<^sub>u uop Max (uop set \<guillemotleft>a\<guillemotright>)\<close> */\<close>
*)
end
