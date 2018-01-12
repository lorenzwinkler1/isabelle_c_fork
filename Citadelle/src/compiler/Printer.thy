(******************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Printer.thy ---
 * This file is part of HOL-TestGen.
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

section\<open>Finalizing the Printer\<close>

theory  Printer
imports Core
        "meta/Printer_META"
begin

definition "List_iterM f l =
  List.fold (\<lambda>x m. bind m (\<lambda> () \<Rightarrow> f x)) l (return ())"

context Print
begin

declare[[cartouche_type' = "String.literal"]]

definition "(write_file0 :: _ \<Rightarrow> (((_ \<Rightarrow> String.literal \<Rightarrow> _) \<Rightarrow> _) \<Rightarrow> _) \<times> _) env =
 (let (l_thy, Sys_argv) = compiler_env_config.more env
    ; (is_file, f_output) = case (D_output_header_thy env, Sys_argv)
     of (Some (file_out, _), Some dir) \<Rightarrow>
          let dir = To_string dir in
          (True, \<lambda>f. bind (Sys_is_directory2 dir) (\<lambda> Sys_is_directory2_dir.
                     out_file1 f (if Sys_is_directory2_dir then sprint2 \<open>%s/%s.thy\<close>\<acute> dir (To_string file_out) else dir)))
      | _ \<Rightarrow> (False, out_stand1)
    ; (env, l) =
           fold_thy'
             comp_env_save_deep
             (\<lambda>f. f ())
             (\<lambda>_ _. [])
             (\<lambda>msg x acc1 acc2. (acc1, Cons (msg, x) acc2))
             (fst (compiler_env_config.more env))
             (compiler_env_config.truncate env, []) in
  (f_output, of_all_meta_lists (compiler_env_config_more_map (\<lambda>_. is_file) env) (rev l)))"

definition "write_file env =
 (let (f_output, l) = write_file0 env in
  f_output
    (\<lambda>fprintf1.
      List_iterM (fprintf1 \<open>%s
\<close>                             )
                 l))"
end

definition "write_file0 = Print.write_file0 (String.implode o String.to_list) (ToNat integer_of_natural)"
definition "write_file = Print.write_file (String.implode o String.to_list) (ToNat integer_of_natural)"

lemmas [code] =
  (* def *)
  Print.write_file0_def
  Print.write_file_def

  (* fun *)

section\<open>Miscellaneous: Garbage Collection of Notations\<close>

no_type_notation natural ("nat")
no_type_notation abr_string ("string")

end
