(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_compiler_parser_Pure.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Sud, France
 *               2013-2015 IRT SystemX, France
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
(* $Id:$ *)

header{* Part ... *}

theory  OCL_compiler_parser_Pure
imports OCL_compiler_meta_Pure
        OCL_compiler_parser_init
begin

subsection{* i of ... *} (* i_of *)

subsubsection{* general *}

context i_of
begin

definition "i_of_pure_indexname a b = rec_pure_indexname
  (ap2 a (b \<open>PureIndexname\<close>) (i_of_string a b) (i_of_nat a b))"

definition "i_of_pure_class a b = rec_pure_class
  (ap1 a (b \<open>PureClass\<close>) (i_of_string a b))"

definition "i_of_pure_sort a b = rec_pure_sort
  (ap1 a (b \<open>PureSort\<close>) (i_of_list a b (i_of_pure_class a b)))"

definition "i_of_pure_typ a b = rec_pure_typ
  (ap2 a (b \<open>PureType\<close>) (i_of_string a b) (i_of_list a b snd))
  (ap2 a (b \<open>PureTFree\<close>) (i_of_string a b) (i_of_pure_sort a b))
  (ap2 a (b \<open>PureTVar\<close>) (i_of_pure_indexname a b) (i_of_pure_sort a b))"

definition "i_of_pure_term a b = (\<lambda>f0 f1 f2 f3 f4 f5. rec_pure_term f0 f1 f2 f3 (co2 K f4) (\<lambda>_ _. f5))
  (ap2 a (b \<open>PureConst\<close>) (i_of_string a b) (i_of_pure_typ a b))
  (ap2 a (b \<open>PureFree\<close>) (i_of_string a b) (i_of_pure_typ a b))
  (ap2 a (b \<open>PureVar\<close>) (i_of_pure_indexname a b) (i_of_pure_typ a b))
  (ap1 a (b \<open>PureBound\<close>) (i_of_nat a b))
  (ar3 a (b \<open>PureAbs\<close>) (i_of_string a b) (i_of_pure_typ a b))
  (ar2 a (b \<open>PureApp\<close>) id)"

end

lemmas [code] =
  i_of.i_of_pure_indexname_def
  i_of.i_of_pure_class_def
  i_of.i_of_pure_sort_def
  i_of.i_of_pure_typ_def
  i_of.i_of_pure_term_def

end
