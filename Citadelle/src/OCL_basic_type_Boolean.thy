(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.4
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * OCL_basic_type_Boolean.thy --- Library definitions.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2014 Université Paris-Sud, France
 *               2013-2014 IRT SystemX, France
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

theory  OCL_basic_type_Boolean
imports OCL_lib_common
begin


subsection{* Fundamental Predicates on Basic Types: Strict (Referential) Equality *}
text{*
  Here is a first instance of a definition of strict value equality---for
  the special case of the type @{typ "('\<AA>)Boolean"}, it is just
  the strict extension of the logical
  equality:
*}
defs   StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n[code_unfold] :
      "(x::('\<AA>)Boolean) \<doteq> y \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                                    then (x \<triangleq> y)\<tau>
                                    else invalid \<tau>"

text{* which implies elementary properties like: *}
lemma [simp,code_unfold] : "(true \<doteq> false) = false"
by(simp add:StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n)
lemma [simp,code_unfold] : "(false \<doteq> true) = false"
by(simp add:StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n)

lemma null_non_false [simp,code_unfold]:"(null \<doteq> false) = false"
 apply(rule ext, simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n StrongEq_def false_def)
 by (metis drop.simps cp_valid false_def is_none_code(2) is_none_def valid4
           bot_option_def null_fun_def null_option_def)

lemma null_non_true [simp,code_unfold]:"(null \<doteq> true) = false"
 apply(rule ext, simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n StrongEq_def false_def)
 by(simp add: true_def bot_option_def null_fun_def null_option_def)

lemma false_non_null [simp,code_unfold]:"(false \<doteq> null) = false"
 apply(rule ext, simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n StrongEq_def false_def)
 by(metis drop.simps cp_valid false_def is_none_code(2) is_none_def valid4
          bot_option_def null_fun_def null_option_def )

lemma true_non_null [simp,code_unfold]:"(true \<doteq> null) = false"
 apply(rule ext, simp add: StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n StrongEq_def false_def)
 by(simp add: true_def bot_option_def null_fun_def null_option_def)

text{* With respect to strictness properties and miscelleaneous side-calculi,
strict referential equality behaves on booleans as described in the
@{term "profile_bin3"}:*}
interpretation StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n : profile_bin3 "\<lambda> x y. (x::('\<AA>)Boolean) \<doteq> y" 
         by unfold_locales (auto simp:StrictRefEq\<^sub>B\<^sub>o\<^sub>o\<^sub>l\<^sub>e\<^sub>a\<^sub>n)
         
text{* In particular, it is strict, cp-preserving and const-preserving. In particular,
it generates the simplifier rules for terms like:*}
lemma "(invalid \<doteq> false) = invalid" by(simp)
lemma "(invalid \<doteq> true) = invalid"  by(simp)
lemma "(false \<doteq> invalid) = invalid" by(simp)
lemma "(true \<doteq> invalid) = invalid"  by(simp)
lemma "((invalid::('\<AA>)Boolean) \<doteq> invalid) = invalid" by(simp)
text{* Thus, the weak equality is \emph{not} reflexive. *}



subsection{* Test Statements on Boolean Operations. *}
text{* Here follows a list of code-examples, that explain the meanings
of the above definitions by compilation to code and execution to @{term "True"}.*}

text{* Elementary computations on Boolean *}
Assert "\<tau> \<Turnstile> \<upsilon>(true)"
Assert "\<tau> \<Turnstile> \<delta>(false)"
Assert "\<not>(\<tau> \<Turnstile> \<delta>(null))"
Assert "\<not>(\<tau> \<Turnstile> \<delta>(invalid))"
Assert "\<tau> \<Turnstile> \<upsilon>((null::('\<AA>)Boolean))"
Assert "\<not>(\<tau> \<Turnstile> \<upsilon>(invalid))"
Assert "\<tau> \<Turnstile> (true and true)"
Assert "\<tau> \<Turnstile> (true and true \<triangleq> true)"
Assert "\<tau> \<Turnstile> ((null or null) \<triangleq> null)"
Assert "\<tau> \<Turnstile> ((null or null) \<doteq> null)"
Assert "\<tau> \<Turnstile> ((true \<triangleq> false) \<triangleq> false)"
Assert "\<tau> \<Turnstile> ((invalid \<triangleq> false) \<triangleq> false)"
Assert "\<tau> \<Turnstile> ((invalid \<doteq> false) \<triangleq> invalid)"
Assert "\<tau> \<Turnstile> (true <> false)"
Assert "\<tau> \<Turnstile> (false <> true)"


end
