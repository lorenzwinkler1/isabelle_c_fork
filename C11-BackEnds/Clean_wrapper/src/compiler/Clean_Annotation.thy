(******************************************************************************
 * Isabelle/C
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 
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

chapter \<open>Isabelle/C/Clean Annotations\<close>

text\<open>This file contains the basic setup of Isabelle/C/Clean; in particular, it contains
the definition and declaration of the Clean-specific annotation commands. \<close>

theory Clean_Annotation
  imports Isabelle_C.C_Main
begin

section \<open>User Defined Commands in the Semantic Verification Space\<close>

ML \<comment> \<open>\<^theory>\<open>Isabelle_C.C_Command\<close>\<close> \<open>
infix 3 >>>;

structure Clean_Annotation =
struct
type text_range = Symbol_Pos.text * Position.T

datatype antiq_hol = Invariant of string (* term *)
                   | Fnspec of text_range (* ident *) * string (* term *)
                   | Relspec of string (* term *)
                   | Modifies of (bool (* true: [*] *) * text_range) list
                   | Dont_translate
                   | Auxupd of string (* term *)
                   | Ghostupd of string (* term *)
                   | Spec of string (* term *)
                   | End_spec of string (* term *)
                   | Calls of text_range list
                   | Owned_by of text_range
                   | Measure of string

(*In the following data structure the annotations are saved*)
type annotation_data = {
  preconditions: (string*(Context.generic -> term)*Position.range) list,
  postconditions: (string*(Context.generic -> term)*Position.range) list,
  invariants: (string*(Context.generic -> term)*Position.range) list,
  measures: (string*(Context.generic -> term)*Position.range) list
}
structure Data_Clean_Annotations = Generic_Data
  (type T = annotation_data
   val empty = {preconditions=[], postconditions=[], invariants=[], measures=[]}
   val merge = K empty)

fun map_context_annotation_declaration annotation_type src range context0 =
let 
  val current_env =snd (C_Stack.Data_Lang.get' context0)
  fun get_fun_name [(SOME (C_Ast.Ident0 (C_Ast.SS_base (C_Ast.ST name), _, _)),_)] = name
      | get_fun_name (_::R) = get_fun_name R
      | get_fun_name _ = (warning "unable to find name of surrounding function for CLEAN annotation";"")
  val term =fn ctxt=> 
                (*Important change: Syntax.read_term does coerce the types of the terms 
                  constructed by C_Expr antiquotation. Syntax.parse_term does not do that*)
                (*It does substitute free variables though, which is quite an issue*)
                Syntax.parse_term 
                        (Context.proof_of (C_Module.Data_Surrounding_Env.put current_env ctxt)) 
                        (Token.inner_syntax_of src)
  val function_name = (get_fun_name o #scopes o snd o C_Stack.Data_Lang.get') context0
  val new_data = [(function_name, term, range)]

  val new_context_map = Data_Clean_Annotations.map (fn {preconditions, postconditions, invariants, measures} => {
      preconditions = case annotation_type of Spec _ => preconditions@new_data | _ => preconditions,
      postconditions = case annotation_type of End_spec _ => postconditions@new_data | _ => postconditions,
      invariants =case annotation_type of Invariant _ => invariants@new_data | _ => invariants,
      measures =case annotation_type of Measure _ => measures@new_data | _ => measures
  })
in new_context_map context0 end

fun bind scan context_map ((stack1, (to_delay, stack2)), _) =
  C_Parse.range scan
  >> (fn (src, range) =>
      C_Env.Parsing
        ( (stack1, stack2)
        , ( range
          , C_Inner_Syntax.bottom_up
              (fn v1 => fn context =>(
                  context_map src range context)
                  )
          , Symtab.empty
          , to_delay)))

fun scan >>> f = bind scan f

end
\<close>

text \<open>
Finally, we will have a glance at the code for the registration of the annotation commands
used in the example. Thanks to Isabelle/C's function \<^ML>\<open>C_Annotation.command'\<close>, the registration of 
user-defined annotations is very similar to the registration of ordinary commands in the Isabelle
platform.\<close>

ML \<open>local open Clean_Annotation
    in fun command keyword annotation_type =
        C_Annotation.command' keyword ""
          (C_Token.syntax'
            (Parse.token Parse.cartouche)
           >>> map_context_annotation_declaration annotation_type)
    end\<close>    

setup \<open>let open Clean_Annotation
       in command ("pre\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n", \<^here>) (Spec "")
       #> command ("post\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n", \<^here>) (End_spec "")
       #> command ("inv\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n", \<^here>) (Invariant "")
       #> command ("measure\<^sub>C\<^sub>l\<^sub>e\<^sub>a\<^sub>n", \<^here>) (Measure "")
       end\<close>

end
