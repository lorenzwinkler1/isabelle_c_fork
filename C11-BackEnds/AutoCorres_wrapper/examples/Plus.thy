(******************************************************************************
 * Isabelle/C/AutoCorres
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
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
(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Plus
imports
  Isabelle_C_AutoCorres.AutoCorres_Wrapper
begin

declare [[AutoCorres]]

C \<open>
//@ install_autocorres plus [ ts_force nondet = plus2 ]

unsigned int plus(unsigned int a, unsigned int b) {
    return a + b;
}

unsigned int plus2(unsigned int a, unsigned int b) {
    while (b > 0) {
        a += 1;
        b -= 1;
    }
    return a;
}

int main(int argc, char **argv) {
    return !(plus(1, 2) == plus2(1, 2));
}
\<close>

context plus begin

(* 3 + 2 should be 5 *)
lemma "plus' 3 2 = 5"
  unfolding plus'_def
  by eval

(* plus does what it says on the box *)
lemma plus_correct: "plus' a b = a + b"
  unfolding plus'_def
  apply (rule refl)
  done

(* Compare pre-lifting to post-lifting *)
thm plus_global_addresses.plus2_body_def
thm plus2'_def

(* plus2 does what it says on the box *)
lemma plus2_correct: "\<lbrace>\<lambda>s. True\<rbrace> plus2' a b \<lbrace> \<lambda>r s. r = a + b\<rbrace>"
  unfolding plus2'_def
  apply (subst whileLoop_add_inv
   [where I="\<lambda>(a', b') s. a' + b' = a + b"
      and M="\<lambda>((a', b'), s). b'"])
  apply (wp, auto simp: not_less)
  done

(* plus2 does what it says on plus's box *)
lemma plus2_is_plus: "\<lbrace> \<lambda>s. True \<rbrace> plus2' a b \<lbrace> \<lambda>r s. r = plus' a b \<rbrace>"
  unfolding plus'_def
  apply (simp add:plus2_correct)
  done

(* Prove plus2 with no failure *)
lemma plus2_valid:"\<lbrace> \<lambda>s. True \<rbrace> plus2' a b \<lbrace> \<lambda>r s. r = a + b \<rbrace>!"
  unfolding plus2'_def
  apply (subst whileLoop_add_inv
   [where I="\<lambda>(a', b') s. a' + b' = a + b"
      and M="\<lambda>((a', b'), s). b'"])
  apply wp
    apply clarsimp
    apply unat_arith
   apply clarsimp
   apply unat_arith
  apply clarsimp
  done

end

end
