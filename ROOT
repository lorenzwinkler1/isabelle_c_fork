(******************************************************************************
 * Generation of Language.C Grammar with ML Interface Binding
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

(* For modularity reasons, and to ease the importation of a specific session by
   semantic back-ends, theory files are (at the time of writing) not regrouped
   into a unique session. *)

session Isabelle_C_AutoCorres in "C11-FrontEnd" = AutoCorres +
  options [document = pdf, document_output = "generated"]
  (* TODO: find a way to concatenate together PDF in:
           generated/part1 + generated/part2 + generated/part3 *)
  theories
    "semantic-backends/AutoCorres/README"


session Isabelle_C_AutoCorres_test in "C11-FrontEnd" = Isabelle_C_AutoCorres +
  options [document = pdf, document_output = "generated"]
  (* TODO: find a way to concatenate together PDF in:
           generated/part1 + generated/part2 + generated/part3 *)
  sessions
    "HOL-Computational_Algebra"
  theories
    "semantic-backends/AutoCorres/examples/IsPrime_integrated"
    "semantic-backends/AutoCorres/examples/IsPrime_linear_outside"
    "semantic-backends/AutoCorres/examples/IsPrime_sqrt_outside"
    "semantic-backends/AutoCorres/examples/Parse_for_loop"
    "semantic-backends/AutoCorres/examples/TestSEL4"
  document_files
    "root.tex"
    "root.bib"
