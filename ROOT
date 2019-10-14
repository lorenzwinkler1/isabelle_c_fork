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

session Isabelle_C_AutoCorres in "C11-BackEnds/AutoCorres_wrapper" = AutoCorres +
  theories
    "../AutoCorres/src/README"
    "src/Backend"

session Isabelle_C_AutoCorres_examples in "C11-BackEnds/AutoCorres_wrapper" = Isabelle_C_AutoCorres +
  sessions
    "HOL-Computational_Algebra"
  theories
    "examples/IsPrime_integrated"
    "examples/IsPrime_linear_outside"
    "examples/IsPrime_sqrt_outside"
    "examples/IsPrime_sqrt_opt_outside"
    "examples/Parse_for_loop"
    "examples/Quicksort"
    "examples/TestSEL4"

session Isabelle_C_Clean in "C11-BackEnds/Clean_wrapper" = Isabelle_C +
  sessions
    Clean
  theories
    "src/Backend"

session Isabelle_C_Clean_examples in "C11-BackEnds/Clean_wrapper" = Isabelle_C_Clean +
  sessions
    "HOL-Computational_Algebra"
  theories
    "examples/IsPrime_sqrt_outside"
    "examples/Prime"
    "examples/Quicksort2"
    "examples/Quicksort"

session Isabelle_C_README in "C11-FrontEnd" = HOL +
  theories
    "../README"

session Isabelle_C_archive = Isabelle_C_AutoCorres +
  options [quick_and_dirty]
  sessions
    Clean
    "HOL-Computational_Algebra"
  theories
    "C11-FrontEnd/archive/Clean_old"
    "C11-FrontEnd/archive/IsPrime_sqrt_outside"
    "C11-FrontEnd/archive/Prime"
    "C11-BackEnds/AutoCorres/examples/program-based/Example1"
    "C11-BackEnds/AutoCorres/examples/program-based/Example2"
