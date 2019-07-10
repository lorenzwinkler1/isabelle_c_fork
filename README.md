<div class="head">

Theory README
=============

<span class="command">theory</span> <span class="name">README</span>\
<span class="keyword">imports</span> [<span
class="name">Main</span>](../../HOL/HOL/Main.html)\

</div>

<div class="source">

``` {.source}
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

theory README imports Main begin

section ‹Isabelle/C›

text ‹
Isabelle/C contains a C11 front-end support for Isabelle.

The code requires Isabelle2019. For a first start, the following C examples or entry-points of
documentation can be executed:

▪ ▩‹isabelle jedit -d› 🗀‹C11-FrontEnd› 🗏‹C11-FrontEnd/examples/C1.thy›
▪ ▩‹isabelle jedit -d› 🗀‹C11-FrontEnd› 🗏‹C11-FrontEnd/examples/C2.thy›
▪ ▩‹isabelle jedit -d› 🗀‹C11-FrontEnd› 🗏‹C11-FrontEnd/examples/C3.thy›
▪ ▩‹isabelle jedit -d› 🗀‹C11-FrontEnd› 🗏‹C11-FrontEnd/C_Appendices.thy›
›

text ‹
Certain examples in 🗀‹C11-FrontEnd› actually require to change the initial
directory provided to ▩‹isabelle jedit -d›, because they might depend on
other projects (such as ‹l4v›):

▪ ▩‹export L4V_ARCH = ARM› ∗‹‹#› the same effect can be made in 🗏‹~/.isabelle/etc/settings››
▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l CParser› 🗏‹C11-FrontEnd/semantic-backends/AutoCorres/examples/TestSEL4.thy›
▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l AutoCorres› 🗏‹C11-FrontEnd/semantic-backends/AutoCorres/examples/IsPrime_integrated.thy›
›

text ‹
For the last examples, we were used to see a sub-window ‹Bad session structure›
appearing just after starting Isabelle. Nevertheless, if this ever happens again, the sub-window can
be ignored by clicking on ‹OK›.

Additionally, 🗏‹l4v/src/run_tests› can be executed in
🗀‹l4v/src›, and interrupted once the success of ‹CBaseRefine›
obtained. Then, to test the interactive version of AutoCorres, it would suffice to run the following
command:
▪ ▩‹isabelle build -d› 🗀‹l4v/src› ▩‹-b -v AutoCorresSEL4›
›

text ‹
Note: The version of the ‹l4v› (🌐‹https://github.com/seL4/l4v/›)
project used is ‹e3352826893db4d00fc402fad2a0125307ebe45e›.
›

subsection ‹Authors›

text ‹
▪ Frédéric Tuong (🌐‹https://www.lri.fr/~ftuong›)
▪ Burkhart Wolff (🌐‹https://www.lri.fr/~wolff›)
›

subsection ‹License›

text ‹
This project is licensed under a 3-clause BSD-style license.
›

end
```

</div>
