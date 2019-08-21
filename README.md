<div class="source">

``` {.source}
section ‹Global git structure of the Isabelle/C project›

text ‹
The Isabelle/C project consists of four components, where two of them represent AFP submissions.

▪ - C11-FrontEnd  (AFP)
▪ - C11-BackEnds  
▪ -- C11-BackEnd Clean (AFP, dependent on C11-FrontEnd)
▪ -- C11-BackEnd AutoCorres 
▪ --- Slightly modified version of AutoCorres Library
▪ --- Adapter to C11-FrontEnd
▪ -- C11-BackEnd-CLEAN
▪ --- Clean + Library
▪ --- CleanAdapter
▪ - Citadelle (Own Model-based Framework Generating The Granmmars and the AST of
C11-FrontEnd)
›

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
▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l CParser› 🗏‹C11-BackEnds/AutoCorres/examples/TestSEL4.thy›
▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l AutoCorres› 🗏‹C11-BackEnds/AutoCorres/examples/IsPrime_integrated.thy›
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
```

</div>
