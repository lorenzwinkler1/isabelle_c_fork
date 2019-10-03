<div class="source">

``` {.source}
section ‹Global Structure of the Isabelle/C Project›

text ‹
The Isabelle/C project consists of several components, where some of them represent AFP submissions.

▪ 🗀‹C11-FrontEnd› (AFP)
▪ 🗀‹C18-FrontEnd› (AFP)
▪ 🗀‹C11-BackEnds›
  ▪ 🗀‹C11-BackEnds/Clean›: (AFP, depending of 🗀‹C11-FrontEnd›) Clean Library
  ▪ 🗀‹C11-BackEnds/Clean_wrapper›: adapter to 🗀‹C11-FrontEnd›
  ▪ 🗀‹C11-BackEnds/AutoCorres›: slightly modified version of AutoCorres library
  ▪ 🗀‹C11-BackEnds/AutoCorres_wrapper›: adapter to 🗀‹C11-FrontEnd›
▪ 🗀‹Citadelle›: own model-based framework generating the grammars and the AST of 🗀‹C11-FrontEnd›
›

section ‹Isabelle/C›

text ‹
Isabelle/C contains a C99/C11/C18 front-end support for Isabelle. The front-end is actually composed
of two possibly interchangeable parsers (from two different projects):

▪ 🗀‹C11-FrontEnd›: 🌐‹https://hackage.haskell.org/package/language-c›
▪ 🗀‹C18-FrontEnd›: 🌐‹https://github.com/jhjourdan/C11parser›

Thus, one can select which parser(s) are better suitable to be enabled in front of a piece of C
code.

Isabelle/C requires Isabelle2019. For a first start, the following C examples or entry-points of
documentation can be executed:

▪ ▩‹isabelle jedit -d› 🗀‹C11-FrontEnd› 🗏‹C11-FrontEnd/examples/C1.thy›
▪ ▩‹isabelle jedit -d› 🗀‹C11-FrontEnd› 🗏‹C11-FrontEnd/examples/C2.thy›
▪ ▩‹isabelle jedit -d› 🗀‹C18-FrontEnd› 🗏‹C11-FrontEnd/examples/C0.thy›
▪ ▩‹isabelle jedit -d› 🗀‹C11-FrontEnd› 🗏‹C11-FrontEnd/C_Appendices.thy›
›

text ‹
Examples in 🗀‹C11-BackEnds› require to change the initial directory provided to
▩‹isabelle jedit -d›, because they depend on respective semantic back-ends.
›

subsection ‹Isabelle/C/Clean›

text ‹
▪ ▩‹isabelle jedit -d› 🗀‹.› 🗏‹C11-BackEnds/Clean_wrapper/examples/Prime.thy›
›

subsection ‹Isabelle/C/AutoCorres›

text ‹
Before using the 🗀‹C11-BackEnds/AutoCorres_wrapper› back-end, the shell variable
‹L4V_ARCH› must be additionally set to ‹ARM›.

▪ ▩‹export L4V_ARCH = ARM› ∗‹‹#› the same effect can be permanently made in 🗏‹$ISABELLE_HOME_USER/etc/settings››
▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l CParser› 🗏‹C11-BackEnds/AutoCorres_wrapper/examples/TestSEL4.thy›
▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l AutoCorres› 🗏‹C11-BackEnds/AutoCorres_wrapper/examples/IsPrime_integrated.thy›
›

text ‹
For the case of 🗀‹C11-BackEnds/AutoCorres_wrapper›, we were used to see a
sub-window ‹Bad session structure› appearing just after starting Isabelle. This is
because the back-end normally requires to execute some initialization script (for example using
🗏‹l4v/src/run_tests›) to generate specific Isabelle theory files. Instead, as
possible workaround, we have introduced by hand in 🗀‹l4v/src› several symbolic
links pointing to the missing files, making the sub-window not supposed to appear
anymore. Nevertheless, if this ever happens again, the sub-window can be ignored by clicking on
‹OK›.

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

subsection ‹Isabelle/C/README›

text ‹
🗏‹README.md› is automatically generated from 🗏‹README.thy›
using:
▪ ▩‹isabelle env› 🗏‹./README.sh›
›

section ‹Authors›

text ‹
▪ Frédéric Tuong (🌐‹https://www.lri.fr/~ftuong›)
▪ Burkhart Wolff (🌐‹https://www.lri.fr/~wolff›)
›

section ‹License›

text ‹
This project is licensed under a 3-clause BSD-style license.
›
```

</div>
