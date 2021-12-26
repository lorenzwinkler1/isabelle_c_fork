<div class="source">

``` {.source}
section ‹Global Structure of the Isabelle/C Project›

text ‹
The Isabelle/C project consists of several components, where some of them are published in the
Isabelle AFP, or represent AFP submissions.

▪ 🗀‹C11-FrontEnd› (AFP)
▪ 🗀‹C18-FrontEnd›
▪ 🗀‹C11-BackEnds›
  ▪ 🗀‹C11-BackEnds/Clean›: (AFP) Clean Library
  ▪ 🗀‹C11-BackEnds/Clean_wrapper›: (AFP) adapter to 🗀‹C11-FrontEnd›
  ▪ 🗀‹C11-BackEnds/AutoCorres›: slightly modified version of AutoCorres library
  ▪ 🗀‹C11-BackEnds/AutoCorres_wrapper›: adapter to 🗀‹C11-FrontEnd›
▪ 🗀‹Citadelle›: model-based framework generating the grammars and the AST of 🗀‹C11-FrontEnd›
›

section ‹Isabelle/C›

text ‹
Isabelle/C contains a C99/C11/C18 front-end support for Isabelle. The front-end is actually composed
of two possibly interchangeable parsers (from two different projects):

▪ 🗀‹C11-FrontEnd›: 🌐‹https://hackage.haskell.org/package/language-c›
▪ 🗀‹C18-FrontEnd›: 🌐‹https://github.com/jhjourdan/C11parser›

At present, the recommended and default version is C11.

Isabelle/C requires Isabelle2021. (This is following the latest version currently supported by
AutoCorres.)
›

section ‹Getting started (quickstart for users)›

text ‹
In the sequel, with ▩‹isabelle› we refer to your local Isabelle2021
installation, and assume your current working directory is at the root of ▩‹Isabelle_C›
(i.e. the directory that contains this 🗏‹README.md› file).

▪ Building Isabelle_C : 
  ▩‹isabelle build -d› 🗀‹.› ▩‹-b Isabelle_C›
▪ Building Isabelle_C_AutoCorres : 
  ▩‹export L4V_ARCH = ARM› ∗‹‹#› the same effect can be permanently made in 🗏‹$ISABELLE_HOME_USER/etc/settings››
  ▩‹isabelle build -d› 🗀‹.› ▩‹-b Isabelle_C_AutoCorres›
▪ Running an example: 
  ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l Isabelle_C_AutoCorres› 🗏‹C11-BackEnds/AutoCorres_wrapper/examples/IsPrime_linear_CCT.thy›
›

section ‹Getting started (for developers)›

text ‹
A first installation step of Isabelle/C without back-ends is:

▪ ▩‹isabelle build -D› 🗀‹C11-FrontEnd› ▩‹-D› 🗀‹C18-FrontEnd›

which should work out of the box.
›

text ‹
Alternatively, the full build of the ∗‹developer repository› of Isabelle/C with
all back-ends enabled is performed with:

▪ ▩‹isabelle build -b -v -d› 🗀‹.› ▩‹Isabelle_C_all Isabelle_C_Advance_examples Clean_document Isabelle_C_AutoCorres_document Isabelle_C_Clean_document Isabelle_C_README Isabelle_C_archive›
›

text ‹
The following C examples or entry-points of documentation can be executed:

▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l Isabelle_C› 🗏‹C11-FrontEnd/examples/C0.thy›
▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l Isabelle_C› 🗏‹C11-FrontEnd/examples/C1.thy›
▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l Isabelle_C› 🗏‹C11-FrontEnd/examples/C2.thy›
▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l Isabelle_C› 🗏‹C18-FrontEnd/examples/C0.thy›
▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l Isabelle_C› 🗏‹C11-FrontEnd/appendices/C_Appendices.thy›

The option ▩‹-l Isabelle_C› can be omitted; it instructs Isabelle to use a
binary-built version of the ▩‹Isabelle_C› session. In case of omission,
Isabelle automatically loads all ▩‹Isabelle_C› sources, such that the user
might browse in there or modify any files.
›

text ‹
▪ The example 🗏‹C11-FrontEnd/examples/C0.thy› is basically used to
demonstrate the faithfulness of the C11 parser implementation.
▪ The example 🗏‹C11-FrontEnd/examples/C2.thy› shows common cases of C and
C editing support in PIDE; it also contains annotation commands without any semantics.
▪ The example 🗏‹C11-FrontEnd/examples/C1.thy› is a show-case for markup
generation and the use of bindings resulting from the static C environment.
▪ The example 🗏‹C18-FrontEnd/examples/C0.thy› is basically used to
demonstrate the faithfulness of the C18 parser implementation.
▪ The example 🗏‹C11-FrontEnd/appendices/C_Appendices.thy› shows the use of
Isabelle/C documentation facilities.
›

text ‹
The AFP version of Isabelle/C does not include semantic back-ends (these are distributed by other
AFP submissions or available via the web; see below). The structure of 🗀‹.› has
been designed to create a directory 🗀‹C11-BackEnds› into which back-ends can be
installed. The structure of 🗀‹.› is actually similar as
🌐‹https://gitlri.lri.fr/ftuong/isabelle_c›: see for example
🌐‹https://gitlri.lri.fr/ftuong/isabelle_c/tree/C/C11-BackEnds› where several
back-ends can be copied and tried.
›

subsection ‹Isabelle/C/Clean›

text ‹
A first installation step of Isabelle/C/Clean is:

▪ ▩‹isabelle build -d› 🗀‹.› ▩‹-D› 🗀‹C11-BackEnds/Clean_wrapper›

which should work out of the box.
›

text ‹
▪ ▩‹isabelle jedit -d› 🗀‹.› 🗏‹C11-BackEnds/Clean_wrapper/examples/Prime.thy›
›

subsection ‹Isabelle/C/AutoCorres›

text ‹
Before using the 🗀‹C11-BackEnds/AutoCorres_wrapper› back-end, the shell variable
‹L4V_ARCH› must be additionally set to ‹ARM›.

▪ ▩‹export L4V_ARCH = ARM› ∗‹‹#› the same effect can be permanently made in 🗏‹$ISABELLE_HOME_USER/etc/settings››
▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l CParser› 🗏‹C11-BackEnds/AutoCorres_wrapper/examples/TestSEL4.thy›
▪ ▩‹isabelle jedit -d› 🗀‹.› ▩‹-l AutoCorres› 🗏‹C11-BackEnds/AutoCorres_wrapper/examples/IsPrime_linear_CCT.thy›
›

text ‹
For the case of 🗀‹C11-BackEnds/AutoCorres_wrapper›, we were used to see a
sub-window ‹Bad session structure› appearing just after starting Isabelle. This is
because the back-end normally requires to execute some initialization script (for example using
🗏‹src_ext/l4v/src/run_tests›) to generate specific Isabelle theory
files. Instead, as possible workaround, we have introduced by hand in
🗀‹src_ext/l4v/src› several symbolic links pointing to the missing files, making
the sub-window not supposed to appear anymore. Nevertheless, if this ever happens again, the
sub-window can be ignored by clicking on ‹OK›.

Additionally, 🗏‹src_ext/l4v/src/run_tests› can be executed in
🗀‹src_ext/l4v/src›, and interrupted once the success of
‹CBaseRefine› obtained. Then, to test the interactive version of AutoCorres, it would
suffice to run the following command:
▪ ▩‹isabelle build -d› 🗀‹src_ext/l4v/src› ▩‹-b -v AutoCorresSEL4›
›

text ‹
Note: The version of the ‹l4v› (🌐‹https://github.com/seL4/l4v/›)
project used is ‹e3352826893db4d00fc402fad2a0125307ebe45e›.
›

subsection ‹Isabelle/C/README›

text ‹
🗏‹README.md› is automatically generated from 🗏‹README/README.thy›
using:
▪ ▩‹isabelle env› 🗏‹README/README.sh›
›

text ‹ Note that this shell-script requires the prior installation of
▩‹pandoc› (🌐‹https://github.com/jgm/pandoc›).
›

section ‹Authors›

text ‹
▪ Frédéric Tuong (🌐‹https://www.lri.fr/~ftuong›)
▪ Burkhart Wolff (🌐‹https://www.lri.fr/~wolff›)
›

section ‹License›

text ‹
Isabelle/C is licensed under a 3-clause BSD-style license (where certain files are in the HPND
license compatible with the 3-clause BSD).

In more details:
▪ The generated files 🗏‹C11-FrontEnd/generated/c_ast.ML› and
  🗏‹C11-FrontEnd/generated/c_grammar_fun.grm› are mixing several source code of
    different projects:
  ▪ In 3-clause BSD: the part representing the Haskell Language.C library.  
  ▪ In 2-clause BSD: the C99 AST in HOL (before reflection to SML) adapted from the original
    one in the L4.verified project.
  ▪ In 3-clause BSD: the HOL translation C11 to C99 from the Securify project.    
  ▪ In 3-clause BSD: any other binding and translations of meta-models from the Citadelle
    project.
▪ In 3-clause BSD: the two combined generators generating
  🗏‹C11-FrontEnd/generated/c_ast.ML› based on some modified version of Haskabelle
  and Citadelle.
▪ In 3-clause BSD: the Happy modified generator generating
  🗏‹C11-FrontEnd/generated/c_grammar_fun.grm›
▪ In HPND: the ML-Yacc modified generator generating the two
  🗏‹C11-FrontEnd/generated/c_grammar_fun.grm.sig› and
  🗏‹C11-FrontEnd/generated/c_grammar_fun.grm.sml› (i.e., the ML-Yacc version of
  MLton).
▪ In HPND: the modified grammar library of ML-Yacc loaded in
  🗏‹C11-FrontEnd/src/C_Parser_Language.thy›.
▪ In 3-clause BSD: the remaining files in 🗀‹C11-FrontEnd/src› constituting
  Isabelle/C core implementation.
▪ Most examples in 🗀‹C11-FrontEnd/examples› are in 3-clause BSD, some are
  used for quotation purposes to test the Isabelle/C lexer (hyperlinks around each example detail
  their provenance).
›
```

</div>
