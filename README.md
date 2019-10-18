<div class="source">

``` {.source}
section ‹Isabelle/C›

text ‹
Isabelle/C contains a C99/C11/C18 front-end support for Isabelle. The front-end is actually composed
of two possibly interchangeable parsers (from two different projects):

▪ 🗀‹C11-FrontEnd›: 🌐‹https://hackage.haskell.org/package/language-c›
▪ 🌐‹https://gitlri.lri.fr/ftuong/isabelle_c/tree/C/C18-FrontEnd›:
  🌐‹https://github.com/jhjourdan/C11parser›

Thus, one can select which parser(s) are better suitable to be enabled in front of a piece of C
code.

Isabelle/C requires Isabelle2019. For a first start, the following C examples or entry-points of
documentation can be executed:

▪ ▩‹isabelle jedit -d› 🗀‹C11-FrontEnd› 🗏‹C11-FrontEnd/examples/C1.thy›
▪ ▩‹isabelle jedit -d› 🗀‹C11-FrontEnd› 🗏‹C11-FrontEnd/examples/C2.thy›
▪ ▩‹isabelle jedit -d› 🗀‹C11-FrontEnd› 🗏‹C11-FrontEnd/C_Appendices.thy›
›

text ‹
The AFP version of Isabelle/C does not include semantic back-ends. However, the structure of
🗀‹.› has been designed to let one easily create a directory
‹C11-BackEnds› for possibly supporting new back-ends of interests. The structure of
🗀‹.› is actually similar as
🌐‹https://gitlri.lri.fr/ftuong/isabelle_c›: see for example
🌐‹https://gitlri.lri.fr/ftuong/isabelle_c/tree/C/C11-BackEnds› where several
back-ends can be copied and tried.
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
