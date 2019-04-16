# C11 Front-End

This project contains a C11 Front-End support for Isabelle.

The code requires Isabelle2018, and the C examples loading can be
executed as follows:

isabelle jedit C11-FrontEnd/examples/C1.thy
isabelle jedit C11-FrontEnd/examples/C2.thy
isabelle jedit C11-FrontEnd/examples/C3.thy

isabelle jedit -d l4v/src l4v/examples/TestSEL4.thy

For the last example, a sub-window 'Bad session structure' will be
opened, but this can be ignored: after a click on 'OK', the
compilation will correctly start.

Additionally, `run_tests` can be executed in `l4v/src/`, and
interrupted once the success of CBaseRefine obtained. Then, to test
the interactive version of autocorres, it would suffice to run the
following command:
isabelle build -d l4v/src -b -v AutoCorresSEL4


As short note, the version of the l4v project used is seL4-10.1.1.

## Authors
* [Frédéric Tuong](https://www.lri.fr/~ftuong/)
* [Burkhart Wolff](https://www.lri.fr/~wolff/)

## License
This project is licensed under a 3-clause BSD-style license.
