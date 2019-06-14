# Isabelle/C

Isabelle/C contains a C11 front-end support for Isabelle.

The code requires Isabelle2018, and the C examples loading can be executed as
follows:

```console
isabelle jedit -d C11-FrontEnd C11-FrontEnd/examples/C1.thy
isabelle jedit -d C11-FrontEnd C11-FrontEnd/examples/C2.thy
isabelle jedit -d C11-FrontEnd C11-FrontEnd/examples/C3.thy
```

```console
export L4V_ARCH = ARM # the same effect can be made in ~/.isabelle/etc/settings
isabelle jedit -d . -l CParser C11-FrontEnd/semantic-backends/AutoCorres/TestSEL4.thy
isabelle jedit -d . -l AutoCorres C11-FrontEnd/semantic-backends/AutoCorres/IsPrime_integrated.thy
```

For the last examples, we were used to see a sub-window ``Bad session
structure`` appearing, but it has been fixed. Nevertheless, if it still does
appear: after a click on ``OK``, the compilation will correctly start.

Additionally, ``run_tests`` can be executed in ``l4v/src/``, and interrupted
once the success of ``CBaseRefine`` obtained. Then, to test the interactive
version of AutoCorres, it would suffice to run the following command:
```console
isabelle build -d l4v/src -b -v AutoCorresSEL4
```

Note: The version of the [l4v](https://github.com/seL4/l4v/) project used is
[seL4-10.1.1](https://github.com/seL4/l4v/releases/tag/seL4-10.1.1).

## Authors
* [Frédéric Tuong](https://www.lri.fr/~ftuong/)
* [Burkhart Wolff](https://www.lri.fr/~wolff/)

## License
This project is licensed under a 3-clause BSD-style license.
