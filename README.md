# Isabelle/C

Isabelle/C contains a C11 front-end support for Isabelle.

The code requires Isabelle2018. For a first start, the following C examples or
entry-points of documentation can be executed:

```console
isabelle jedit -d C11-FrontEnd C11-FrontEnd/examples/C1.thy
isabelle jedit -d C11-FrontEnd C11-FrontEnd/examples/C2.thy
isabelle jedit -d C11-FrontEnd C11-FrontEnd/examples/C3.thy
isabelle jedit -d C11-FrontEnd C11-FrontEnd/C_Appendices.thy
```

Certain examples in ``C11-FrontEnd`` actually require to change the initial
directory provided to ``isabelle jedit``, because they might depend on other
projects (such as ``l4v``):

```console
export L4V_ARCH = ARM # the same effect can be made in ~/.isabelle/etc/settings
isabelle jedit -d . -l CParser C11-FrontEnd/semantic-backends/AutoCorres/TestSEL4.thy
isabelle jedit -d . -l AutoCorres C11-FrontEnd/semantic-backends/AutoCorres/IsPrime_integrated.thy
```

For the last examples, we were used to see a sub-window ``Bad session
structure`` appearing just after starting Isabelle. Nevertheless, if this ever
happens again, the sub-window can be ignored by clicking on ``OK``.

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
