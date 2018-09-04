The PML₂ programming language and proof assistant
=================================================

The PML₂ language provides a uniform environment for programming, and for
proving properties of programs in an ML-like setting.  The language is
Curry-style and call-by-value, it provides a control operator (interpreted in
terms of classical logic), it supports general recursion and a very general
form of (implicit, non-coercive) subtyping. In the system, equational
properties of programs are expressed using two new type formers, and they are
proved by constructing terminating programs. Although proofs rely heavily on
equational reasoning, equalities are exclusively managed by the type-checker.
This means that the user only has to choose which equality to use, and not
where to use it, as is usually done in mathematical proofs. In the system,
writing proofs mostly amounts to applying lemmas (possibly recursive function
calls), and to perform case analyses (pattern matchings).

Related documents and prototypes:
 - http://lepigre.fr/files/docs/lepigre2017_pml2.pdf (introductory paper),
 - https://tel.archives-ouvertes.fr/tel-01590363 (R. Lepigre's PhD thesis),
 - https://doi.org/10.1007/978-3-662-49498-1_19 (paper related to the model),
 - https://github.com/rlepigre/subml (the SubML language).

Dependencies and compilation
----------------------------

PML₂ requiere a Unix-like system. It should work well on Linux as well as on
MacOS. It might also be possible to make it work on Windows with Cygwyn or
with "bash on Windows").

List of dependencies:
 - GNU make,
 - OCaml (at least 4.04.0),
 - ocamlbuild,
 - findlib,
 - bindlib 4.0.5 (https://github.com/rlepigre/ocaml-bindlib),
 - earley 1.0.0 (https://github.com/rlepigre/ocaml-earley),
 - earley-ocaml 1.0.0 (https://github.com/rlepigre/ocaml-earley-ocaml).

Using Opam, a suitable OCaml environment can be setup as follows.
```bash
opam switch 4.05.0
eval `opam config env`
opam install ocamlfind ocamlbuild
opam install bindlib.4.0.5 earley.1.0.2 earley-ocaml.1.0.2
```

To compile PML₂, just run the command `make` in the source directory. This
produces the `main.native` binary, which can be run on files with the `.pml`
extension (use `./main.native --help` for more informations).

```bash
make
make install   # optionally install the program.
make doc       # optionally produce the ocamldoc documentation
```

Organization of the repository
------------------------------

This folder contains files related to the PML2 project.

The source files can be found in the following folders:
 - `util` contains a set of libraries not directly related to PML2,
 - `parser` contains a low level AST of the language and the parser,
 - `kernel` contains the core of PML2 (type checking, equivalence, AST...),
 - `pml2` contains the main program.

Other directories:
 - `editors` contains PML2 modes for editors (vim and emacs only),
 - `lib` contains the PML2 standard library (very small),
 - `test` contains most of our examples of PML2 programs,

The directories `tmp` and `attic` are not relevant as the contain files used
for debugging the newest features including termination checking and old code
that we want to keep somewhere.

Where to start in the code
--------------------------

My advice to start looking at the code would be to take a look at the three
different abstract syntax representations.
 - The main abstract syntax is implemented as a GADT in `kernel/ast.ml`,
 - The abstract syntax after parsing can be found in `parser/raw.ml`, together
   with the first level of type checking (sorting),
 - The graph representation of terms for the decision of equivalence can be
   found in `ast/equiv.ml`.

The implementation of type checking can be found in `kernel/typing.ml`, and
the function for comparing expressions (including the unification functions)
are in `kernel/compare.ml`.
