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
 - https://doi.org/10.4230/LIPIcs.TYPES.2017.4 (introductory paper),
 - https://tel.archives-ouvertes.fr/tel-01682908 (R. Lepigre's PhD thesis),
 - https://doi.org/10.1007/978-3-662-49498-1_19 (paper related to the model),
 - https://doi.org/10.1145/3285955 (paper related to subtyping),
 - https://github.com/rlepigre/subml (the SubML language).

Dependencies and compilation
----------------------------

PML₂ requiere a Unix-like system. It should work well on Linux as well as on
MacOS. It might also be possible to make it work on Windows with Cygwyn or
with "bash on Windows").

List of dependencies:
 - GNU make,
 - OCaml (at least 4.04.0) with Opam,
 - dune (at least 1.7.0),
 - bindlib 5.0.1 (https://github.com/rlepigre/ocaml-bindlib),
 - earley 2.0.0 (https://github.com/rlepigre/ocaml-earley).

Using Opam, a suitable OCaml environment can be setup as follows.
```bash
opam switch 4.05.0
eval `opam config env`
opam install dune>=1.7.0 bindlib.5.0.1 earley.2.0.0
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

This folder contains files related to the PML project.

The source files can be found in the following folders:
 - `src/util` contains a set of libraries not directly related to PML,
 - `src/parser` contains a low level AST of the language and the parser,
 - `src/kernel` contains the core of PML (type checking, equivalence, AST...),
 - `src/pml.ml` is the main program.

Other directories:
 - `editors` contains PML modes for editors (vim and emacs only),
 - `lib` contains the PML standard library (very small),
 - `test` contains most of our examples of PML programs,

The directories `tmp` and `attic` are not relevant as the contain files used
for debugging the newest features including termination checking and old code
that we want to keep somewhere.

Support for the Vim (or Neovim) editor
--------------------------------------

After installing PML (with `make install`), you will need to add the
following lines to you `.vimrc` file (if they are not already present).
```vim
" PML stuff
let g:opamshare = substitute(system('opam config var share'),'\n$','','''')
execute "set rtp+=" . g:opamshare . "/pml/vim"
```

Note that it may be necessary for these lines to appear before the
following line.
```vim
filetype plugin indent on
```

Support for the Emacs editor
----------------------------

After installing PML (with `make install`), you will need to add the
following lines to you `.emacs` file.
```elisp
;; PML stuff
(load "pml-mode")
```

Where to start in the code
--------------------------

My advice to start looking at the code would be to take a look at the three
different abstract syntax representations.
 - The main abstract syntax is implemented as a GADT in `src/kernel/ast.ml`,
 - The abstract syntax after parsing can be found in `src/parser/raw.ml`,
   together with the first level of type checking (sorting),
 - The graph representation of terms for the decision of equivalence can be
   found in `src/kernel/equiv.ml`.

The implementation of type checking can be found in `src/kernel/typing.ml`,
and the function for comparing expressions (including the unification
functions) are in `src/kernel/compare.ml`.
