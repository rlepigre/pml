OCAMLBUILD := ocamlbuild -docflags -hide-warnings -use-ocamlfind -r

all: depchecks pml pml_doc parser

# Check for ocamlfind and ocamlbuild on the system.
HAS_OCAMLFIND  := $(shell which ocamlfind 2> /dev/null)
HAS_OCAMLBUILD := $(shell which ocamlbuild 2> /dev/null)

# Check for the bindlib and earley library.
HAS_BINDLIB    := $(shell ocamlfind query -format %p bindlib 2> /dev/null)
HAS_EARLEY     := $(shell ocamlfind query -format %p earley 2> /dev/null)

.PHONY: depchecks
depchecks:
ifndef HAS_OCAMLBUILD
	$(error "The ocamlbuild program is required...")
endif
ifndef HAS_OCAMLFIND
	$(error "The ocamlfind program is required...")
endif
ifndef HAS_BINDLIB
	$(error "The bindlib library is required...")
endif
ifndef HAS_EARLEY
	$(error "The earley library is required...")
endif

# Compilation of the pml.
.PHONY: pml pml_doc
pml: pml/pml.cmxa pml/pml.cma
pml_doc: pml/pml.docdir/index.html

KERNELFILES := $(wildcard pml/*.ml) $(wildcard pml/*.ml)

pml/pml.cmxa: $(KERNELFILES)
	$(OCAMLBUILD) -package bindlib -package earley $@

pml/pml.cma: $(KERNELFILES)
	$(OCAMLBUILD) -package bindlib -package earley $@

pml/pml.docdir/index.html: $(KERNELFILES)
	$(OCAMLBUILD) -package bindlib -package earley $@

# Compilation of the parser.
.PHONY: parser parser_doc
parser: parser/pml.byte

PARSERFILES := $(wildcard parser/*.ml) $(wildcard parser/*.ml)

parser/pml.byte: 
	$(OCAMLBUILD) -I pml -package bindlib -package earley,earley.str $@

clean:
	ocamlbuild -clean

distclean: clean
	rm -f *~ pml/*~ parser/*~ editors/*~ tests/*~
