OCAMLBUILD := ocamlbuild -docflags -hide-warnings -use-ocamlfind -r

all: depchecks pml pml_doc

# Check for ocamlfind and ocamlbuild on the system.
HAS_OCAMLFIND  := $(shell which ocamlfind 2> /dev/null)
HAS_OCAMLBUILD := $(shell which ocamlbuild 2> /dev/null)

# Check for the bindlib and decap library.
HAS_BINDLIB    := $(shell ocamlfind query -format %p bindlib 2> /dev/null)
HAS_DECAP      := $(shell ocamlfind query -format %p decap 2> /dev/null)

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
ifndef HAS_DECAP
	$(error "The decap library is required...")
endif

# Compilation of the pml.
.PHONY: pml pml_doc
pml: pml/pml.cmxa pml/pml.cma
pml_doc: pml/pml.docdir/index.html

KERNELIMPL := $(wildcard pml/*.ml)
KERNELINTF := $(wildcard pml/*.ml)

pml/pml.cmxa: $(KERNELIMPL) $(KERNELINTF)
	$(OCAMLBUILD) -package bindlib -package decap $@

pml/pml.cma: $(KERNELIMPL) $(KERNELINTF)
	$(OCAMLBUILD) -package bindlib -package decap $@

pml/pml.docdir/index.html: $(KERNELIMPL) $(KERNELINTF)
	$(OCAMLBUILD) -package bindlib -package decap $@

clean:
	ocamlbuild -clean

distclean: clean
	rm -f *~ pml/*~
