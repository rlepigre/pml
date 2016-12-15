OCAMLBUILD := ocamlbuild -docflags -hide-warnings -use-ocamlfind -r

all: pml2

.PHONY: libs libs_byte doc
doc: depchecks kernel_doc util_doc
libs: depchecks kernel util parser
libs_byte: depchecks kernel_byte util_byte parser_byte

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

# Compilation of the util modules.
.PHONY: util util_byte util_doc
util: util/util.cmxa
util_byte: util/util.cma
util_doc: util/util.docdir/index.html

UTILFILES := $(wildcard util/*.ml) $(wildcard util/*.mli)

util/util.cmxa: $(UTILFILES)
	$(OCAMLBUILD) -package unix $@

util/util.cma: $(UTILFILES)
	$(OCAMLBUILD) -package unix $@

util/util.docdir/index.html: $(UTILFILES)
	$(OCAMLBUILD) -package bindlib -package unix $@

# Compilation of the kernel.
.PHONY: kernel kernel_byte kernel_doc
kernel: kernel/kernel.cmxa
kernel_byte: kernel/kernel.cma
kernel_doc: kernel/kernel.docdir/index.html

KERNELFILES := $(wildcard kernel/*.ml) $(wildcard kernel/*.mli)

kernel/kernel.cmxa: $(KERNELFILES)
	$(OCAMLBUILD) -package bindlib,earley $@

kernel/kernel.cma: $(KERNELFILES)
	$(OCAMLBUILD) -package bindlib,earley $@

kernel/kernel.docdir/index.html: $(KERNELFILES)
	$(OCAMLBUILD) -package bindlib,earley $@

# Compilation of the parser.
.PHONY: parser parser_byte
parser: parser/parser.cmxa
parser_byte: parser/parser.cma

PARSERFILES := $(wildcard parser/*.ml) $(wildcard parser/*.mli)

parser/parser.cmxa: $(KERNELFILES)
	$(OCAMLBUILD) -package bindlib,earley,earley.str $@

parser/parser.cma: $(KERNELFILES)
	$(OCAMLBUILD) -package bindlib,earley,earley.str $@

# Compilation of PML2.
.PHONY: pml2 pml2_byte
pml2: pml2/main.native
pml2_byte: pml2/main.byte

pml2/main.native:
	$(OCAMLBUILD) -package unix,bindlib,earley,earley.str $@

pml2/main.byte:
	$(OCAMLBUILD) -package unix,bindlib,earley,earley.str $@

# Cleaning targets.
clean:
	ocamlbuild -clean

distclean: clean
	rm -f *~ pml2/*~ kernel/*~ parser/*~ editor/*~ doc/*~ test/*~ util/*~
