include Makefile.config

OCAMLBUILD := ocamlbuild -docflags -hide-warnings -use-ocamlfind -r -quiet

all: pml2 lib check

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
util: _build/util/util.cmxa
util_byte: _build/util/util.cma
util_doc: _build/util/util.docdir/index.html

UTILFILES := $(wildcard util/*.ml) $(wildcard util/*.mli)

_build/util/util.cmxa: $(UTILFILES)
	$(OCAMLBUILD) util/util.cmxa

_build/util/util.cma: $(UTILFILES)
	$(OCAMLBUILD) util/util.cma

_build/util/util.docdir/index.html: $(UTILFILES)
	$(OCAMLBUILD) util/util.docdir/index.html

# Compilation of the kernel.
.PHONY: kernel kernel_byte kernel_doc
kernel: _build/kernel/kernel.cmxa
kernel_byte: _build/kernel/kernel.cma
kernel_doc: _build/kernel/kernel.docdir/index.html

KERNELFILES := $(wildcard kernel/*.ml) $(wildcard kernel/*.mli)

_build/kernel/kernel.cmxa: $(KERNELFILES)
	$(OCAMLBUILD) kernel/kernel.cmxa

_build/kernel/kernel.cma: $(KERNELFILES)
	$(OCAMLBUILD) kernel/kernel.cma

_build/kernel/kernel.docdir/index.html: $(KERNELFILES)
	$(OCAMLBUILD) kernel/kernel.docdir/index.html

# Compilation of the parser.
.PHONY: parser parser_byte
parser: _build/parser/parser.cmxa
parser_byte: _build/parser/parser.cma

PARSERFILES := $(wildcard parser/*.ml) $(wildcard parser/*.mli)

_build/parser/parser.cmxa: $(KERNELFILES)
	$(OCAMLBUILD) parser/parser.cmxa

_build/parser/parser.cma: $(KERNELFILES)
	$(OCAMLBUILD) parser/parser.cma

# Compilation of PML2.
.PHONY: pml2 pml2_byte
pml2: _build/pml2/main.native
pml2_byte: _build/pml2/main.byte

main.byte: _build/pml2/main.byte
main.native: _build/pml2/main.native

pml2/main.ml.depends: pml2/config.ml
pml2/config.ml: GNUmakefile
	echo "let path = [\".\" ; \"$(LIBDIR)\"]" > $@

ML_FILES = $(wildcard */*.ml) pml2/config.ml

_build/pml2/main.native: $(ML_FILES)
	@rm -f main.native
	$(OCAMLBUILD) pml2/main.native

_build/pml2/main.byte: $(ML_FILES)
	@rm -f main.byte
	$(OCAMLBUILD) pml2/main.byte

check:
	@f=`grep FIXME */*.ml */*.mli | wc -l`;\
	 ft=`grep FIXME */*.ml */*.mli | grep -P -v '#[0-9]+' | wc -l`;\
	 echo FIXME: $$ft/$$f '(without ticket/all)'
	@grep FIXME */*.ml */*.mli -n | grep -P -v '#[0-9]+' || true
	@f=`grep TODO */*.ml */*.mli | wc -l`;\
	 ft=`grep TODO */*.ml */*.mli | grep -P -v '#[0-9]+' | wc -l`;\
	 echo TODO: $$ft/$$f '(without ticket/all)'
	@grep TODO */*.ml */*.mli -n | grep -P -v '#[0-9]+' || true
	@echo Lines with TAB:
	@grep -P "\t" */*.ml */*.mli; true
	@echo Lines too long:
	@wc -L */*.ml */*.mli | grep -e "\([89][0-9]\)\|\([1-9][0-9][0-9]\)"; true


# Lib target
# NOTE: PML is doing the dependencies analysis himself
.PHONY: lib
LIB_FILES = $(wildcard lib/*.pml)
lib: main.native $(LIB_FILES)
	@for f in $(LIB_FILES); do ./main.native --quiet $$f || break ; done

# Test target.
.PHONY: test
TEST_FILES = $(wildcard examples/*.pml test/*.pml test/phd_examples/*.pml)
test: main.native lib $(TEST_FILES)
	@for f in $(TEST_FILES); do ./main.native --quiet $$f || break ; done

# Cleaning targets.
clean: libclean
	@ocamlbuild -clean

libclean:
	@find . -name \*.pmi -exec rm {} \;

distclean: clean
	@find . -name \*~ -exec rm {} \;

.PHONY: install_vim
# Install for the vim mode.
install_vim: editors/vim/indent/pml.vim editors/vim/syntax/pml.vim
	cp editors/vim/syntax/pml.vim ~/.vim/syntax/pml.vim
	cp editors/vim/indent/pml.vim ~/.vim/indent/pml.vim
	@echo -e "\e[36m==== Add the following to '$(HOME)/.vimrc'\e[39m"
	@echo "au BufRead,BufNewFile *.pml set filetype=pml"
	@echo "au! Syntax pml source $(HOME)/.vim/syntax/pml.vim"
	@echo "autocmd BufEnter *.pml source $(HOME)/.vim/indent/pml.vim"
	@echo -e "\e[36m==== Add the above to '$(HOME)/.vimrc'\e[39m"

.PHONY: install_emacs
install_emacs: editors/emacs/pml2-mode.el
	if [ -d $(EMACSDIR) ]; then \
	  install -d $(EMACSDIR) ;\
	  install -m 0644 editors/emacs/pml2-mode.el $(EMACSDIR) ;\
	  install -m 0755 editors/emacs/pml2-indent.sh $(BINDIR)/pml2-indent ;\
	fi

# Install.
.PHONY: install
PML_FILES = $(wildcard lib/*.pml)
PMI_FILES = $(PML_FILES:.pml=.pmi)
install: main.native $(PML_FILES) lib install_emacs
	install -d $(BINDIR)
	install -m 0755 $< $(BINDIR)/pml2
	install -d $(LIBDIR)
	install -m 0644 lib/*.pml $(LIBDIR)
	install -m 0644 lib/*.pmi $(LIBDIR)
