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
HAS_PA_OCAML   := $(shell which pa_ocaml 2> /dev/null)

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
ifndef HAS_PA_OCAML
	$(error "The pa_ocaml (earley-ocaml) is required...")
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
main.p.native: _build/pml2/main.p.native

pml2/config.ml: GNUmakefile
	@echo "let path = [\"$(LIBDIR)/pml2\"]" > $@

ML_FILES = $(wildcard */*.ml) pml2/config.ml

_build/pml2/main.native: $(ML_FILES)
	@rm -f main.native
	$(OCAMLBUILD) pml2/main.native

_build/pml2/main.byte: $(ML_FILES)
	@rm -f main.byte
	$(OCAMLBUILD) -cflags -g -lflag -g  pml2/main.byte

_build/pml2/main.p.native: $(ML_FILES)
	@rm -f main.p.native
	$(OCAMLBUILD) -cflags -ccopt,-no-pie -lflags -ccopt,-no-pie pml2/main.p.native

# Checks on the source code.
check:
	# FIXME/TODO
	@f=`grep FIXME */*.ml */*.mli */*.pml */*/*.pml  | wc -l`;\
	 ft=`grep FIXME */*.ml */*.mli */*.pml */*/*.pml | grep -P -v '#[0-9]+' | wc -l`;\
	 echo FIXME: $$ft/$$f '(without ticket/all)'
	@grep FIXME */*.ml */*.mli */*.pml */*/*.pml -n | grep -P -v '#[0-9]+' || true
	@f=`grep TODO */*.ml */*.mli */*.pml */*/*.pml | wc -l`;\
	 ft=`grep TODO */*.ml */*.mli */*.pml */*/*.pml | grep -P -v '#[0-9]+' | wc -l`;\
	 echo TODO: $$ft/$$f '(without ticket/all)'
	@grep TODO */*.ml */*.mli */*.pml */*/*.pml -n | grep -P -v '#[0-9]+' || true
	# TAB/LINES TOO LONG
	@echo Lines with TAB:
	@grep -P "\t" */*.ml */*.mli; true
	@echo Lines too long:
	@grep -n -x '^.\{80\}' */*.ml */*.mli

# Lib target (PML handles the dependencies).
.PHONY: lib
LIB_FILES = $(wildcard lib/*.pml)
lib: main.native $(LIB_FILES)
	@for f in $(LIB_FILES); do ./main.native --quiet $$f || break ; done

# Test target.
.PHONY: test
TEST_FILES = $(wildcard examples/*.pml test/*.pml test/phd_examples/*.pml)
test: main.native lib $(TEST_FILES)
	@for f in $(TEST_FILES); do echo $$f; ./main.native --quiet $$f || break ; done

# target to mesure time
.PHONY: time
time:
	make libclean
	time make lib test

# Cleaning targets.
clean: libclean
	@ocamlbuild -clean

libclean:
	@find . -name \*.pmi -exec rm {} \;

distclean: clean
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name \#\* -exec rm {} \;
	@find . -type f -name .\#\* -exec rm {} \;
	@rm -f pml2/config.ml

# Install for the vim mode (in the user's directory).
.PHONY: install_vim
install_vim: editors/vim/indent/pml.vim editors/vim/syntax/pml.vim
ifeq ($(wildcard $(VIMDIR)/.),)
	@echo -e "\e[36mWill not install vim mode.\e[39m"
else
	install -d $(VIMDIR)/syntax
	install -d $(VIMDIR)/indent
	install -d $(VIMDIR)/ftdetect
	install -m 644 editors/vim/syntax/pml.vim $(VIMDIR)/syntax
	install -m 644 editors/vim/indent/pml.vim $(VIMDIR)/indent
	install -m 644 editors/vim/ftdetect/pml.vim $(VIMDIR)/ftdetect
	@echo -e "\e[36mVim mode installed.\e[39m"
endif

# Install for the emacs mode (system-wide).
.PHONY: install_emacs
install_emacs: editors/emacs/pml2-mode.el
ifeq ($(wildcard $(EMACSDIR)/.),)
	@echo -e "\e[36mWill not install emacs mode.\e[39m"
else
	install -d $(EMACSDIR)
	install -m 644 editors/emacs/pml2-mode.el $(EMACSDIR)
	install -m 755 editors/emacs/pml2-indent.sh $(BINDIR)/pml2-indent
	@echo -e "\e[36mEmacs mode installed.\e[39m"
endif

# Install.
.PHONY: install
PML_FILES = $(wildcard lib/*.pml)
PMI_FILES = $(PML_FILES:.pml=.pmi)
install: main.native $(PML_FILES) lib install_emacs
	install -d $(BINDIR)
	install -m 755 $< $(BINDIR)/pml2
	install -d $(LIBDIR)/pml2/lib
	install -m 644 $(PML_FILES) $(LIBDIR)/pml2/lib
	install -m 644 $(PMI_FILES) $(LIBDIR)/pml2/lib

# Release.
.PHONY: release
release: distclean
	git push origin
	git tag -a pml_$(VERSION)
	git push origin pml_$(VERSION)
