# Take opam config if available.
ifeq (, $(shell which opam 2> /dev/null))
$(warning "We recommend using opam for dependencies.")
PREFIX   = /usr/local
BINDIR   = $(PREFIX)/bin
LIBDIR   = $(PREFIX)/lib
else
PREFIX   = $(shell opam config var prefix)
BINDIR   = $(shell opam config var bin)
LIBDIR   = $(shell opam config var lib)
endif

# Editors directory.
EMACSDIR = $(PREFIX)/emacs/site-lisp
VIMDIR   = $(HOME)/.vim

# Check for required binaries.
ifeq (, $(shell which ocamlbuild 2> /dev/null))
$(error "ocamlbuild is required... (try 'opam install ocamlbuild')")
endif
ifeq (, $(shell which ocamlfind 2> /dev/null))
$(error "ocamlfind is required... (try 'opam install ocamlfind')")
endif
ifeq (, $(shell which pa_ocaml 2> /dev/null))
$(error "pa_ocaml is required... (try 'opam install earley-ocaml')")
endif

# Check for required libraries.
ifeq (, $(shell ocamlfind query -format %p bindlib 2> /dev/null))
$(error "bindlib is required... (try 'opam install bindlib')")
endif
ifeq (, $(shell ocamlfind query -format %p earley 2> /dev/null))
$(error "earley is required... (try 'opam install earley earley-ocaml')")
endif

# Compilation commands and flags
OCAMLBUILD = ocamlbuild -use-ocamlfind -r -quiet
DOCFLAGS   = -docflags -hide-warnings

# Version.
VERSION  = 2.0.1_thesis

# Main target.
.PHONY: all
all: main.native lib check

# Documentation targets.
.PHONY: doc
doc: util_doc kernel_doc

.PHONY: util_doc
util_doc: _build/util/util.docdir/index.html
_build/util/util.docdir/index.html: $(UTILFILES)
	$(OCAMLBUILD) $(DOCFLAGS) util/util.docdir/index.html

.PHONY: kernel_doc
kernel_doc: _build/kernel/kernel.docdir/index.html
_build/kernel/kernel.docdir/index.html: $(KERNELFILES)
	$(OCAMLBUILD) $(DOCFLAGS) kernel/kernel.docdir/index.html

# Configuration file.
pml2/config.ml: GNUmakefile
	@echo "let path = [\"$(LIBDIR)/pml2\"]" > $@

ML_FILES = $(wildcard */*.ml) pml2/config.ml

# Compilation of PML2.
main.native: _build/pml2/main.native
_build/pml2/main.native: $(ML_FILES)
	@rm -f main.native
	$(OCAMLBUILD) pml2/main.native

# Checks on the source code.
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

# Lib target (PML handles the dependencies).
.PHONY: lib
LIB_FILES = $(wildcard lib/*.pml)
lib: main.native $(LIB_FILES)
	@for f in $(LIB_FILES); do ./main.native --quiet $$f || break ; done

# Test target.
.PHONY: test
TEST_FILES = $(wildcard examples/*.pml test/*.pml test/phd_examples/*.pml)
test: main.native lib $(TEST_FILES)
	@for f in $(TEST_FILES); do ./main.native --quiet $$f || break ; done

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
install: main.native lib install_emacs install_vim
	install -d $(BINDIR)
	install -m 755 $< $(BINDIR)/pml2
	@echo -e "\e[36m\"pml2\" binary installed.\e[39m"
	install -d $(LIBDIR)/pml2/lib
	install -m 644 $(PML_FILES) $(PMI_FILES) $(LIBDIR)/pml2/lib
	@echo -e "\e[36mPML library installed.\e[39m"

# Release.
.PHONY: release
release: distclean
	git push origin
	git tag -a pml_$(VERSION)
	git push origin pml_$(VERSION)
