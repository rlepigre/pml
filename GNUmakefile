# Editors directory.
VIMDIR   = $(HOME)/.vim

# Version.
VERSION  = devel

# Main target.
.PHONY: all
all: bin

.PHONY: bin
bin:
	@dune build

# Documentation.
.PHONY: book
book: book/pml_book.pdf

book/pml_book.pdf: book/biblio.bib $(shell find book -name "*.tex")
	@cd book && rubber --pdf pml_book.tex

# Checks on the source code.
check:
	@sh tools/sanity_check.sh

# Lib target (PML handles the dependencies).
.PHONY: lib
LIB_FILES = $(wildcard lib/*.pml)
lib: bin $(LIB_FILES)
	@for f in $(LIB_FILES); do dune exec -- pml --quiet $$f || break ; done

# Test target.
.PHONY: tests
TEST_FILES = $(wildcard examples/*.pml tests/*.pml tests/*/*.pml)
tests: bin lib $(TEST_FILES)
	@for f in $(TEST_FILES); do echo $$f; dune exec -- pml --quiet $$f || break ; done

# target to mesure time
.PHONY: time
time:
	make libclean
	time make lib test

# Cleaning targets.
clean: libclean
	@dune clean

libclean:
	@find . -name \*.pmi -exec rm {} \;
	@find . -name \*.vo -exec rm {} \;
	@find . -name \*.vo.aux -exec rm {} \;
	@find . -name \*.glob -exec rm {} \;
	@find . -name \*.agdai -exec rm {} \;

distclean: clean
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name \#\* -exec rm {} \;
	@find . -type f -name .\#\* -exec rm {} \;
	@rm -f src/config.ml
	@cd book && rubber --clean --pdf pml_book.tex

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

# Install.
.PHONY: install
install: bin
	@dune install

# Release.
.PHONY: release
release: distclean
	git push origin
	git tag -a pml_$(VERSION)
	git push origin pml_$(VERSION)
