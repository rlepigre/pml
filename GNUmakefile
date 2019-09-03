VERSION = devel

# Main target.
.PHONY: all
all: bin

.PHONY: bin
bin:
	@dune build

# Documentation.
.PHONY: book
book: book/pml_book.pdf

book/pml_book.pdf: book/biblio.bib book/pml.py $(shell find book -name "*.tex")
	@rm -rf book/_minted*
	@cd book && rubber --unsafe -W all --pdf pml_book.tex

# Checks on the source code.
check:
	@sh tools/sanity_check.sh

# Lib target (PML handles the dependencies).
.PHONY: lib
LIB_FILES = $(shell find lib -name "*.pml")
lib: bin $(LIB_FILES)
	dune exec -- pml --quiet --timed $(LIB_FILES)

# Book test target, testing pml code in the book
.PHONY: book_tests
TEXPML= book/part1_doc/basics.pml \
        book/part1_doc/subtype.pml \
        book/part1_doc/dependent.pml \
        book/part1_doc/advanced.pml \
        book/part1_doc/solutions.pml
book_tests: bin lib $(TEXPML)
	@for f in $(TEXPML); do \
     echo $$f; \
     dune exec -- pml --quiet $$f || break ; \
   done

# Test target.
.PHONY: tests
TEST_FILES = $(shell find examples tests -name "*.pml")
tests: bin lib $(TEST_FILES)
	@for f in $(TEST_FILES); do \
     echo $$f; \
     dune exec -- pml --quiet $$f || break ; \
   done

# target to mesure time
.PHONY: time
time: bin
	@find . -name \*.pmi -exec rm {} \;
	@/usr/bin/time -f "Finished in %E at %P with %MKb of RAM" make -s tests

# Cleaning targets.
clean:
	@find . -name \*.pmi -exec rm {} \;
	@dune clean
	@rm -f $(TEXPML)

distclean: clean
	@rm -rf book/_minted* book/pml_book.pygmented
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name \#\* -exec rm {} \;
	@find . -type f -name .\#\* -exec rm {} \;
	@cd book && rubber --clean --pdf pml_book.tex

# Install.
.PHONY: install
install: bin
	@dune install

.PHONY: uninstall
uninstall:
	@dune uninstall

# Release.
.PHONY: release
release: distclean
	git push origin
	git tag -a pml_$(VERSION)
	git push origin pml_$(VERSION)

%.pml: %.tex
	dune exec -- extract_pmlcode $< $@
