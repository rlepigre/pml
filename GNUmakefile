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
	@cd book && rubber --unsafe -W all --module xelatex pml_book.tex

# Checks on the source code.
check:
	@sh tools/sanity_check.sh

# Lib target (PML handles the dependencies).
LIB_FILES = $(shell find lib -name "*.pml")
LIB_PMI   = $(LIB_FILES:.pml=.pmi)
$(LIB_PMI): $(LIB_FILES)
	dune exec -- pml --quiet --timed $(LIB_FILES)

.PHONY: lib
lib: $(LIB_PMI)

# Book test target, testing pml code in the book
.PHONY: book_tests
TEXPML= book/part1_doc/basics.pml \
        book/part1_doc/subtype.pml \
        book/part1_doc/dependent.pml \
        book/part1_doc/advanced.pml \
        book/part1_doc/solutions.pml
book_tests: $(LIB_PMI) $(TEXPML)
	dune exec -- pml --quiet --timed $(TEXPML)

# Test target.
.PHONY: tests
TEST_FILES = $(shell find examples tests -name "*.pml")
tests: $(LIB_PMI) $(TEST_FILES)
	dune exec -- pml --quiet --timed $(TEST_FILES)

.PHONY: all
all: lib tests book_tests

# target to mesure time
.PHONY: time
time: bin
	@find . -name \*.pmi -exec rm {} \;
	@/usr/bin/time -f "Finished in %E at %P with %MKb of RAM" make -s tests

.PHONY: clean_pmi
clean_pmi:
	@find . -name \*.pmi -exec rm {} \;

.PHONY: clean_mem
clean_mem: clean_pmi
	@find . -name \*.mem -exec rm {} \;

# Cleaning targets.
.PHONY: clean
clean: clean_pmi
	@dune clean
	@rm -f $(TEXPML)

distclean: clean clean_mem
	@rm -rf book/_minted* book/pml_book.pygmented book/pml_book.pyg
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name \#\* -exec rm {} \;
	@find . -type f -name .\#\* -exec rm {} \;
	@cd book && rubber --clean --module xelatex pml_book.tex

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
