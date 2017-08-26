OCAMLBUILD := ocamlbuild -docflags -hide-warnings -use-ocamlfind -r

all: pml2 check

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
	$(OCAMLBUILD) $@

util/util.cma: $(UTILFILES)
	$(OCAMLBUILD) $@

util/util.docdir/index.html: $(UTILFILES)
	$(OCAMLBUILD) $@

# Compilation of the kernel.
.PHONY: kernel kernel_byte kernel_doc
kernel: kernel/kernel.cmxa
kernel_byte: kernel/kernel.cma
kernel_doc: kernel/kernel.docdir/index.html

KERNELFILES := $(wildcard kernel/*.ml) $(wildcard kernel/*.mli)

kernel/kernel.cmxa: $(KERNELFILES)
	$(OCAMLBUILD) $@

kernel/kernel.cma: $(KERNELFILES)
	$(OCAMLBUILD) $@

kernel/kernel.docdir/index.html: $(KERNELFILES)
	$(OCAMLBUILD) $@

# Compilation of the parser.
.PHONY: parser parser_byte
parser: parser/parser.cmxa
parser_byte: parser/parser.cma

PARSERFILES := $(wildcard parser/*.ml) $(wildcard parser/*.mli)

parser/parser.cmxa: $(KERNELFILES)
	$(OCAMLBUILD) $@

parser/parser.cma: $(KERNELFILES)
	$(OCAMLBUILD) $@

# Compilation of PML2.
.PHONY: pml2 pml2_byte
pml2: pml2/main.native
pml2_byte: pml2/main.byte

main.byte: pml2/main.byte
main.native: pml2/main.native

pml2/main.native:
	@rm -f main.native
	$(OCAMLBUILD) $@

pml2/main.byte:
	@rm -f main.byte
	$(OCAMLBUILD) $@

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


# Test target.
.PHONY: test
TEST_FILES = $(wildcard lib/*.pml examples/*.pml test/*.pml test/phd_examples/*.pml)
test: main.native $(TEST_FILES)
	@for f in $(TEST_FILES); do ./main.native --quiet $$f || break ; done

# Cleaning targets.
clean: libclean
	ocamlbuild -clean

libclean:
	find . -name \*.pmi -exec rm {} \;

distclean: clean
	rm -f *~ pml2/*~ kernel/*~ parser/*~ editor/*~ doc/*~ test/*~ util/*~

# Install for the vim mode.
install_vim: editors/vim/indent/pml.vim editors/vim/syntax/pml.vim
	cp editors/vim/syntax/pml.vim ~/.vim/syntax/pml.vim
	cp editors/vim/indent/pml.vim ~/.vim/indent/pml.vim
	@echo -e "\e[36m==== Add the following to '$(HOME)/.vimrc'\e[39m"
	@echo "au BufRead,BufNewFile *.pml set filetype=pml"
	@echo "au! Syntax pml source $(HOME)/.vim/syntax/pml.vim"
	@echo "autocmd BufEnter *.pml source $(HOME)/.vim/indent/pml.vim"
	@echo -e "\e[36m==== Add the above to '$(HOME)/.vimrc'\e[39m"

# Install.
PML_FILES = $(wildcard lib/*.pml)
PMI_FILES = $(PML_FILES:.pml=.pmi)
install: main.native $(PML_FILES) $(PMI_FILES)
	install -d /usr/local/bin
	install $< /usr/local/bin/pml2
	install -d /usr/local/lib/pml2
	install -d /usr/local/lib/pml2/lib
	install lib/*.pml /usr/local/lib/pml2/lib
	install lib/*.pmi /usr/local/lib/pml2/lib
