.PHONY: build configure doc install pinstall gen-types

## Silent by default
V =
ifeq ($(strip $(V)),)
        E = @echo
        Q = @
else
        E = @\#
        Q =
endif
export E Q

include config.mk
PWD:=$(shell pwd)

# These file lists are for generating dummy headers for c compilation
PASS_TEST_COGENT_FILES := $(wildcard tests/pass_*.cogent)
FAIL_TEST_COGENT_FILES := $(wildcard tests/fail_*.cogent)
DUMMY_HEADER_FILES := $(addprefix tests/include/,$(notdir $(PASS_TEST_COGENT_FILES:.cogent=_dummy.h)))

all: install
	$(E) "Cogent Compiler successfully built for $(OS)."
	$(E)
	$(E) "Add 'cogent' compiler to your path by running:"
	$(E) '  export PATH=$$PATH:$(PWD)/.cabal-sandbox/bin/'
	$(E)
	$(E) "To enable bash auto-completion for 'cogent', please add the following to your .bashrc file:"
	$(E) "source $(PWD)/misc/cogent_autocomplete.sh"
	$(E)
	$(E)

install: build
	$(E) "Installing.."
	$(CABAL) install $(CABALFLAGS)

pinstall: CABALFLAGS += --enable-executable-profiling
pinstall: setup-config
	$(CABAL) install $(CABALFLAGS)

build: setup-config
	$(E) "Building..."
	$(CABAL) build

configure: install-deps
	$(E) "Configuring"

sandbox:
	$(CABAL) sandbox init
	$(CABAL) sandbox add-source ../isa-parser

install-deps: sandbox
	$(E) "Installing dependencies"
	$(CABAL) install --only-dependencies

doc:
	$(E) "Docs"

clean:
	$(E) "Cleaning"
	$(Q) cabal sandbox delete -v0
	$(Q) rm -rf .cabal-sandbox/ dist/ ../isa-parser/dist
	$(Q) rm -rf out/
	$(Q) rm -rf tests/include
	$(Q) find . -name "*_flymake.hs" -delete

tests/include/%_dummy.h: tests/%.cogent
	$(Q) egrep "^type +([A-Z][a-zA-Z0-9_']*)( [a-z][a-zA-Z0-9_']*)* *$$" $^ | sed -e "s/type \([A-Z][a-zA-Z0-9_']*\).*$$/typedef void* \1;/" > $@

.gen-types: test-setup $(DUMMY_HEADER_FILES)
	$(E) "Generated C headers."

test-setup:
	$(Q)mkdir -p tests/include

tests: test-clean .test-cogent test-tc test-ds test-an test-mn test-cg \
	test-tc-proof test-aq test-aq test-shallow-proof test-ee test-gcc

test-clean:
	$(E) "Cleaning up artefacts from earlier test runs."
	$(Q) rm -rf out/
	$(Q) rm -rf tests/include/

.test-cogent:
ifeq ($(shell which cogent 2> /dev/null; echo $$? ),1)
	$(error Cogent not installed, or is not available in your PATH)
endif

test-tc: .gen-types
	$(E) "=== Type Checking Tests ==="

test-ds: .gen-types
	$(E) "=== Desugaring Tests ==="

test-an: .gen-types
	$(E) "=== A-normal transform Tests ==="

test-mn: .gen-types
	$(E) "=== Monomorphization Tests ==="

test-cg: .gen-types
	$(E) "=== Code Generation Tests ==="

test-tc-proof: .gen-types
	$(E) "=== Proof Feneration For Type Checking Tests ==="

test-aq: .gen-types
	$(E) "=== Anti-quotation Tests ==="

test-shallow-proof: .gen-types
	$(E) "=== Shallow-embedding Proofs Tests ==="

test-ee: .gen-types
	$(E) "=== End-to-end Proofs Tests ==="

test-gcc: .gen-types
	$(E) "=== Compile generated code using GCC ==="

setup-config: configure
	$(CABAL) configure $(CABALFLAGS)

pkg:
	$(CABAL) sdist
help:
	$(E) "** Cogent Compiler **"
	$(E) "Run 'make' to build the Cogent compiler."
	$(E) ""
	$(E) "* make clean"
	$(E) "  Cleanup"
	$(E) ""
	$(E) "* make tests"
	$(E) "  Run all tests."
	$(E) ""
	$(E) "* make pkg"
	$(E) "  Create a source distribution package."
	$(E) ""
	$(E) "* make help"
	$(E) "  Print this help."

