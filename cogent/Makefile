.PHONY: build configure doc install gen-types

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

PWD:=$(shell pwd)
SCRIPTS_DIR:=$(PWD)/scripts/
include $(PWD)/../config.mk

# These file lists are for generating dummy headers for c compilation
PASS_TEST_COGENT_FILES := $(wildcard tests/pass_*.cogent)
FAIL_TEST_COGENT_FILES := $(wildcard tests/fail_*.cogent)
DUMMY_HEADER_FILES := $(addprefix tests/include/,$(notdir $(PASS_TEST_COGENT_FILES:.cogent=_dummy.h)))

all: install-dev

.install:
	$(E) "Installing.."
	$(CABAL) install $(INSTALL_FLAGS)

isa-parser:
	$(Q) make -C ../isa-parser

stack-build:
	$(E) "Building Cogent using stack."
	$(STACK) build

build:
	$(E) "Building..."
	$(CABAL) build

configure:
	$(E) "Configuring"
	$(CABAL) configure

sandbox:
ifneq ($(wildcard .cabal-sandbox/),)
	$(E) "Using Existing sandbox..."
else
	$(E) "Building in a sandbox..."
	$(CABAL) sandbox init
	$(CABAL) sandbox add-source ../isa-parser
endif

.install-deps:
	$(E) "Installing dependencies"
	$(CABAL) install --only-dependencies

doc:
	$(E) "Building Cogent docs..."
	$(Q) make -C doc

clean:
	$(Q) $(CABAL) clean
	$(Q) make -C doc clean
	$(Q) find . -name "*_flymake.hs" -delete

full-clean: clean
	$(Q) $(CABAL) sandbox delete -v0
	$(Q) rm -rf .cabal-sandbox/ dist/ ../isa-parser/dist
	$(Q) rm -rf out/
	$(Q) rm -rf tests/include
	$(Q) find . -name "*_flymake.hs" -delete


install-dev: sandbox cabal-update .install-deps configure build
	$(CABAL) install $(INSTALL_FLAGS)
	$(E) "Cogent Compiler successfully built for $(OS)."
	$(E)
	$(E) "Add 'cogent' compiler to your path by running:"
	$(E) '  export PATH=$$PATH:$(PWD)/.cabal-sandbox/bin/'
	$(E)
	$(E) "To enable bash auto-completion for 'cogent', please add the following to your .bashrc file:"
	$(E) "source $(PWD)/misc/cogent_autocomplete.sh"
	$(E)
	$(E)

cabal-update:
	$(CABAL) update

tests/include/%_dummy.h: tests/%.cogent
	$(Q) egrep "^type +([A-Z][a-zA-Z0-9_']*)( [a-z][a-zA-Z0-9_']*)* *(--.*)?$$" $^ | sed -e "s/type \([A-Z][a-zA-Z0-9_']*\).*$$/typedef void* \1;/" > $@

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
	$(SCRIPTS_DIR)/cogent_validate.sh -tc

test-ds: .gen-types
	$(E) "=== Desugaring Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -ds

test-an: .gen-types
	$(E) "=== A-normal transform Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -an

test-mn: .gen-types
	$(E) "=== Monomorphization Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -mn

test-cg: .gen-types
	$(E) "=== Code Generation Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -cg

test-tc-proof: .gen-types
	$(E) "=== Proof Generation For Type Checking Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -tc-proof

test-ac: .gen-types test-gcc
	$(E) "=== Isabelle (AutoCorres) test ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -ac

test-aq: .gen-types
	$(E) "=== Anti-quotation Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -aq

test-shallow-proof: .gen-types
	$(E) "=== Shallow-embedding Proofs Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -shallow-proof

test-goanna:
	$(E) "=== Goanna test ==="
	$(error Goanna tests are not currently supported.)
	$(SCRIPTS_DIR)/cogent_validate.sh -goanna

test-ee: .gen-types
	$(E) "=== End-to-End Proofs Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -ee

test-gcc: .gen-types test-cg
	$(E) "=== Compile generated code using GCC ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -gcc

examples: .test-cogent
	$(E) "=== Build Cogent examples ==="
	$(SCRIPTS_DIR)/build_examples.sh

examples-clean:
	$(E) "=== Build Cogent examples ==="
	$(SCRIPTS_DIR)/build_examples.sh clean

pkg:
	$(CABAL) sdist
help:
	$(E) "** Cogent Compiler **"
	$(E) "Run 'make' to build the Cogent compiler."
	$(E) ""
	$(E) "* make"
	$(E) "  Build and install Cogent in a cabal-sandbox"
	$(E) ""
	$(E) "* make clean"
	$(E) "  Cleanup"
	$(E) ""
	$(E) "* make full-clean"
	$(E) "  Cleanup (removes sandbox)."
	$(E) ""
	$(E) "* make tests"
	$(E) "  Run all tests."
	$(E) ""
	$(E) "* make pkg"
	$(E) "  Create a source distribution package."
	$(E) ""
	$(E) "* make tests"
	$(E) "  Run all tests."
	$(E) ""
	$(E) "* make test-clean"
	$(E) "  Cleanup artefacts from earlier test runs."
	$(E) ""
	$(E) "* make test-tc"
	$(E) "  Run Type-Checking Tests."
	$(E) ""
	$(E) "* make test-ds"
	$(E) "  Run De-sugaring Tests."
	$(E) ""
	$(E) "* make test-an"
	$(E) "  Run A-Normal Transform Tests."
	$(E) ""
	$(E) "* make test-mn"
	$(E) "  Run Monomorphization Tests."
	$(E) ""
	$(E) "* make test-cg"
	$(E) "  Run Code Generation Tests."
	$(E) ""
	$(E) "* make test-tc-proof"
	$(E) "  Run Proof Generation For Type-Checking Tests."
	$(E) ""
	$(E) "* make test-ac"
	$(E) "  Run Isabelle (AutoCorres) test."
	$(E) ""
	$(E) "* make test-aq"
	$(E) "  Run Anti-Quotation Tests."
	$(E) ""
	$(E) "* make test-shallow-proof"
	$(E) "  Run Anti-Shallow-embedding Proofs Tests."
	$(E) ""
	$(E) "* make test-goanna"
	$(E) "  Run Goanna Test [Currently Not Supported]."
	$(E) ""
	$(E) "* make test-ee"
	$(E) "  Run End-to-End Proofs Tests."
	$(E) ""
	$(E) "* make test-gcc"
	$(E) "  Compile generated code using GCC."
	$(E) ""
	$(E) "* make examples"
	$(E) "  Compile Cogent examples."
	$(E) ""
	$(E) "* make examples-clean"
	$(E) "  Clean up earlier build of examples."
	$(E) ""
	$(E) "* make doc"
	$(E) "  Build Cogent docs."
	$(E) ""
	$(E) "* make help"
	$(E) "  Print this help."

