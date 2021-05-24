.PHONY: build install test-compiler

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

all: .cabal-update install
	$(E) "Cogent Compiler successfully built for $(OS)."
	$(E)
	$(E) "Add the installed 'cogent' executable to your path."
	$(E)
	$(E) "To enable bash auto-completion for 'cogent', please add the following to your .bashrc file:"
	$(E) "source $(PWD)/misc/cogent_autocomplete.sh"
	$(E)
	$(E)


stack-build:
	$(E) "Building Cogent using stack."
	$(Q) $(STACK) build

build:
	$(E) "Building..."
	$(Q) $(CABAL) new-build $(BUILD_FLAGS)

install:
	$(E) "Installing.."
	$(Q) $(CABAL) new-install $(INSTALL_FLAGS)

clean:
	$(Q) rm -rf out/
	$(Q) rm -rf tests/include
	$(Q) find . -name "*_flymake.hs" -delete

full-clean: clean
	$(Q) $(CABAL) new-clean
	$(Q) rm -rf dist-newstyle/ ../isa-parser/dist-newstyle


dev: .cabal-update build
	$(E) "Cogent Compiler successfully built for $(OS)."
	$(E)
	$(E) "Add 'cogent' compiler to your path by running (substitute the placeholders with your configuration):"
	$(E) '  export PATH=$(PWD)/dist-newstyle/build/<ARCH>/ghc-<GHC_VERSION>/cogent-<COGENT_VERSION>/build/cogent/cogent:$$PATH'
	$(E)
	$(E) "_Or_ make a symlink to the executable in ~/.cabal/bin by running:"
	$(E) '  ln -s $(PWD)/dist-newstyle/build/<ARCH>/ghc-<GHC_VERSION>/cogent-<COGENT_VERSION>/build/cogent/cogent $$HOME/.cabal/bin/cogent' 
	$(E)
	$(E) "To enable bash auto-completion for 'cogent', please add the following to your .bashrc file:"
	$(E) "source $(PWD)/misc/cogent_autocomplete.sh"
	$(E)
	$(E)

.cabal-update:
	$(Q) $(CABAL) new-update

local: .cabal-update
	$(E) "Installing cogent locally"
	$(Q) $(CABAL) new-install --overwrite-policy=always --installdir=$(PWD)/build/bin/

# There's a sed script that does a very similar thing in scripts/cogent_validate.sh, and for some reason they're both necessary.
tests/include/%_dummy.h: tests/%.cogent
	$(Q) egrep "^type +([A-Z][a-zA-Z0-9_']*)( [a-z][a-zA-Z0-9_']*)* *(--.*)?$$" $^ | sed -e "s/type \([A-Z][a-zA-Z0-9_']*\).*$$/struct \1 {int dummy; }; typedef struct \1 \1;/" > $@

.gen-types: .test-setup $(DUMMY_HEADER_FILES)
	$(E) "Generated C headers."

.test-setup:
	$(Q)mkdir -p tests/include

tests: test-compiler \
       test-tc-proof test-shallow-proof test-ee test-hs test-quickcheck

test-compiler: test-clean .test-cogent
	./tests/run-test-suite.py \
	# test-tc test-ds test-an test-mn test-cg test-gcc \
	# test-pp test-aq \
	# test-hs \
	# test-quickcheck

test-compiler-proofs: test-clean .test-cogent
	./tests/run-test-suite.py --repo "$(PWD)/../" \
		--extra-phases "$(PWD)/tests/phases/" \
		--repo "$(PWD)/../" \
		--ignore-phases "cogent"

test-quickcheck:
	$(Q) $(CABAL) test test-quickcheck

test-clean:
	$(E) "Cleaning up artefacts from earlier test runs."
	$(Q) rm -rf out/
	$(Q) rm -rf tests/include/

.test-cogent:
ifeq ($(shell which cogent 2> /dev/null; echo $$? ),1)
	$(error Cogent not installed, or is not available in your PATH)
endif

test-pp:
	$(E) "=== Parser & Pretty-Printer Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -pp

test-tc:
	$(E) "=== Type Checking Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -tc

test-ds:
	$(E) "=== Desugaring Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -ds

test-an:
	$(E) "=== A-normal transform Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -an

test-mn:
	$(E) "=== Monomorphization Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -mn

test-cg:
	$(E) "=== Code Generation Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -cg

test-tc-proof:
	$(E) "=== Proof Generation For Type Checking Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -tc-proof

test-ac: .gen-types
	$(E) "=== Isabelle (AutoCorres) test ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -ac

test-c-refine: .gen-types
	$(E) "=== C-refinement proof test ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -c-refine

test-flags:
	$(E) "=== FFI-generator Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -flags

test-aq:
	$(E) "=== Anti-quotation Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -aq

test-shallow-proof:
	$(E) "=== Shallow-embedding Proofs Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -shallow-proof

test-goanna:
	$(E) "=== Goanna test ==="
	$(error Goanna tests are not currently supported.)
	$(SCRIPTS_DIR)/cogent_validate.sh -goanna

test-ee: .gen-types
	$(E) "=== End-to-End Proofs Tests ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -ee

test-gcc: .gen-types
	$(E) "=== Compile generated code using GCC ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -gcc

test-hs:
	$(E) "=== Generate Haskell shallow embedding and compile using GHC ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -hs-shallow

test-hsc:
	$(E) "=== Generate C FFI in .hsc form and compile with hsc2hs ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -hsc-gen

test-libgum:
	$(E) "=== Typechecking libgum ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -libgum

examples: .test-cogent
	$(E) "=== Build Cogent examples ==="
	$(SCRIPTS_DIR)/cogent_validate.sh -examples

examples-clean:
	$(E) "=== Build Cogent examples ==="
	$(SCRIPTS_DIR)/build_examples.sh clean

help:
	$(E) "** Cogent Compiler **"
	$(E) "Run 'make' to build the Cogent compiler."
	$(E) ""
	$(E) "* make"
	$(E) "  Install Cogent via cabal (default to: ~/.cabal/bin)"
	$(E) ""
	$(E) "* make dev"
	$(E) "  Build Cogent via cabal to a local dist-newstyle directory"
	$(E) ""
	$(E) "* make local"
	$(E) "  Build Cogent and put the executable in build/bin/"
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
	$(E) "* make test-compiler"
	$(E) "  Run all compiler tests (excl. Isabelle proofs)."
	$(E) ""
	$(E) "* make test-compiler-proofs"
	$(E) "  Only run compiler Isabelle proof tests."
	$(E) ""
	$(E) "* make test-clean"
	$(E) "  Cleanup artefacts from earlier test runs."
	$(E) ""
	$(E) "* make test-tc"
	$(E) "  Run Typechecking Tests."
	$(E) ""
	$(E) "* make test-ds"
	$(E) "  Run Desugaring Tests."
	$(E) ""
	$(E) "* make test-an"
	$(E) "  Run A-Normalisation Tests."
	$(E) ""
	$(E) "* make test-mn"
	$(E) "  Run Monomorphisation Tests."
	$(E) ""
	$(E) "* make test-cg"
	$(E) "  Run Code Generation Tests."
	$(E) ""
	$(E) "* make test-tc-proof"
	$(E) "  Run Typechecking Proof Generation Tests."
	$(E) ""
	$(E) "* make test-ac"
	$(E) "  Run AutoCorres test."
	$(E) ""
	$(E) "* make test-c-refine"
	$(E) "  Run C-refinement proof test."
	$(E) ""
	$(E) "* make test-flags"
	$(E) "  Run Compiler Flags Tests."
	$(E) ""
	$(E) "* make test-aq"
	$(E) "  Run Anti-Quotation Tests."
	$(E) ""
	$(E) "* make test-shallow-proof"
	$(E) "  Run Shallow Embedding Proofs Tests."
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
	$(E) "* make test-hs"
	$(E) "  Generate Haskell shallow embedding and compile with GHC."
	$(E) ""
	$(E) "* make test-hsc"
	$(E) "  Generate C FFI in .hsc form and compile with hsc2hs."
	$(E) ""
	$(E) "* make test-libgum"
	$(E) "  Run libgum Typechecking Tests."
	$(E) ""
	$(E) "* make examples"
	$(E) "  Compile Cogent examples."
	$(E) ""
	$(E) "* make examples-clean"
	$(E) "  Clean up earlier build of examples."
	$(E) ""
	$(E) "* make help"
	$(E) "  Print this help."

