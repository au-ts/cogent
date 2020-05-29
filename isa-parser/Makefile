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

PWD:=$(shell pwd)
include $(PWD)/../config.mk

install: deps
	$(E) "Installing.."
	$(CABAL) v1-install $(INSTALL_FLAGS)

pinstall: CONFIG_FLAGS += --enable-executable-profiling
pinstall: setup-config
	$(CABAL) v1-install $(CONFIG_FLAGS)

deps:
	$(CABAL) v1-install --only-dependencies

build: setup-config
	$(E) "Building..."
	$(CABAL) v1-build

setup-config:
	$(CABAL) v1-configure $(CONFIG_FLAGS)
