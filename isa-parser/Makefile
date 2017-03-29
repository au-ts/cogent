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
	$(CABAL) install $(INSTALL_FLAGS)

pinstall: CONFIG_FLAGS += --enable-executable-profiling
pinstall: setup-config
	$(CABAL) install $(CONFIG_FLAGS)

deps:
	$(CABAL) install --only-dependencies

build: setup-config
	$(E) "Building..."
	$(CABAL) build

setup-config:
	$(CABAL) configure $(CONFIG_FLAGS)
