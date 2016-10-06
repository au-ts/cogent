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

install:
	$(E) "Installing.."
	$(CABAL) install $(CABALFLAGS)

pinstall: CABALFLAGS += --enable-executable-profiling
pinstall: setup-config
	$(CABAL) install $(CABALFLAGS)

build: setup-config
	$(E) "Building..."
	$(CABAL) build

setup-config: configure
	$(CABAL) configure $(CABALFLAGS)
