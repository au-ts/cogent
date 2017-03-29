CABAL := cabal
STACK := stack

# Cabal Flags
CONFIG_FLAGS += --enable-tests
BUILD_FLAGS +=
INSTALL_FLAGS += --enable-tests --force-reinstalls


MACHINE := $(shell $(CC) -dumpmachine)
ifneq (, $(findstring darwin, $(MACHINE)))
	OS:=darwin
else ifneq (, $(findstring cygwin, $(MACHINE)))
        OS:=windows
else ifneq (, $(findstring mingw, $(MACHINE)))
        OS:=windows
else ifneq (, $(findstring windows, $(MACHINE)))
        OS:=windows
else
        OS:=unix
endif
