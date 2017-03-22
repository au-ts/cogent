CABAL := cabal
STACK := stack

# Cabal Flags
INSTALL_FLAGS += --enable-tests --force-reinstalls
CONFIG_FLAGS +=


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
