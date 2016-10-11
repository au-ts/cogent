CABAL := cabal
STACK := stack

# Cabal Flags
CABALFLAGS += --enable-tests --force-reinstalls


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
