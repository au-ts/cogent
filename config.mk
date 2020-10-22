CABAL := cabal
STACK := stack

# Cabal Flags
BUILD_FLAGS +=
INSTALL_FLAGS += --installdir=$(HOME)/.cabal/bin/ --overwrite-policy=always


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
