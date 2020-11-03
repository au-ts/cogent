CLANG=clang -I../include
AS=llvm-as
LINK=llvm-link
COGENT=stack exec cogent --

all: main.c adder.bc
	$(CLANG) main.c adder.bc -o main
	chmod +x main

run: all
	./main

adder.bc: adder.ll
	$(AS) adder.ll -o adder.bc

adder.ll: adder.cogent
	$(COGENT) --llvm adder.cogent

.PHONY: clean
clean:
	rm *.ll
	rm *.bc
	rm main
