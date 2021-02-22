CLANG=clang-11
AS=llvm-as-11
LINK=llvm-link-11
COGENT=cogent

all: main.bc adder.bc
	$(LINK) main.bc adder.bc -o main
	chmod +x main

main.bc: main.ll
	$(AS) main.ll -o main.bc

main.ll: main.c
	$(CLANG) -S -emit-llvm main.c -o main.ll

adder.bc: adder.ll
	$(AS) adder.ll -o adder.bc

adder.ll: adder.cogent
	$(COGENT) --llvm adder.cogent

.PHONY: clean
clean:
	rm *.ll
	rm *.bc
	rm main
