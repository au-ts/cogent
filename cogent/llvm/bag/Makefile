CLANG=clang -I../include
AS=llvm-as
LINK=llvm-link
COGENT=stack exec cogent --

all: main.c bag.bc
	$(CLANG) main.c bag.bc -o main
	chmod +x main

run: all
	./main

bag.bc: bag.ll
	$(AS) bag.ll -o bag.bc

bag.ll: bag.cogent
	$(COGENT) --llvm bag.cogent

.PHONY: clean
clean:
	rm *.ll
	rm *.bc
	rm main
