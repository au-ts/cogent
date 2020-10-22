CLANG=clang -I../include
AS=llvm-as
LINK=llvm-link
COGENT=stack exec cogent --

all: main.c hello_world.bc
	$(CLANG) main.c hello_world.bc -o main
	chmod +x main

run: all
	./main

hello_world.bc: hello_world.ll
	$(AS) hello_world.ll -o hello_world.bc

hello_world.ll: hello_world.cogent
	$(COGENT) --llvm hello_world.cogent

.PHONY: clean
clean:
	rm *.ll
	rm *.bc
	rm main
