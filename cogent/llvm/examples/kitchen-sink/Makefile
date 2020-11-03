CLANG=clang -I../include -O3
AS=llvm-as
LINK=llvm-link
COGENT=stack exec cogent --

all: main.c kitchen_sink.bc
	$(CLANG) main.c kitchen_sink.bc -o main
	chmod +x main

run: all
	./main

kitchen_sink.bc: kitchen_sink.ll
	$(AS) kitchen_sink.ll -o kitchen_sink.bc

kitchen_sink.ll: kitchen_sink.cogent
	$(COGENT) --llvm kitchen_sink.cogent

kitchen_sink.c: kitchen_sink.cogent
	$(COGENT) --code-gen kitchen_sink.cogent

.PHONY: clean
clean:
	rm *.ll
	rm *.bc
	rm main
