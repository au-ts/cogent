SRC=*.cogent

COGENT_FLAGS= -Od --fno-static-inline --fno-fncall-as-macro --ffunc-purity-attr --all -g --type-proof --c-refinement --root-dir=../../.. --fgen-header 
# lol makefile
gen-c-proof:
	for x in $(SRC); do cogent $$x $(COGENT_FLAGS) ; done

