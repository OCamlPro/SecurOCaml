obytelib=~/github/obytelib/lib
occ=ocamlc -g -I $(obytelib)

normbytecode: normbytecode.ml
	$(occ) -o $@ $(obytelib)/obytelib.cma $^

listx.cmo: listx.ml
	$(occ) -c $<

types.cmo: types.ml listx.cmo
	$(occ) -c $<

var.cmo: var.ml var.cmi
	$(occ) -c $<

var.cmi: var.mli
	$(occ) -c $<

rules.cmo: rules.ml types.cmo
	$(occ) -c $<

rules.mli.auto: rules.ml
	$(occ) -i $<

test_unify.cmo: test_unify.ml
	$(occ) -c $<

test_unify: listx.cmo types.cmo test_unify.cmo
	$(occ) $^ -o test_unify

bytecheck.cmo: bytecheck.ml rules.cmo
	$(occ) -c $<

bytecheck: $(obytelib)/obytelib.cma listx.cmo types.cmo rules.cmo bytecheck.cmo
	$(occ) $^ -o bytecheck

.PHONY: clean
clean:
	rm *.cmo *.cmi
