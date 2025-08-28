
COQC=coqc
COQDOC=coqdoc

all: main doc

main:
	$(COQC) CRing_theory.v
	$(COQC) ListSet.v
	$(COQC) filters.v

clean:
	rm *.vo* *.glob .*aux

force_look:
	true
