
COQC=coqc
COQDOC=coqdoc

all: main doc

main:
	$(COQC) filters.v
	$(COQC) classcomp.v

doc:
	$(COQDOC) -d doc -g --utf8 --toc --no-index *.v

clean:
	rm -f *.vo* *.glob doc/classcomp.html doc/filters.html doc/toc.html doc/coqdoc.css

force_look:
	true
