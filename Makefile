OCAMLBUILD = ocamlbuild -package verdi-runtime -I ml -cflag -g

BANK = Bank.v ExtractionBank.v

default: bank.native

bank: $(BANK)
	coqc $(BANK)

bank.native: bank
	$(OCAMLBUILD) Bank.native

clean:
	rm -rf *.vo *.glob _build *.native *_Coq.ml*
