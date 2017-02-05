OCAMLBUILD = ocamlbuild -package uuidm -package verdi-runtime \
                        -I ml -cflags -g,-w,a,-color,always

BANK = Bank.v ExtractBank.v
BANK_COQ = Bank_Coq.ml

default: bank.native

$(BANK_COQ): $(BANK)
	coqc $(BANK)

bank.d.byte: $(BANK_COQ)
	$(OCAMLBUILD) Bank.d.byte

bank.native: $(BANK_COQ)
	$(OCAMLBUILD) Bank.native

clean:
	$(OCAMLBUILD) -clean
	rm -rf *.vo *.glob *_Coq.ml*
