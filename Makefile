OCAML = ocamlbuild -package uuidm -package verdi-runtime -I ml

OCAML_BUILD = $(OCAML) -cflags -w,a
OCAML_DBG_BUILD = $(OCAML) -cflags -g

BANK_EXTRACT = Bank.v Bank_Extract.v
BANK_PROVE = Bank.v Bank_Proofs.v

BANK_OCAML = Bank_Coq.ml
BANK_PROOF = Bank_Proofs.vo

default: bank.native

debug: bank.d.byte

$(BANK_PROOF): $(BANK_PROVE)
	coqc $(BANK_PROVE)

$(BANK_OCAML): $(BANK_EXTRACT)
	coqc $(BANK_EXTRACT)

bank.d.byte: $(BANK_PROOF) $(BANK_OCAML)
	$(OCAML_DBG_BUILD) Bank.d.byte

bank.native: $(BANK_OCAML)
	$(OCAML_BUILD) Bank.native

clean:
	$(OCAML_BUILD) -clean
	rm -rf *.vo *.glob *_Coq.ml*
