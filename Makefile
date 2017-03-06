OCAML = ocamlbuild -package uuidm -package verdi-runtime -I ml

OCAML_BUILD     = $(OCAML) -cflags -w,a
OCAML_DBG_BUILD = $(OCAML) -cflags -g

COQ       = coqc
COQ_QUICK = $(COQ) -quick


BANK_EXTRACT    = Bank.v Bank_Extract.v
BANK_PROVE      = Bank.v Bank_Utils.v Bank_Proofs.v
BANK_SN_EXTRACT = Bank.v Bank_SN.v Bank_SN_Extract.v
BANK_SN_PROVE   = $(BANK_PROVE) Bank_SN.v Bank_SN_Proofs.v

BANK          = $(BANK_EXTRACT:.v=.vo)
BANK_PROOF    = $(BANK_PROVE:.v=.vo)
BANK_SN       = $(BANK_SN_EXTRACT:.v=.vo)
BANK_SN_PROOF = $(BANK_SN_PROVE:.v=.vo)



.PHONY: clean

default: bank.bin

quick: $(BANK_SN_PROVE:.v=.vio)


%.vio: %.v
	$(COQ_QUICK) $<

%.vo: %.v
	$(COQ) $<


bank.bin: $(BANK)
	$(OCAML_BUILD) Bank.native
	mv Bank.native bank.bin

bank-dbg.bin: $(BANK_PROOF)
	$(OCAML_DBG_BUILD) Bank.d.byte
	mv Bank.d.byte bank-dbg.bin

bank-sn.bin: $(BANK_SN)
	$(OCAML_BUILD) Bank.native
	mv Bank.native bank-sn.bin

bank-sn-dbg.bin: $(BANK_SN_PROOF)
	$(OCAML_DBG_BUILD) Bank.d.byte
	mv Bank.d.byte bank-sn-dbg.bin



clean:
	$(OCAML_BUILD) -clean
	rm -rf *.vio *.vo *.glob *_Coq.ml*
