OCAML = ocamlbuild -package uuidm -package verdi-runtime -I ml

OCAML_BUILD     = $(OCAML) -cflags -w,a
OCAML_DBG_BUILD = $(OCAML) -cflags -g



BANK_EXTRACT    = Bank.v Bank_Extract.v
BANK_PROVE      = Bank.v Bank_Proofs.v
BANK_SN_EXTRACT = Bank.v Bank_SN.v Bank_SN_Extract.v
BANK_SN_PROVE   = Bank.v Bank_SN.v Bank_SN_Proofs.v

BANK          = Bank_Extract.vo
BANK_PROOF    = Bank_Proofs.vo
BANK_SN       = Bank_SN_Extract.vo
BANK_SN_PROOF = Bank_SN_Proofs.vo



default: bank


$(BANK): $(BANK_EXTRACT)
	coqc $(BANK_EXTRACT)

$(BANK_PROOF): $(BANK_PROVE)
	coqc $(BANK_PROVE)

$(BANK_SN): $(BANK_SN_EXTRACT)
	coqc $(BANK_SN_EXTRACT)

$(BANK_SN_PROOF): $(BANK_SN_PROVE)
	coqc $(BANK_SN_PROVE)


bank: $(BANK)
	$(OCAML_BUILD) Bank.native
	mv Bank.native bank

bank-dbg: $(BANK_PROOF) $(BANK)
	$(OCAML_DBG_BUILD) Bank.d.byte
	mv Bank.d.byte bank-dbg

bank-sn: $(BANK_SN)
	$(OCAML_BUILD) Bank.native
	mv Bank.native bank-sn

bank-sn-dbg: $(BANK_SN_PROOF) $(BANK_SN)
	$(OCAML_DBG_BUILD) Bank.d.byte
	mv Bank.d.byte bank-sn-dbg



clean:
	$(OCAML_BUILD) -clean
	rm -rf *.vo *.glob *_Coq.ml*
