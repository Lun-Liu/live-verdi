Require Bank_SN.

From Coq Require Import
  ExtrOcamlBasic
  ExtrOcamlNatInt
  ExtrOcamlString.

From Verdi Require Import
  Verdi
  ExtrOcamlBasicExt
  ExtrOcamlNatIntExt
  ExtrOcamlBool
  ExtrOcamlList
  ExtrOcamlFin.

Definition final_base_params := Bank_SN.bank_sn_base_params.
Definition final_multi_params := Bank_SN.bank_sn_multi_params.
Definition final_failure_params := Bank_SN.bank_sn_failure_params.

Extraction Language Ocaml.
Extraction "Bank_Coq.ml" seq final_base_params final_multi_params final_failure_params.
