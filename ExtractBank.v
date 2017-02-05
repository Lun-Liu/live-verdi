Require Import Verdi.Verdi.

Require Import Bank.

Require Import
  ExtrOcamlBasic
  ExtrOcamlNatInt
  ExtrOcamlString.

Require Import
  Verdi.ExtrOcamlBasicExt
  Verdi.ExtrOcamlNatIntExt
  Verdi.ExtrOcamlBool
  Verdi.ExtrOcamlList.

Extraction "Bank_Coq.ml" seq bank_base_params bank_multi_params.
