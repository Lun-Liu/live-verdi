Require Import Bank.

Require Import Verdi.Verdi.

Set Bullet Behavior "Strict Subproofs".

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Section Bank_Proof.
  Context {bank_base_params  : BaseParams}.
  Context {bank_multi_params : MultiParams bank_base_params}.

End Bank_Proof.