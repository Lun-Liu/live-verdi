Require Import Bank.

Require Import Verdi.SeqNum.

Set Bullet Behavior "Strict Subproofs".

Section Bank_SN.
  Definition bank_sn_base_params    := base_params.
  Definition bank_sn_multi_params   := multi_params.
  Definition bank_sn_failure_params := bank_failure_params.
End Bank_SN.
