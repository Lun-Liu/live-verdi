Require Import Verdi.Verdi.

Require Import Verdi.SeqNum.
Require Import Bank.

Definition transformed_base_params :=
    @SeqNum.base_params Bank.bank_base_params Bank.bank_multi_params.
    
Definition transformed_multi_params :=
    @SeqNum.multi_params Bank.bank_base_params Bank.bank_multi_params.
    
Definition transformed_network :=
    @network transformed_base_params transformed_multi_params.