Require Import
  Bank
  Bank_SN
  Bank_Proofs.

From Verdi Require Import
  Verdi
  SeqNum
  SeqNumCorrect.

From InfSeqExt Require Import
  infseq
  exteq.

Set Bullet Behavior "Strict Subproofs".

Section Bank_SN_Proofs.

  (* What about traces?? *)
  Theorem transformed_min_value_invariant :
    forall (net : bank_sn_network) tr,
      step_dup_star (params := bank_sn_multi_params) step_async_init net tr ->
      min_value_invariant_network (revertNetwork net).
  Proof using.
    intros.
    pose proof @true_in_reachable_transform _ bank_multi_params 
               (fun net : network => min_value_invariant_network net)
               true_in_reachable_min_value.
    unfold true_in_reachable in *.
    apply H0. unfold reachable. eauto.
  Qed.

End Bank_SN_Proofs.