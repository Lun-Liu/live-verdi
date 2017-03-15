Require Import Bank.

From Verdi Require Import
  Verdi
  HandlerMonad
  LabeledNet.

From InfSeqExt Require Import
  infseq
  classical.

Local Arguments update {_} {_} _ _ _ _ _ : simpl never.

Set Bullet Behavior "Strict Subproofs".


Lemma In_split_not_In :
  forall A (p : A) p' xs ys zs,
    In p (xs ++ p' :: ys) ->
    ~ In p (zs ++ xs ++ ys) ->
    p = p'.
Proof using.
  intros. find_apply_lem_hyp in_app_iff. simpl in *.
  intuition ; find_false ; apply in_app_iff
            ; right ; apply in_app_iff ; auto.
Qed.

Lemma option_eq_dec : forall {T : Type} (T_eq_dec : forall t1 t2 : T, {t1 = t2} + {t1 <> t2}),
  forall l1 l2 : option T, {l1 = l2} + {l1 <> l2}.
Proof.
  repeat decide equality.
Qed.


Definition label_eq_dec :
  forall x y : label,
    {x = y} + {x <> y}.
Proof using.
  decide equality; apply fin_eq_dec.
Qed.


Ltac basic_unfold :=
  repeat ( unfold step_async_init,
                  unlabeled_input_handlers, unlabeled_net_handlers,
                  lb_net_handlers, lb_input_handlers,
                  net_handlers, input_handlers in *
         ; repeat break_let).

Ltac handler_unfold :=
  repeat (monad_unfold; unfold NetHandler, ServerNetHandler, AgentNetHandler,
                               IOHandler, AgentIOHandler, ServerIOHandler in *).

Ltac simplify_bank_handlers :=
  repeat ( basic_unfold ; handler_unfold ; unfold InitState in *
         ; repeat break_match ; simpl in *)
  ; try solve_by_inversion
  ; repeat ( repeat (find_inversion ; intuition)
           ; subst_max ; simpl in * ; intuition )
  ; repeat clean.


Definition initialized_network (net:network) :=
  exists tr, step_async_star step_async_init net tr.

Definition initialized_eventseq (s:infseq (event network label (name * (input + list output)))) :=
  event_step_star step_async step_async_init (hd s) /\
  lb_step_execution lb_step_async s.

Lemma initialized_event_network :
  forall (e:event network label (name * (input + list output))),
    event_step_star step_async step_async_init e ->
    initialized_network (evt_a e).
Proof using.
  intuition. find_apply_lem_hyp refl_trans_1n_n1_trace.
  destruct e. simpl in *.
  prep_induction H. induction H ; intuition ; subst_max.
  - exists []. constructor.
  - unfold initialized_network in *. break_exists.
    exists (x ++ cs'). apply RT1n_step with (y := x') ; intuition.
Qed.

Lemma initialized_eventseq_network :
  forall s,
    initialized_eventseq s ->
    always (now (fun e => initialized_network (evt_a e))) s.
Proof using.
  unfold initialized_eventseq. intuition.
  pose proof (step_async_star_lb_step_execution H0 H1).
  generalize dependent H. clear H0 H1. generalize dependent s.
  cofix c. destruct s. constructor.
  - apply always_now in H. simpl in *. apply initialized_event_network ; intuition.
  - apply c. simpl. apply always_tl in H. simpl in H. apply H.
Qed.


Lemma IOHandler_labels :
  forall n ni s s' l os ms,
    IOHandler n ni s = (l, os, s', ms) ->
    (exists id:ClientId,
      (l = Ready /\ ms = [] /\
                   (s' = s /\ os = [] \/
                    s' = agent fail /\ os = [(netO id Failed)] \/
                    s' = agent wait /\ os = [(netO id Ignore)])) \/
      (exists r : ReqMsg,
        l = Waiting /\ os = [] /\ s' = agent wait /\
                       ms = [(Server, (netM id (req r)))])) \/
    (l = Nop /\ os = [] /\ ms = [] /\ s = s').
Proof using.
  intros. simplify_bank_handlers ; left ; exists c ; intuition
                                 ; right ; eexists ; intuition.
Qed.

Lemma NetHandler_labels :
  forall dst src nm s s' l os ms,
    NetHandler dst src nm s = (l, os, s', ms) ->
    (exists id : ClientId,
      (l = Ready /\ ms = [] /\
                   ((s = s' /\ os = []) \/
                    (s' = agent fail /\ os = [(netO id Failed)]) \/
                    (exists a v,
                      s' = agent pass /\ os = [(netO id (Passed a v))]))) \/
      (exists r : RespMsg,
        l = Processed /\ os = [] /\ ms = [(Agent, netM id (resp r))])) \/
    (l = Nop /\ os = [] /\ ms = [] /\ s = s').
Proof using.
  intros. simplify_bank_handlers ; left ; exists c ;  intuition
                                 ; first ( left ; intuition ; right ; right
                                                ; repeat eexists )
                                 ; right ; repeat eexists.
Qed.

Lemma step_star_consistent_state :
  forall net,
    initialized_network net ->
    (exists astate, nwState net Agent = agent astate) /\
    (exists sstate, nwState net Server = server sstate) /\
    (forall sstate, nwState net Agent <> server sstate) /\
    (forall astate, nwState net Server <> agent astate).
Proof using.
  intros net Hstar. unfold initialized_network in *. break_exists_name tr.
  find_apply_lem_hyp refl_trans_1n_n1_trace.
  prep_induction Hstar. induction Hstar.
  - intuition ; break_exists ; subst_max ; simplify_bank_handlers ; eauto.
  - intuition ; subst_max ; invcs H0 ; simplify_bank_handlers
                ; unfold update ; simpl ; eauto
                ; repeat break_exists ; unfold update in * ; simpl in * ; discriminate.
Qed.


Definition message_enables_label p l :=
  forall net,
    initialized_network net ->
    In p (nwPackets net) ->
    lb_step_ex lb_step_async l net.

Definition message_delivered_label p l :=
  forall l' net net' tr,
    initialized_network net ->
    lb_step_async net l' net' tr ->
    In p (nwPackets net) ->
    ~ In p (nwPackets net') ->
    l = l'.

Lemma messages_trigger_labels :
  forall l p,
    message_enables_label p l ->
    message_delivered_label p l ->
    forall s,
      initialized_eventseq s ->
      In p (nwPackets (evt_a (hd s))) ->
      weak_until (now (enabled lb_step_async l))
                 (now (occurred l))
                 s.
Proof using.
    intros l p Henables Hdelivered. cofix c. intros.
    assert (H' := H). apply initialized_eventseq_network in H.
    destruct s,e. simpl in *. destruct (label_eq_dec l evt_l) ; subst_max.
    - apply W0. easy.
    - apply W_tl ; simpl.
      + apply always_now in H. simpl in H. 
        unfold message_enables_label, initialized_network in *.
        unfold enabled. simpl. break_exists. now eauto.
      + apply c ; unfold initialized_eventseq in * ; break_and ; invcs H2 ; intuition.
        * unfold event_step_star in *. unfold bank_multi_params.
          rewrite H6. apply (step_async_star_lb_step_reachable H1 H5).
        * destruct (In_dec packet_eq_dec
                           p (nwPackets (LabeledNet.evt_a e'))) ; intuition.
          unfold message_delivered_label, message_enables_label in *.
          apply always_now in H. simpl in H. intuition.
          pose proof (Hdelivered evt_l evt_a (LabeledNet.evt_a e') tr). intuition.
Admitted. (* WHY??!! ... *)

Lemma message_labels_eventually_occur :
  forall l p,
    l <> label_silent ->
    message_enables_label p l ->
    message_delivered_label p l ->
    forall s,
      initialized_eventseq s ->
      weak_fairness lb_step_async label_silent s ->
      lb_step_execution lb_step_async s ->
      In p (nwPackets (evt_a (hd s))) ->
      eventually (now (occurred l)) s.
Proof using.
    intros.
    find_eapply_lem_hyp messages_trigger_labels ; eauto.
    find_apply_lem_hyp weak_until_until_or_always.
    intuition.
    - now eauto using until_eventually.
    - find_apply_lem_hyp always_continuously.
      eapply_prop_hyp weak_fairness continuously; auto.
      destruct s. now find_apply_lem_hyp always_now.
Qed.