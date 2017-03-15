Require Import Verdi.Verdi.
Require Import Verdi.LabeledNet.

Set Implicit Arguments.

Section LabeledSeqNum.
  Context {orig_base_params : BaseParams}.
  Context {orig_lb_multi_params : LabeledMultiParams orig_base_params}.

  Record lb_seq_num_data := mkseq_num_data { tdNum  : nat;
                                             tdSeen : lb_name -> list nat;
                                             tdData : data }.

  Record lb_seq_num_msg := mkseq_num_msg { tmNum : nat;
                                           tmMsg : lb_msg }.

  Definition lb_seq_num_msg_eq_dec (x y : lb_seq_num_msg) : {x = y} + {x <> y}.
    decide equality.
    apply lb_msg_eq_dec.
    decide equality.
  Defined.

  Fixpoint lb_processPackets (seq_num : nat) (packets : list (name * msg)) : nat * list (name * lb_seq_num_msg) :=
    match packets with
      | [] => (seq_num, [])
      | p :: ps => let (n', pkts) := lb_processPackets seq_num ps in
                   (n' + 1, (fst p, mkseq_num_msg n' (snd p)) :: pkts)
    end.


  Definition lb_seq_num_init_handlers (n : name) :=
    mkseq_num_data 0 (fun _ => []) (init_handlers n).

  Definition lb_seq_num_net_handlers
             (dst : lb_name)
             (src : lb_name)
             (m : lb_seq_num_msg)
             (state : lb_seq_num_data) :
    label * (list output) * lb_seq_num_data * list (name * lb_seq_num_msg) :=
    if (member (tmNum m) (tdSeen state src)) then
      (label_silent, [], state, [])
    else
      let '(l,out, data', pkts) := (lb_net_handlers dst src (tmMsg m) (tdData state)) in
      let (n', tpkts) := lb_processPackets (tdNum state) pkts in
      (l, out, mkseq_num_data n' (update name_eq_dec (tdSeen state) src (tmNum m :: tdSeen state src)) data', tpkts).

  Definition lb_seq_num_input_handlers
             (h : name)
             (inp : input)
             (state : lb_seq_num_data) :
    label * (list output) * lb_seq_num_data * list (name * lb_seq_num_msg) :=
    let '(l, out, data', pkts) := (lb_input_handlers h inp (tdData state)) in
    let (n', tpkts) := lb_processPackets (tdNum state) pkts in
    (l, out, mkseq_num_data n' (tdSeen state) data', tpkts).

  Instance base_params : BaseParams :=
    {
      data := lb_seq_num_data ;
      input := input ;
      output := output
    }.

  Instance lb_multi_params : LabeledMultiParams _ :=
    {
      lb_name := lb_name ;
      lb_msg  := lb_seq_num_msg ;
      lb_msg_eq_dec := lb_seq_num_msg_eq_dec ;
      lb_name_eq_dec := lb_name_eq_dec ;
      lb_nodes := lb_nodes ;
      label := label ;
      label_silent := label_silent;
      lb_init_handlers := lb_seq_num_init_handlers ;
      lb_net_handlers := lb_seq_num_net_handlers ;
      lb_input_handlers := lb_seq_num_input_handlers ;
    }.
  Proof.
    - eauto using all_names_nodes.
    - eauto using no_dup_nodes.
  Defined.

  Instance multi_params : MultiParams base_params :=
    unlabeled_multi_params.
End LabeledSeqNum.

Hint Extern 5 (@BaseParams) => apply base_params : typeclass_instances.
Hint Extern 5 (@MultiParams _) => apply multi_params : typeclass_instances.
Hint Extern 5 (@LabeledMultiParams _) => apply lb_multi_params : typeclass_instances.