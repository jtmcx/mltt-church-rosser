(** Destruct all hypotheses of the form [exists x, ...], while attempting
    to preserve the name of the existensial variable. *)

Ltac deex :=
  repeat match goal with
    | H: exists x, _ |- _ =>
        let x' := fresh x in
        destruct H as [x' H]
  end.

(** Destruct all disjunctive hypotheses. *)

Ltac deor :=
  repeat match goal with
  | H: _ \/ _ |- _ => destruct H
  end.

(** Destruct all conjunctive hypotheses. *)

Ltac deand :=
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  end.
