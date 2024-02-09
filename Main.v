From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lists.List.

(* XXX *)
Set Debug Eauto.
Set Debug Auto.

(** ======================================================================== *)
(** ** Tactics *)

(** Destruct all hypotheses of the form [exists x, ...], while attempting
    to preserve the name of the existensial variable. *)

Ltac deex :=
  repeat match goal with
  | H: exists x, _ |- _ => let x' := fresh x in
                           destruct H as [x' H]
  end.

(** Destruct all disjunctive hypotheses. *)

Ltac deor :=
  repeat match goal with
  | H: _ \/ _ |- _ => destruct H
  end.

Ltac deand :=
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  end.

Create HintDb mltt.
#[global] Hint Constants Opaque : mltt.
#[global] Hint Variables Opaque : mltt.

Inductive ty :=
  | ty_func (a b : ty)
  | ty_unit.

Definition context := list ty.

Inductive term : context -> ty -> Type :=
  | tm_var : forall G a x,
      nth_error G x = Some a -> term G a
  | tm_app : forall G a b,
      term G (ty_func a b) -> term G a -> term G b
  | tm_abs : forall G a b,
      term (a :: G) b -> term G (ty_func a b).

#[export] Hint Constructors term : mltt.

Definition thin (k x : nat) :=
  if x <? k then x else S x.

Definition thick (k x : nat) :=
  if x <? k then x else pred x.

Fixpoint lift_at (k : nat) (t : term) :=
  match t with
  | tm_type => tm_type
  | tm_var x => tm_var (thin k x)
  | tm_app t u => tm_app (lift_at k t) (lift_at k u)
  | tm_prod a b => tm_prod (lift_at k a) (lift_at (S k) b)
  | tm_abs a t => tm_abs (lift_at k a) (lift_at (S k) t)
  end.

Definition lift := lift_at 0.

Fixpoint subst (k : nat) (s t : term) :=
  match t with
  | tm_type => tm_type
  | tm_var x => if x =? k then s else tm_var (thick k x)
  | tm_app t u => tm_app (subst k s t) (subst k s u)
  | tm_prod a b => tm_prod (subst k s a) (subst (S k) (lift s) b)
  | tm_abs a t => tm_abs (subst k s a) (subst (S k) (lift s) t)
  end.

(** ------------------------------------------------------------------------ *)
(** ** Free Variables *)

Inductive free : nat -> term -> Prop :=
  | in_var : forall x,
      free x (tm_var x)
  | in_app : forall x t u,
      free x t \/ free x u -> free x (tm_app t u)
  | in_prod : forall x a b,
      free x a \/ free (S x) b -> free x (tm_prod a b)
  | in_abs : forall x a t,
      free x a \/ free (S x) t -> free x (tm_abs a t).

#[export] Hint Constructors free : mltt.

Definition closed (t : term) :=
  forall x, ~ free x t.

(** Proof that a term [t] is *scoped* to a context [g]. That is, for
    every free variable [x] that occurs in [t], [x] does not exceed the
    bounds of the context [g]. *)

Definition scoped (g : list term) (t : term) :=
  forall x, free x t -> x < length g.

(** A term that is scoped to the empty context is closed. *)

Definition scoped_empty_closed : forall t,
  scoped nil t <-> closed t.
Proof.
  unfold scoped, closed, not. split; intros.
  - apply Nat.nlt_0_r with x. auto.
  - exfalso. eauto.
Qed.


(** ------------------------------------------------------------------------ *)
(** ** Small Step *)

Reserved Notation "t '⊳' u" (at level 60).
Reserved Notation "t '⊳*' u" (at level 60).

(** The definition of [step t u] guarantees that exactly one redex was
    reduced in [t], yielding [u]. The definition of [step] is not reflexive.
    It is not irreflexive either, because of the omega combinator. A well-typed
    step is irreflexive, however. 
    *)
    

Inductive step : term -> term -> Prop :=
  | step_appl : forall t t',
      t ⊳ t' -> forall u, tm_app t u ⊳ tm_app t' u
  | step_appr : forall u u',
      u ⊳ u' -> forall t, tm_app t u ⊳ tm_app t u'
  | step_absl : forall a a',
      a ⊳ a' -> forall t, tm_abs a t ⊳ tm_abs a' t
  | step_absr : forall t t',
      t ⊳ t' -> forall a, tm_abs a t ⊳ tm_abs a t'
  | step_prodl : forall a a',
      a ⊳ a' -> forall b, tm_prod a b ⊳ tm_prod a' b
  | step_prodr : forall b b',
      b ⊳ b' -> forall a, tm_prod a b ⊳ tm_prod a b'
  | step_beta : forall a t u,
      tm_app (tm_abs a t) u ⊳ subst 0 u t
  where "t '⊳' u" := (step t u).

Inductive mstep : term -> term -> Prop :=
  | mstep_refl : forall t,
      t ⊳* t
  | mstep_step : forall t u v,
      t ⊳ u -> u ⊳* v -> t ⊳* v
  where "t '⊳*' u" := (mstep t u).

#[export] Hint Constructors step : mltt.
#[export] Hint Constructors mstep : mltt.

Lemma step_mstep : forall t u,
  t ⊳ u -> t ⊳* u.
Proof.
  eauto with mltt.
Qed.

Lemma mstep_trans : forall t u v,
  t ⊳* u -> u ⊳* v -> t ⊳* v.
Proof.
  induction 1; eauto with mltt.
Qed.

Lemma mstep_app : forall t t' u u',
  t ⊳* t' -> u ⊳* u' -> tm_app t u ⊳* tm_app t' u'.
Proof.
  intros t t' u u' Ht Hu.
  apply mstep_trans with (u := tm_app t' u).
  - induction Ht; eauto with mltt.
  - induction Hu; eauto with mltt.
Qed.

Lemma mstep_abs : forall a a' t t',
  a ⊳* a' -> t ⊳* t' -> tm_abs a t ⊳* tm_abs a' t'.
Proof.
  intros a a' t t' Ha Ht.
  apply mstep_trans with (u := tm_abs a' t).
  - induction Ha; eauto with mltt.
  - induction Ht; eauto with mltt.
Qed.

Lemma mstep_prod : forall a a' b b',
  a ⊳* a' -> b ⊳* b' -> tm_prod a b ⊳* tm_prod a' b'.
Proof.
  intros a a' b b' Ha Hb.
  apply mstep_trans with (u := tm_prod a' b).
  - induction Ha; eauto with mltt.
  - induction Hb; eauto with mltt.
Qed.

#[export] Hint Resolve step_mstep : mltt.
#[export] Hint Resolve mstep_app : mltt.
#[export] Hint Resolve mstep_abs : mltt.
#[export] Hint Resolve mstep_prod : mltt.

(** ------------------------------------------------------------------------ *)
(** ** Normalization *)

Inductive
  neutral : term -> Prop :=
  | ne_type :
      neutral tm_type
  | ne_var : forall x,
      neutral (tm_var x)
  | ne_app : forall t u,
      neutral t -> normal u -> neutral (tm_app t u)
  | ne_prod : forall a b,
      normal a -> normal b -> neutral (tm_prod a b)
with
  normal : term -> Prop :=
  | nf_abs : forall a t,
      normal a -> normal t -> normal (tm_abs a t)
  | nf_neu : forall t,
      neutral t -> normal t.

#[export] Hint Constructors neutral : mltt.
#[export] Hint Constructors normal : mltt.

Scheme nf_ne_ind := Induction for normal Sort Prop
  with ne_nf_ind := Induction for neutral Sort Prop.


Lemma normal_not_reducible : forall t,
  normal t -> forall u, t ⊳ u -> False.
Proof.
  apply (nf_ne_ind (fun t _ => forall u, ~ t ⊳ u)
                   (fun t _ => forall u, ~ t ⊳ u));
    autounfold; try easy;
  inversion 5; subst; now eauto.
Qed.

(** ------------------------------------------------------------------------ *)
(** ** Confluence (Church-Rosser) *)

Reserved Notation "t '⊳⊳' u"  (at level 60).

Inductive parstep : term -> term -> Prop :=
  | parstep_type :
      tm_type ⊳⊳ tm_type
  | parstep_var : forall x,
      tm_var x ⊳⊳ tm_var x
  | parstep_app : forall t t' u u',
      t ⊳⊳ t' -> u ⊳⊳ u' -> tm_app t u ⊳⊳ tm_app t' u'
  | parstep_abs : forall a a' t t',
      a ⊳⊳ a' -> t ⊳⊳ t' -> tm_abs a t ⊳⊳ tm_abs a' t'
  | parstep_prod : forall a a' b b',
      a ⊳⊳ a' -> b ⊳⊳ b' -> tm_prod a b ⊳⊳ tm_prod a' b'
  | parstep_beta : forall a t t' u u',
      t ⊳⊳ t' -> u ⊳⊳ u' -> tm_app (tm_abs a t) u ⊳⊳ subst 0 u t
  where "t '⊳⊳' u" := (parstep t u).

#[export]
Hint Constructors parstep : mltt.

Lemma parstep_refl : forall t,
  t ⊳⊳ t.
Proof.
  induction t; constructor; trivial.
Qed.

Lemma parstep_step : forall t u,
  t ⊳ u -> t ⊳⊳ u.
Proof.
  induction 1; eauto using parstep_refl with mltt.
Qed.

Lemma parstep_mstep : forall t u,
  t ⊳⊳ u -> t ⊳* u.
Proof.
  induction 1; eauto with mltt.
Qed.

Lemma parstep_subst : forall s t s' t',
  s ⊳⊳ s' -> t ⊳⊳ t' -> subst 0 s t ⊳⊳ subst 0 s' t'.
Admitted.

#[local]
Hint Extern 4 =>
  match goal with
  | H: exists w, _ /\ _ |- _ => let w := fresh w in
                                destruct H as [w [? ?]]
  end : mltt.

Lemma parstep_confluence : forall t u v,
  t ⊳⊳ u -> t ⊳⊳ v -> exists w, u ⊳⊳ w /\ v ⊳⊳ w.
Proof with eauto 16 with core mltt.
  intros t u v Htu.
  generalize dependent v.
  induction Htu; inversion 1; subst...
  - apply IHHtu1 in H2. apply IHHtu2 in H4...
  - admit.
  - apply IHHtu1 in H2. apply IHHtu2 in H4...
  - apply IHHtu1 in H2. apply IHHtu2 in H4...
  - admit.
Admitted.

Lemma step_confluence : forall t u v,
  t ⊳ u -> t ⊳ v -> exists w, u ⊳* w /\ v ⊳* w.
Proof.
  intros t u v Htu Htv.
  assert (H: exists w, u ⊳⊳ w /\ v ⊳⊳ w) by
    eauto using parstep_step, parstep_confluence.
  destruct H as [w [H1 H2]]. 
  eauto using parstep_mstep.
Qed.

Theorem confluence : forall t u v,
  t ⊳* u -> t ⊳* v -> exists w, u ⊳* w /\ v ⊳* w.
Proof.
  intros t u v Htu.
  generalize dependent v.
  induction Htu.
  - intro v. exists v; eauto with mltt.
  - admit.
Admitted.

#[export]
Hint Resolve confluence : mltt.

Reserved Notation "t '≃' u" (at level 50).

Inductive equiv (t : term) : term -> Prop :=
  | equiv_refl :
      t ≃ t
  | equiv_reduction : forall u,
      t ≃ u -> forall v, u ⊳ v -> t ≃ v
  | equiv_expansion : forall u,
      t ≃ u -> forall v, v ⊳ u -> t ≃ v
  where "t '≃' u" := (equiv t u).

#[export]
Hint Constructors equiv : mltt.


Definition equiv_diamond_ind
     : forall (t : term) (P : term -> Prop),
       P t ->
       (forall u : term, t ≃ u -> P u -> forall v w : term, v ⊳* u /\ v ⊳* w -> P w) ->
       forall u : term, t ≃ u -> P u.
Proof.
  intros.
  induction H1; eauto with mltt.
Qed.

(*
Check equiv_ind.

Inductive equiv (t : term) : term -> Prop :=
  | equiv_refl :
      t ≃ t
  | equiv_step : forall u,
      t ≃ u -> forall v w, v ⊳* u /\ v ⊳* w -> t ≃ w
  where "t '≃' u" := (equiv t u).

#[export]
Hint Constructors equiv : mltt.
*)

(** Note that eta equivalence is not included in equivalence, as this
    breaks the church rosser property. This is mentioned in Luo with
    examples in the beginning of chapter 3.

    More on eta-reduction and Church Rosser in Geuvers 93:
      http://www.cs.ru.nl/~herman/PUBS/LICS92_CRbh.pdf
    
    http://www.cs.ru.nl/~herman/PUBS/Proefschrift.pdf

    Initial discussion of eta-reduction issues:
      https://www.win.tue.nl/automath/archive/pdf/aut031.pdf *)

(*
Lemma equiv_reduction : forall t u,
  t ⊳ u -> t ≃ u.
Proof.
  eauto with mltt.
Qed.
*)

(*
Lemma equiv_reduction : forall t u,
  t ≃ u -> forall v, u ⊳* v -> t ≃ v.
Proof.
  eauto with mltt.
Qed.

Lemma equiv_expansion : forall t u,
  t ≃ u -> forall v, v ⊳* u -> t ≃ v.
Proof.
  eauto with mltt.
Qed.
*)

Lemma equiv_transitive : forall t u v,
  t ≃ u -> u ≃ v -> t ≃ v.
Proof.
  induction 2 using equiv_diamond_ind; eauto with mltt.
Qed.

Lemma equiv_symmetric : forall t u,
  t ≃ u -> u ≃ t.
Proof.
  induction 1.
  - trivial with mltt.
  - assert (w ≃ u). { destruct H0. eauto with mltt. }
    apply equiv_transitive with u; assumption.
Qed.

Lemma church_rosser : forall t u,
  t ≃ u -> exists z, t ⊳* z /\ u ⊳* z.
Proof.
  induction 1.
  - (* equiv_refl *)
    exists t; split; trivial with mltt.
  - (* equiv_step *)
    destruct H0.
    destruct IHequiv as [x [Htx Hux]].

(** At this point, we have a the following graph. Each node
    is a term, and every edge represents some some multi-step
    reduction ([⊳*]) flowing from top to bottom.

                                 v
                                / \
                           t ≃ u   w
                            \ /
                             x

    We can use the [confluence] theorem to introduce additional
    reductions, and construct the following diagram; ultimately
    demonstrating that the [t] and [w] will eventually reduce
    to some term [z].
                                 v
                                / \
                           t   u   w
                            \ / \ /
                             x   y
                              \ /
                               z   *)

    (* construct [y] *)
    assert (Hy: exists y, u ⊳* y /\ w ⊳* y)
      by solve [apply confluence with (t := v); assumption].
    destruct Hy as [y [Huy Hwy]].

    (* construct [z] *)
    assert (Hz: exists z, x ⊳* z /\ y ⊳* z)
      by solve [apply confluence with (t := u); assumption].
    destruct Hz as [z [Hxz Hyz]].

    exists z. eauto using mstep_trans.
Qed.

Inductive redk : term -> term -> Prop :=
  | redk_beta : forall a t u,
      redk (tm_app (tm_abs a t) u) (subst 0 u t)
  | redk_appl : forall t t',
      redk t t' -> forall u, redk (tm_app t u) (tm_app t' u).

Lemma redk_step : forall t u,
  redk t u -> t ⊳ u.
Proof.
  induction 1; eauto with mltt.
Qed.


Inductive sn (t : term) :=
  | sn_intro : (forall u, t ⊳ u -> sn u) -> sn t.

Lemma sn_normal : forall t,
  normal t -> sn t.
Proof.
  constructor. intros.
  exfalso. eauto using normal_not_reducible.
Qed.

Lemma sn_induction : forall P,
  (forall t, (forall u, t ⊳ u -> P u) -> P t) ->
  forall t, sn t -> P t.
Proof.
  intros. induction H.
  eauto with mltt.
Qed.


Check sn_ind.



Inductive keyredex : term -> Prop :=
  | keyredex_here : forall a t u,
      keyredex (tm_app (tm_abs a t) u)
  | keyredex_there : forall t u,
      keyredex t -> keyredex (tm_app t u).




Inductive cumulativity : nat -> term -> term -> Prop :=
  | cumu_equiv : forall t u,
      t ≃ u -> cumulativity 0 t u.
