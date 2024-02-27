From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lists.List.
From ChurchRosser Require Import Tactics.

Create HintDb mltt.
#[global] Hint Constants Opaque : mltt.
#[global] Hint Variables Opaque : mltt.

Inductive term :=
  | tm_type
  | tm_var (x : nat)
  | tm_app (t u : term)
  | tm_prod (a b : term)
  | tm_abs (a t : term).

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
    reduced in [t], yielding [u]. The definition of [step] is not
    reflexive. *)
    
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
(** ** Parallel Reduction *)

Reserved Notation "t '⊳⊳' u"  (at level 60).
Reserved Notation "t '⊳⊳*' u"  (at level 60).

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

Inductive mparstep : term -> term -> Prop :=
  | mparstep_refl : forall t,
      t ⊳⊳* t
  | mparstep_step : forall t u v,
      t ⊳⊳ u -> u ⊳⊳* v -> t ⊳⊳* v
  where "t '⊳⊳*' u" := (mparstep t u).

#[export]
Hint Constructors parstep : mltt.
Hint Constructors mparstep : mltt.

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

Lemma mparstep_mstep : forall t u,
  t ⊳⊳* u <-> t ⊳* u.
Proof.
  split.
  - (* -> *)
    induction 1; auto with mltt.
    apply parstep_mstep in H.
    apply mstep_trans with u; assumption.
  - (* <- *)
    induction 1; auto with mltt.
    apply parstep_step in H.
    apply mparstep_step with u; assumption.
Qed.

Lemma mparstep_trans : forall t u v,
  t ⊳⊳* u -> u ⊳⊳* v -> t ⊳⊳* v.
Proof.
  intros t u v Htu.
  generalize dependent v.
  induction Htu; eauto with mltt.
Qed.

(* XXX: There is still some machinery require to prove local confluence
   for parallel reductions *)

Lemma parstep_local_confluence : forall t u v,
  t ⊳⊳ u -> t ⊳⊳ v -> exists w, u ⊳⊳ w /\ v ⊳⊳ w.
Proof with eauto 16 with core mltt.
  intros t u v Htu.
  generalize dependent v.
  induction Htu; inversion 1; subst...
  - apply IHHtu1 in H2. apply IHHtu2 in H4... admit.
  - admit.
  - apply IHHtu1 in H2. apply IHHtu2 in H4... admit.
  - apply IHHtu1 in H2. apply IHHtu2 in H4... admit.
  - admit.
Admitted.

Lemma parstep_confluence_right : forall t u v,
  t ⊳⊳ u -> t ⊳⊳* v -> exists w, u ⊳⊳* w /\ v ⊳⊳* w.
Proof.
  intros t u v Htu Htv.
  generalize dependent u.
  induction Htv; eauto with mltt.
  intros u' Htu'.

(** At this point, we have the following:

           t
         /   \
        u'    u
               \*
                v
 
    The ascii diagram above flows from top to bottom. Each edge
    represents a parallel step from one term to another.  Edges with
    an asterisk represent multi-step parallel reduction.
    
    We can flush out a little more of the graph by using the theorem
    of local confluence for parallel reduction. We can prove the
    existence of a term `w`, which completes the diamond formed
    between the terms `t`, `u`, and `u'`:
    
           t
         /   \
        u'     u
         \   /   \*
           w      v
 *)  

  assert (P: exists w, u ⊳⊳ w /\ u' ⊳⊳ w) by
    eauto using parstep_local_confluence.
  destruct P as [w [H1 H2]].

(** Now we can see that the triangle formed by `w`, `u`, and `v`
    forms the top half of a diamond. We can apply the induction
    hypothesis to prove the existence of a term `x` which completes
    our proof:
    
           t
         /   \
        u'     u
         \   /   \*
           w      v
             \*  /*
               x
     
*)
  
  apply IHHtv in H1.
  destruct H1 as [x [Hwx Hvx]].
  exists x. eauto with mltt.
Qed.

Theorem parstep_confluence : forall t u v,
  t ⊳⊳* u -> t ⊳⊳* v -> exists w, u ⊳⊳* w /\ v ⊳⊳* w.
Proof.
  intros t u v Htu.
  generalize dependent v.
  induction Htu; eauto with mltt.
  - intros u' Htu'.
    assert (P: exists w, u ⊳⊳* w /\ u' ⊳⊳* w) by
      eauto using parstep_confluence_right.
    destruct P as [w [H1 H2]].
    apply IHHtu in H1.
    destruct H1 as [x [Hwx Hvx]].
    assert (u' ⊳⊳* x) by
      solve [eapply mparstep_trans; eauto].
    exists x. auto.
Qed.

(** Now we can finally prove confluence. Knowing that parallel multi-step
    reduction and non-parallel multi-step reduction are equivalent
    (i.e. `mparstep_mstep`), we can leverage `parstep_confluence` to prove
    that the reduction of terms is confluent. *)

Theorem confluence : forall t u v,
  t ⊳* u -> t ⊳* v -> exists w, u ⊳* w /\ v ⊳* w.
Proof.
  intros t u v Htu Htv.
  assert (H: exists w, u ⊳⊳* w /\ v ⊳⊳* w). {
    apply mparstep_mstep in Htu.
    apply mparstep_mstep in Htv.
    eauto using parstep_confluence.
  }
  destruct H as [w [H1 H2]].
  apply mparstep_mstep in H1.
  apply mparstep_mstep in H2.
  exists w. exact (conj H1 H2).
Qed.

#[export]
Hint Resolve confluence : mltt.

(** ------------------------------------------------------------------------ *)
(** ** Confluence (Church-Rosser) *)

Reserved Notation "t '≃' u" (at level 50).

Inductive equiv (t : term) : term -> Prop :=
  | equiv_refl :
      t ≃ t
  | equiv_step : forall u,
      t ≃ u -> forall v w, v ⊳* u /\ v ⊳* w -> t ≃ w
  where "t '≃' u" := (equiv t u).

#[export]
Hint Constructors equiv : mltt.


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
                               z
 *)

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
