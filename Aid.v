Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

Theorem not_true_is_false :forall b : bool,
  b <> true -> b = false .
Proof.
  intros [] H.
  unfold not in H.
  destruct H.
  reflexivity.
  reflexivity.
Qed.

(*如果前提为False，可以直接用内置的exfalso化简*)
Theorem not_true_is_false' :forall b : bool,
  b <> true -> b = false .
Proof.
  intros [] H.
  - unfold not in H.
    exfalso.
    apply H.
    reflexivity.
  - reflexivity.
Qed.

Theorem beq_true :forall n m, 
  n =? m = true -> n = m .
Proof.
  induction n.
  - induction m.
    + reflexivity.
    + discriminate.
  - induction m.
    + discriminate.
    + intros H.
      simpl in H.
      apply IHn in H.
      apply f_equal.
      apply H.
Qed.

Theorem beq_refl :forall n : nat, true = (n =? n).
Proof.
  induction n.
  - reflexivity.
  - simpl. apply IHn.
Qed.

Theorem beq_eq : forall n m,
  n =? m = true <-> n = m.
Proof.
  split.
  - apply beq_true.
  - intros.
    rewrite H.
    symmetry.
    apply beq_refl.
Qed.

Theorem beq_neq : forall x y ,
  x =? y = false <-> x <> y.
Proof.
 split.
  - rewrite <- beq_eq.
    unfold not.
    intros.
    rewrite H in H0.
    discriminate.
  - unfold not.
    intros.
    rewrite <- (not_true_is_false (x =? y)).
    reflexivity.
    unfold not.
    rewrite beq_eq.
    apply H.
Qed.

Lemma beq_comm : forall (m n:nat),
  (m =? n) = (n =? m).
Proof.
  intros.
  destruct (m =? n) eqn : H.
  apply beq_eq in H.
  rewrite H.
  apply beq_refl.
  apply beq_neq in H.
  symmetry. apply beq_neq.
  intro. subst.
  apply H. trivial.
Qed.

Lemma neq_comm : forall (m n:nat),
  (m <> n) <-> (n <> m).
Proof.
  split;
  intros H N;
  subst;
  apply H;
  trivial.
Qed.

Definition o2v (m:option nat) : nat :=
  match m with
  | Some n => n
  | None => 0
  end.

Definition v2o (m:nat) : option nat :=
  Some m. 



(* 移除列表中指定loc位置的元素 *)
Fixpoint remove_at (n : nat) (li : list nat) : list nat :=
  match n, li with
  | 1, _ :: tail => tail  
  | S m, head :: tail => head :: remove_at m tail  
  | _, _ => li  
  end.



