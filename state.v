Require Import util.
Require Import Aid.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

(*定义五元组来表示系统状态*)
Definition storeO := id -> nat.
Definition storeV := id -> nat.
Definition storeS := id -> list nat.
Definition heapR := nat -> option nat.
Definition heapO := nat -> option (list (option nat)).

(*定义空堆*)
Definition emp_heapR : heapR :=
  fun (n: nat) => None.

Definition emp_heapO : heapO :=
  fun (n: nat) => None.

(*定义命题 : 在堆的定义域中*)
Definition in_domR (loc: nat) (hr: heapR) : Prop :=
  exists n, hr loc = Some n.

Definition in_domO (bloc: nat) (ho: heapO) : Prop :=
  exists l, ho bloc = Some l.

(*定义命题 : 不在堆的定义域中*)
Definition not_in_domR (loc: nat) (hr: heapR) : Prop :=
  hr loc = None.

Definition not_in_domO (bloc: nat) (ho: heapO) : Prop :=
  ho bloc = None.

Theorem in_not_in_dec_R :
  forall l h, {in_domR l h} + {not_in_domR l h}.
Proof.
  intros l h.
  unfold in_domR, not_in_domR.
  destruct (h l).
  - left. exists n. auto.
  - right. auto.
Qed.

Theorem in_not_in_dec_O :
  forall l h, {in_domO l h} + {not_in_domO l h}.
Proof.
  intros l h.
  unfold in_domO, not_in_domO.
  destruct (h l).
  - left. exists l0. auto.
  - right. auto.
Qed.

(*定义命题:两堆不相交*)
Definition disjointR (h1 h2: heapR) : Prop :=
  forall l, not_in_domR l h1 \/ not_in_domR l h2.

Definition disjointO (h1 h2: heapO) : Prop :=
  forall l, not_in_domO l h1 \/ not_in_domO l h2.

Definition h_unionR (h1 h2: heapR) : heapR :=
  fun l =>
    if (in_not_in_dec_R l h1) then h1 l else h2 l.

Definition h_unionO (h1 h2: heapO) : heapO :=
  fun l =>
    if (in_not_in_dec_O l h1) then h1 l else h2 l.  

Definition h_subsetR (h1 h2: heapR) : Prop :=
  forall loc n, h1 loc = Some n -> h2 loc = Some n.

Definition h_subsetO (h1 h2: heapO) : Prop :=
  forall bloc l, h1 bloc = Some l -> h2 bloc = Some l.

(* 栈的更新操作 *)
Definition sO_update (s: storeO) (x: id) (n: nat) : storeO :=
  fun x' => if beq_id x x' then n else s x'.

Definition sV_update (s: storeV) (x: id) (n: nat) : storeV :=
  fun x' => if beq_id x x' then n else s x'.

Definition sS_update (s: storeS) (x: id) (nli: list nat) : storeS :=
  fun x' => if beq_id x x' then nli else s x'.

Notation "x '!so->' v ';' m" := (sO_update m x v)
            (at level 100, v at next level, right associativity).

Notation "x '!sv->' v ';' m" := (sV_update m x v)
            (at level 100, v at next level, right associativity).

Notation "x '!ss->' v ';' m" := (sS_update m x v)
            (at level 100, v at next level, right associativity).

(* 堆的更新操作 *)
Definition hR_update (h: heapR) (loc: nat) (n: nat) : heapR :=
  fun loc' => if Nat.eqb loc loc' then Some n else h loc'.

Definition hO_update (h: heapO) (bloc: nat) (l: list (option nat)) : heapO :=
  fun bloc' => if Nat.eqb bloc bloc' then Some l else h bloc'.

Notation "x '!hr->' v ';' m" := (hR_update m x v)
            (at level 100, v at next level, right associativity).

Notation "x '!ho->' v ';' m" := (hO_update m x v)
            (at level 100, v at next level, right associativity).

(* 堆的移除操作 *)
Definition hR_remove (h:heapR) (l:nat) : heapR :=
fun x => if Nat.eqb x l then None else h x.

Definition hR_removes (h : heapR) (keys : list nat) : heapR :=
  fold_left (fun acc key =>  hR_remove acc key) keys h.

Definition hO_remove (h:heapO) (l:nat) : heapO :=
fun x => if Nat.eqb x l then None else h x.

Lemma sO_update_eq : forall storeO x v,
   (x !so-> v ; storeO) x = v.
Proof.
  intros.
  unfold sO_update.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Lemma sO_update_neq : forall storeO x1 x2 v,
   x1 <> x2
->(x2 !so-> v ; storeO) x1 = storeO x1.
Proof.
  intros.
  unfold sO_update.
  apply beq_neq_id in H.
  rewrite beq_comm_id in H.
  rewrite H.
  reflexivity.
Qed.

Lemma sV_update_eq : forall storeV x v,
   (x !sv-> v ; storeV) x = v.
Proof.
  intros.
  unfold sV_update.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Theorem sV_update_neq :forall sV x1 x2 v,
   x1 <> x2
->(x2 !sv-> v ; sV) x1 = sV x1.
Proof.
  intros.
  unfold sV_update.
  apply beq_neq_id in H.
  rewrite beq_comm_id in H.
  rewrite H.
  reflexivity.
Qed.

Lemma sS_update_eq : forall storeS x v,
   (x !ss-> v ; storeS) x = v.
Proof.
  intros.
  unfold sS_update.
  rewrite beq_id_refl.
  reflexivity.
Qed.

Theorem sS_update_neq :forall sS x1 x2 v,
   x1 <> x2
->(x2 !ss-> v ; sS) x1 = sS x1.
Proof.
  intros.
  unfold sS_update.
  apply beq_neq_id in H.
  rewrite beq_comm_id in H.
  rewrite H.
  reflexivity.
Qed.

Lemma hR_update_eq : forall heapR x v,
   (x !hr-> v ; heapR) x = Some v.
Proof.
  intros.
  unfold hR_update.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Lemma hR_update_neq : forall heapR x1 x2 v,
   x1 <> x2
->(x2 !hr-> v ; heapR) x1 = heapR x1.

Proof.
  intros.
  unfold hR_update.
  apply beq_neq in H.
  rewrite beq_comm in H.
  rewrite H.
  reflexivity.
Qed.

Lemma hO_update_eq : forall heapO x v,
   (x !ho-> v ; heapO) x = Some v.
Proof.
  intros.
  unfold hO_update.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem hO_update_neq :forall hO x1 x2 v,
   x1 <> x2
->(x2 !ho-> v ; hO) x1 = hO x1.
Proof.
  intros.
  unfold hO_update.
  apply beq_neq in H.
  rewrite beq_comm in H.
  rewrite H.
  reflexivity.
Qed.

Lemma sO_update_shadow : forall storeO x v1 v2,
  (x !so-> v2 ; x !so-> v1 ; storeO) = (x !so-> v2; storeO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sO_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sO_update_shadow_2 : forall storeO x y v1 v2 v3,
  (x !so-> v2 ; y !so-> v1 ; x !so-> v3 ;storeO) 
= (x !so-> v2; y !so-> v1; storeO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sO_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sO_update_shadow_3 : forall storeO x y z v1 v2 v3 v4,
  (x !so-> v2 ; y !so-> v1 ; z !so-> v4 ; x !so-> v3 ;storeO) 
= (x !so-> v2; y !so-> v1 ; z !so-> v4 ; storeO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sO_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sO_update_shadow_4 : forall storeO x x2 x3 x4 v1 v5 v6 v7 v8,
  (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ;  x !so-> v1 ; storeO) 
= (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ; storeO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sO_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sO_update_shadow_5 : forall storeO x x2 x3 x4 x5 v1 v4 v5 v6 v7 v8,
  (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ; 
   x5 !so-> v4 ; x !so-> v1 ; storeO) 
= (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ; 
   x5 !so-> v4 ; storeO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sO_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sO_update_shadow_8 : forall storeO x x2 x3 x4 x5 x6 x7  v1 v2 v3 v4 v5 v6 v7 v8,
  (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ; 
   x5 !so-> v4 ; x6 !so-> v3 ; x7 !so-> v2 ; x !so-> v1 ; storeO) 
= (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ; 
   x5 !so-> v4 ; x6 !so-> v3 ; x7 !so-> v2 ; storeO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sO_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sO_update_shadow_9 : forall storeO x x2 x3 x4 x5 x6 x7 x8 v1 v2 v3 v4 v5 v6 v7 v8 v9,
  (x !so-> v9 ; x2 !so-> v8 ; x3 !so-> v7 ; x4 !so-> v6 ; 
   x5 !so-> v5 ; x6 !so-> v4 ; x7 !so-> v3 ; x8 !so-> v2 ; x !so-> v1 ; storeO) 
= (x !so-> v9 ; x2 !so-> v8 ; x3 !so-> v7 ; x4 !so-> v6 ; 
   x5 !so-> v5 ; x6 !so-> v4 ; x7 !so-> v3 ; x8 !so-> v2 ; storeO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sO_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sO_update_shadow_12 : forall storeO x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12,
  (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ;
   x8 !so-> v9 ; x9 !so-> v10 ; x10 !so-> v11 ; x11 !so-> v12 ; 
   x5 !so-> v4 ; x6 !so-> v3 ; x7 !so-> v2 ; x !so-> v1 ; storeO) 
= (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ; 
   x8 !so-> v9 ; x9 !so-> v10 ; x10 !so-> v11 ; x11 !so-> v12 ; 
   x5 !so-> v4 ; x6 !so-> v3 ; x7 !so-> v2 ; storeO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sO_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sO_update_shadow_14 : forall storeO x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13  v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 ,
  (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ;
   x8 !so-> v9 ; x9 !so-> v10 ; x10 !so-> v11 ; x11 !so-> v12 ;
   x12 !so-> v13 ; x13 !so-> v14 ; x5 !so-> v4 ; 
   x6 !so-> v3 ; x7 !so-> v2 ; x !so-> v1 ; storeO) 
= (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ; 
   x8 !so-> v9 ; x9 !so-> v10 ; x10 !so-> v11 ; x11 !so-> v12 ;
   x12 !so-> v13 ; x13 !so-> v14 ; x5 !so-> v4 ; 
   x6 !so-> v3 ; x7 !so-> v2 ; storeO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sO_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sO_update_shadow_15 : forall storeO x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
  (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ;
   x8 !so-> v9 ; x9 !so-> v10 ; x10 !so-> v11 ; x11 !so-> v12 ;
   x12 !so-> v13 ; x13 !so-> v14 ; x14 !so-> v15 ; x5 !so-> v4 ; 
   x6 !so-> v3 ; x7 !so-> v2 ; x !so-> v1 ; storeO) 
= (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ; 
   x8 !so-> v9 ; x9 !so-> v10 ; x10 !so-> v11 ; x11 !so-> v12 ;
   x12 !so-> v13 ; x13 !so-> v14 ; x14 !so-> v15 ;  x5 !so-> v4 ; 
   x6 !so-> v3 ; x7 !so-> v2 ; storeO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sO_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sO_update_shadow_16 : forall storeO x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16,
  (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ;
   x8 !so-> v9 ; x9 !so-> v10 ; x10 !so-> v11 ; x11 !so-> v12 ;
   x12 !so-> v13 ; x13 !so-> v14 ; x14 !so-> v15 ; x15 !so-> v16 ; 
   x5 !so-> v4 ; x6 !so-> v3 ; x7 !so-> v2 ; x !so-> v1 ; storeO) 
= (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ; 
   x8 !so-> v9 ; x9 !so-> v10 ; x10 !so-> v11 ; x11 !so-> v12 ;
   x12 !so-> v13 ; x13 !so-> v14 ; x14 !so-> v15 ; x15 !so-> v16 ; 
   x5 !so-> v4 ; x6 !so-> v3 ; x7 !so-> v2 ; storeO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sO_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_add : forall storeV x n,
  (x !sv-> (n * 0 + 1);storeV) = (x !sv-> 1;storeV).

Proof.
  intros.
  unfold sV_update. 
  apply functional_extensionality.
  intros x'.
  destruct (beq_id x x') eqn:Heq.
  - rewrite Nat.mul_0_r.
    reflexivity. 
  - simpl. reflexivity.
Qed.

Lemma sV_update_shadow : forall storeV x v1 v2,
  (x !sv-> v2 ; x !sv-> v1 ; storeV) = (x !sv-> v2; storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_3 : forall storeV x y v1 v2 v3,
  (x !sv-> v2 ; y !sv-> v1 ; x !sv-> v3 ;storeV) 
= (x !sv-> v2; y !sv-> v1; storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_4 : forall storeV x y z v1 v2 v3 v4,
  (x !sv-> v4 ; z !sv-> v3 ; y !sv-> v2 ; x !sv-> v1 ;storeV) 
= (x !sv-> v4; z !sv-> v3 ; y !sv-> v2; storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_5 : forall storeV x y z x2 v1 v2 v3 v4 v5,
  (x !sv-> v4 ; x2 !sv-> v5 ; z !sv-> v3 ; y !sv-> v2 ; x !sv-> v1 ;storeV) 
= (x !sv-> v4 ; x2 !sv-> v5 ;  z !sv-> v3 ; y !sv-> v2; storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_6 : forall storeV x y z x2 x3 v1 v2 v3 v4 v5 v6,
  (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; x !sv-> v1 ;storeV) 
= (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2; storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_9 : forall storeV x y z x2 x3 x4 x5 x6 v1 v2 v3 v4 v5 v6 v7 v8 v9,
  (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9 ; x !sv-> v1 ;storeV) 
=   (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9  ;storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_10 : forall storeV x y z x2 x3 x4 x5 x6 x7 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
  (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9 ; x7 !sv-> v10 ; x !sv-> v1 ;storeV) 
=   (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9 ; x7 !sv-> v10 ;storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_12 : forall storeV x y z x2 x3 x4 x5 x6 x7 x8 x9 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12,
  (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x8 !sv-> v11 ; x9 !sv-> v12 ; x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9 ; 
   x7 !sv-> v10 ; x !sv-> v1 ;storeV) 
=   (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x8 !sv-> v11 ; x9 !sv-> v12 ; x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9 ; 
   x7 !sv-> v10 ;storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_13 : forall storeV x y z x2 x3 x4 x5 x6 x7 x8 x9 x10 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13,
  (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x8 !sv-> v11 ; x9 !sv-> v12 ; x10 !sv-> v13 ; x4 !sv-> v7 ; x5 !sv-> v8 ; 
   x6 !sv-> v9 ;  x7 !sv-> v10 ; x !sv-> v1 ;storeV) 
=   (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x8 !sv-> v11 ; x9 !sv-> v12 ; x10 !sv-> v13 ; x4 !sv-> v7 ; x5 !sv-> v8 ; 
   x6 !sv-> v9 ;  x7 !sv-> v10 ;storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_14 : forall storeV x y z x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 ,
  (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x8 !sv-> v11 ; x9 !sv-> v12 ; x10 !sv-> v13 ; x11 !sv-> v14 ; x4 !sv-> v7 ; 
   x5 !sv-> v8 ; x6 !sv-> v9 ; x7 !sv-> v10 ; x !sv-> v1 ;storeV) 
=   (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x8 !sv-> v11 ; x9 !sv-> v12 ; x10 !sv-> v13 ; x11 !sv-> v14 ;  x4 !sv-> v7 ; 
   x5 !sv-> v8 ; x6 !sv-> v9 ; x7 !sv-> v10 ;storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_15 : forall storeV x y z x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 ,
  (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x8 !sv-> v11 ; x9 !sv-> v12 ; x10 !sv-> v13 ; x11 !sv-> v14 ; x12 !sv-> v15 ; 
   x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9 ; x7 !sv-> v10 ; x !sv-> v1 ;storeV) 
=   (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x8 !sv-> v11 ; x9 !sv-> v12 ; x10 !sv-> v13 ; x11 !sv-> v14 ; x12 !sv-> v15 ; 
   x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9 ; x7 !sv-> v10 ;storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_17 : forall storeV x y z x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17,
  (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x8 !sv-> v11 ; x9 !sv-> v12 ; x10 !sv-> v13 ; x11 !sv-> v14 ; x12 !sv-> v15 ; 
   x13 !sv-> v16 ; x14 !sv-> v17 ; x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9 ; 
   x7 !sv-> v10 ; x !sv-> v1 ;storeV) 
=   (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x8 !sv-> v11 ; x9 !sv-> v12 ; x10 !sv-> v13 ; x11 !sv-> v14 ; x12 !sv-> v15 ; 
   x13 !sv-> v16 ; x14 !sv-> v17 ; x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9 ; 
   x7 !sv-> v10 ;storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sS_update_shadow : forall storeS x v1 v2,
  (x !ss-> v2 ; x !ss-> v1 ; storeS) = (x !ss-> v2; storeS).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sS_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sS_update_shadow_3 : forall storeS x y v1 v2 v3,
  (x !ss-> v2 ; y !ss-> v1 ; x !ss-> v3 ;storeS) 
= (x !ss-> v2; y !ss-> v1; storeS).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sS_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sS_update_shadow_4 : forall storeS x y z v1 v2 v3 v4,
  (x !ss-> v4 ; y !ss-> v3 ; z !ss-> v2 ; x !ss-> v1 ;storeS) 
= (x !ss-> v4; y !ss-> v3; z !ss-> v2 ; storeS).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sS_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sS_update_shadow_5 : forall storeS x y z x2 v1 v2 v3 v4 v5,
  (x !ss-> v4 ; y !ss-> v3 ; x2 !ss-> v5 ; z !ss-> v2 ; x !ss-> v1 ;storeS) 
= (x !ss-> v4 ; y !ss-> v3;  x2 !ss-> v5 ; z !ss-> v2 ; storeS).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sS_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sS_update_shadow_6 : forall storeS x y z x2 x3 v1 v2 v3 v4 v5 v6,
  (x !ss-> v4 ; y !ss-> v3 ; x2 !ss-> v5 ; x3 !ss-> v6 ; z !ss-> v2 ; x !ss-> v1 ;storeS) 
= (x !ss-> v4; y !ss-> v3;  x2 !ss-> v5 ; x3 !ss-> v6 ; z !ss-> v2 ; storeS).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sS_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow : forall heapR x v1 v2,
  (x !hr-> v2 ; x !hr-> v1 ; heapR) = (x !hr-> v2; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hO_update_shadow : forall heapO x v1 v2,
  (x !ho-> v2 ; x !ho-> v1 ; heapO) = (x !ho-> v2; heapO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hO_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_remove_neq : forall hR x1 x2 v,
   x1 <> x2
-> hR_remove (x2 !hr-> v;hR) x1 
   = (x2 !hr-> v; hR_remove hR x1).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_remove.
  destruct (Nat.eqb x x1) eqn:H1.
  + rewrite beq_eq in H1.
    rewrite H1,hR_update_neq.
    rewrite <- beq_refl.
    trivial. trivial.
  + destruct (Nat.eqb x x2) eqn:H2.
    - rewrite beq_eq in H2. subst.
      repeat rewrite hR_update_eq. trivial.
    - rewrite beq_neq in H2.
      repeat rewrite hR_update_neq; trivial.
      rewrite H1.
      trivial.
Qed.

Lemma hR_remove_eq : forall hR x1 x2 v,
   x1 <> x2
-> (hR_remove (x2 !hr-> v;hR) x1) x2 = Some v.
Proof.
  intros.
  unfold hR_remove.
  apply neq_comm in H.
  rewrite <- beq_neq in H.
  rewrite H.
  apply hR_update_eq.
Qed.

Lemma hR_remove_neq2 : forall hR x1 x2 x3 v,
   x1 <> x2 -> x3 <> x2
-> (hR_remove (x1 !hr-> v;hR) x3) x2 
   = (hR_remove hR x3) x2.
Proof.
  intros.
  unfold hR_remove.
  apply neq_comm in H0.
  rewrite <- beq_neq in H0.
  rewrite H0.
  apply hR_update_neq.
  auto.
Qed. 

Lemma hR_remove_emp : forall x,
  hR_remove emp_heapR x = emp_heapR.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_remove.
  destruct (Nat.eqb x0 x) eqn:H1;
  trivial.
Qed.

Lemma hR_remove_work : forall hR x v,
   not_in_domR x hR
-> hR_remove (x !hr-> v;hR) x = hR.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_remove.
  destruct (Nat.eqb x0 x) eqn:H1.
  - rewrite beq_eq in H1. subst. auto.
  - rewrite beq_neq in H1.
    rewrite hR_update_neq; auto.
Qed.

Lemma hO_remove_neq : forall hO x1 x2 v,
   x1 <> x2
-> hO_remove (x2 !ho-> v;hO) x1 
   = (x2 !ho-> v; hO_remove hO x1).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hO_remove.
  destruct (Nat.eqb x x1) eqn:H1.
  + rewrite beq_eq in H1.
    rewrite H1,hO_update_neq.
    rewrite <- beq_refl.
    trivial. trivial.
  + destruct (Nat.eqb x x2) eqn:H2.
    - rewrite beq_eq in H2. subst.
      repeat rewrite hO_update_eq. trivial.
    - rewrite beq_neq in H2.
      repeat rewrite hO_update_neq; trivial.
      rewrite H1.
      trivial.
Qed.

Lemma hO_remove_eq : forall hO x1 x2 v,
   x1 <> x2
-> (hO_remove (x2 !ho-> v;hO) x1) x2 = Some v.
Proof.
  intros.
  unfold hO_remove.
  apply neq_comm in H.
  rewrite <- beq_neq in H.
  rewrite H.
  apply hO_update_eq.
Qed.

Lemma hO_remove_neq2 : forall hO x1 x2 x3 v,
   x1 <> x2 -> x3 <> x2
-> (hO_remove (x1 !ho-> v;hO) x3) x2 
   = (hO_remove hO x3) x2.
Proof.
  intros.
  unfold hO_remove.
  apply neq_comm in H0.
  rewrite <- beq_neq in H0.
  rewrite H0.
  apply hO_update_neq.
  auto.
Qed. 

Lemma hO_remove_emp : forall x,
  hO_remove emp_heapO x = emp_heapO.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hO_remove.
  destruct (Nat.eqb x0 x) eqn:H1;
  trivial.
Qed.

Lemma hO_remove_work : forall hO x v,
   not_in_domO x hO
-> hO_remove (x !ho-> v;hO) x = hO.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hO_remove.
  destruct (Nat.eqb x0 x) eqn:H1.
  - rewrite beq_eq in H1. subst. auto.
  - rewrite beq_neq in H1.
    rewrite hO_update_neq; auto.
Qed.

(* 定义系统状态 *)
Definition state : Type := (storeO * storeV * storeS * heapR * heapO).

Inductive ext_state : Type :=
| St: state -> ext_state    (* normal state *)
| Abt: ext_state.           (* abort *)


