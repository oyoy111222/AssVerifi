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

Lemma sO_update_shadow_7 : forall storeO x x2 x3 x4 x5 x6 v1 v2 v3 v4 v5 v6 v7 ,
  (x !so-> v7 ;  x2 !so-> v6 ; x3 !so-> v5 ; 
   x4 !so-> v4 ; x5 !so-> v3 ; x6 !so-> v2 ; x !so-> v1 ; storeO) 
= (x !so-> v7 ;  x2 !so-> v6 ; x3 !so-> v5 ; 
   x4 !so-> v4 ; x5 !so-> v3 ; x6 !so-> v2 ;  storeO).
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

Lemma sO_update_shadow_10 : forall storeO x x2 x3 x4 x5 x6 x7 x8 x9 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ,
  (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ;
   x8 !so-> v9 ; x9 !so-> v10 ;  x5 !so-> v4 ; x6 !so-> v3 ; x7 !so-> v2 ; x !so-> v1 ; storeO) 
= (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ; 
   x8 !so-> v9 ; x9 !so-> v10 ; x5 !so-> v4 ; x6 !so-> v3 ; x7 !so-> v2 ; storeO).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sO_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sO_update_shadow_11 : forall storeO x x2 x3 x4 x5 x6 x7 x8 x9 x10 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11,
  (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ;
   x8 !so-> v9 ; x9 !so-> v10 ; x10 !so-> v11 ;
   x5 !so-> v4 ; x6 !so-> v3 ; x7 !so-> v2 ; x !so-> v1 ; storeO) 
= (x !so-> v8 ; x2 !so-> v7 ; x3 !so-> v6 ; x4 !so-> v5 ; 
   x8 !so-> v9 ; x9 !so-> v10 ; x10 !so-> v11 ; 
   x5 !so-> v4 ; x6 !so-> v3 ; x7 !so-> v2 ; storeO).
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

Lemma sV_update_shadow_7 : forall storeV x y z x2 x3 x4 v1 v2 v3 v4 v5 v6 v7,
  (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x4 !sv-> v7 ; x !sv-> v1 ;storeV) 
= (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; x4 !sv-> v7 ;storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_8 : forall storeV x y z x2 x3 x4 x5 v1 v2 v3 v4 v5 v6 v7 v8,
  (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x4 !sv-> v7 ; x5 !sv-> v8 ; x !sv-> v1 ;storeV) 
= (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x4 !sv-> v7 ; x5 !sv-> v8 ;storeV).
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
= (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
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
= (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9 ; x7 !sv-> v10 ;storeV).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold sV_update.
  destruct (beq_id x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma sV_update_shadow_11 : forall storeV x y z x2 x3 x4 x5 x6 x7 x8 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11,
  (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x8 !sv-> v11 ; x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9 ; 
   x7 !sv-> v10 ; x !sv-> v1 ;storeV) 
= (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
   x8 !sv-> v11 ; x4 !sv-> v7 ; x5 !sv-> v8 ; x6 !sv-> v9 ; 
   x7 !sv-> v10 ;storeV).
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
= (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
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
= (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
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
= (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
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
= (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
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
= (x !sv-> v4 ; x2 !sv-> v5 ; x3 !sv-> v6 ; z !sv-> v3 ; y !sv-> v2 ; 
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

Lemma hR_update_shadow_3 : forall heapR x x2  v1 v2 v3  ,
  (x !hr-> v1 ; x2 !hr-> v2 ; x !hr-> v3 ; heapR) 
= (x !hr-> v1 ; x2 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_4 : forall heapR x x2 x3 v1 v2 v3 v4  ,
  (x !hr-> v1 ; x2 !hr-> v2 ; x3 !hr-> v3 ; x !hr-> v4 ; heapR) 
= (x !hr-> v1 ; x2 !hr-> v2 ; x3 !hr-> v3 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_6 : forall heapR x x2 x3 x4 x5 v1 v2 v3 v4 v5 v6 ,
  (x !hr-> v6 ; x2 !hr-> v5 ; x3 !hr-> v4 ; x4 !hr-> v3 ; x5 !hr-> v2 ; x !hr-> v1 ; heapR) 
= (x !hr-> v6 ; x2 !hr-> v5 ; x3 !hr-> v4 ; x4 !hr-> v3 ; x5 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_9 : forall heapR x x2 x3 x4 x5 x6 x7 x8 v1 v2 v3 v4 v5 v6 v7 v8 v9,
  (x !hr-> v9 ; x2 !hr-> v8 ; x3 !hr-> v7 ; x4 !hr-> v6 ; 
   x5 !hr-> v5 ; x6 !hr-> v4 ; x7 !hr-> v3 ; x8 !hr-> v2 ; x !hr-> v1 ; heapR) 
= (x !hr-> v9 ; x2 !hr-> v8 ; x3 !hr-> v7 ; x4 !hr-> v6 ; 
   x5 !hr-> v5 ; x6 !hr-> v4 ; x7 !hr-> v3 ; x8 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_10 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10,
  (x !hr-> v9 ; x9 !hr-> v10 ; x2 !hr-> v8 ; x3 !hr-> v7 ; x4 !hr-> v6 ; 
   x5 !hr-> v5 ; x6 !hr-> v4 ; x7 !hr-> v3 ; x8 !hr-> v2 ; x !hr-> v1 ; heapR) 
= (x !hr-> v9 ; x9 !hr-> v10 ; x2 !hr-> v8 ; x3 !hr-> v7 ; x4 !hr-> v6 ; 
   x5 !hr-> v5 ; x6 !hr-> v4 ; x7 !hr-> v3 ; x8 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_12 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11  
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 ,
  (x !hr-> v12 ; x2 !hr-> v11 ; x3 !hr-> v10 ; x4 !hr-> v9 ; x5 !hr-> v8 ; x6 !hr-> v7 ; x7 !hr-> v6 ; 
   x8 !hr-> v5 ; x9 !hr-> v4 ; x10 !hr-> v3 ; x11 !hr-> v2 ; x !hr-> v1 ; heapR) 
= (x !hr-> v12 ; x2 !hr-> v11 ; x3 !hr-> v10 ; x4 !hr-> v9 ; x5 !hr-> v8 ; x6 !hr-> v7 ; x7 !hr-> v6 ; 
   x8 !hr-> v5 ; x9 !hr-> v4 ; x10 !hr-> v3 ; x11 !hr-> v2 ; heapR) .
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_13 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12  v13,
  (x !hr-> v12 ; x12 !hr-> v13 ; x2 !hr-> v11 ; x3 !hr-> v10 ; x4 !hr-> v9 ; x5 !hr-> v8 ; x6 !hr-> v7 ; x7 !hr-> v6 ; 
   x8 !hr-> v5 ; x9 !hr-> v4 ; x10 !hr-> v3 ; x11 !hr-> v2 ; x !hr-> v1 ; heapR) 
= (x !hr-> v12 ; x12 !hr-> v13 ; x2 !hr-> v11 ; x3 !hr-> v10 ; x4 !hr-> v9 ; x5 !hr-> v8 ; x6 !hr-> v7 ; x7 !hr-> v6 ; 
   x8 !hr-> v5 ; x9 !hr-> v4 ; x10 !hr-> v3 ; x11 !hr-> v2 ; heapR) .
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_15 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 ,
  (x !hr-> v15 ; x2 !hr-> v14 ; x3 !hr-> v13 ; x4 !hr-> v12 ; x5 !hr-> v11 ; x6 !hr-> v10 ; x7 !hr-> v9 ;
   x8 !hr-> v8 ; x9 !hr-> v7 ; x10 !hr-> v6 ; x11 !hr-> v5 ; x12 !hr-> v4 ; x13 !hr-> v3 ; x14 !hr-> v2 ; 
   x !hr-> v1 ; heapR) 
= (x !hr-> v15 ; x2 !hr-> v14 ; x3 !hr-> v13 ; x4 !hr-> v12 ; x5 !hr-> v11 ; x6 !hr-> v10 ; x7 !hr-> v9 ;
   x8 !hr-> v8 ; x9 !hr-> v7 ; x10 !hr-> v6 ; x11 !hr-> v5 ; x12 !hr-> v4 ; x13 !hr-> v3 ; x14 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_18 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 ,
  (x !hr-> v18 ; x2 !hr-> v17 ; x3 !hr-> v16 ; x4 !hr-> v15 ; x5 !hr-> v14 ; x6 !hr-> v13 ; x7 !hr-> v12 ; 
   x8 !hr-> v11 ; x9 !hr-> v10 ; x10 !hr-> v9 ; x11 !hr-> v8 ; x12 !hr-> v7 ; x13 !hr-> v6 ; x14 !hr-> v5 ;
   x15 !hr-> v4 ; x16 !hr-> v3 ; x17 !hr-> v2 ; x !hr-> v1 ; heapR) 
= (x !hr-> v18 ; x2 !hr-> v17 ; x3 !hr-> v16 ; x4 !hr-> v15 ; x5 !hr-> v14 ; x6 !hr-> v13 ; x7 !hr-> v12 ; 
   x8 !hr-> v11 ; x9 !hr-> v10 ; x10 !hr-> v9 ; x11 !hr-> v8 ; x12 !hr-> v7 ; x13 !hr-> v6 ; x14 !hr-> v5 ;
   x15 !hr-> v4 ; x16 !hr-> v3 ; x17 !hr-> v2 ; heapR) .
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_19 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19,
  (x !hr-> v19 ; x2 !hr-> v18 ; x3 !hr-> v17 ; x4 !hr-> v16 ; x5 !hr-> v15 ; x6 !hr-> v14 ; x7 !hr-> v13 ; x8 !hr-> v12 ; 
   x9 !hr-> v11 ; x10 !hr-> v10 ; x11 !hr-> v9 ; x12 !hr-> v8 ; x13 !hr-> v7 ; x14 !hr-> v6 ; x15 !hr-> v5 ;
   x16 !hr-> v4 ; x17 !hr-> v3 ; x18 !hr-> v2 ; x !hr-> v1 ; heapR) 
= (x !hr-> v19 ; x2 !hr-> v18 ; x3 !hr-> v17 ; x4 !hr-> v16 ; x5 !hr-> v15 ; x6 !hr-> v14 ; x7 !hr-> v13 ; x8 !hr-> v12 ; 
   x9 !hr-> v11 ; x10 !hr-> v10 ; x11 !hr-> v9 ; x12 !hr-> v8 ; x13 !hr-> v7 ; x14 !hr-> v6 ; x15 !hr-> v5 ;
   x16 !hr-> v4 ; x17 !hr-> v3 ; x18 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_20 : forall heapR x  x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 
                                   v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v23,
  (x !hr-> v23 ; x4 !hr-> v20 ; x5 !hr-> v19 ; x6 !hr-> v18 ; x7 !hr-> v17 ; x8 !hr-> v16 ; x9 !hr-> v15 ; 
   x10 !hr-> v14 ; x11 !hr-> v13 ; x12 !hr-> v12 ; x13 !hr-> v11 ; x14 !hr-> v10 ; x15 !hr-> v9 ; x16 !hr-> v8 ; x17 !hr-> v7 ; 
   x18 !hr-> v6 ; x19 !hr-> v5 ; x20 !hr-> v4 ; x21 !hr-> v3 ; x !hr-> v1 ; heapR) 
= (x !hr-> v23 ; x4 !hr-> v20 ; x5 !hr-> v19 ; x6 !hr-> v18 ; x7 !hr-> v17 ; x8 !hr-> v16 ; x9 !hr-> v15 ; 
   x10 !hr-> v14 ; x11 !hr-> v13 ; x12 !hr-> v12 ; x13 !hr-> v11 ; x14 !hr-> v10 ; x15 !hr-> v9 ; x16 !hr-> v8 ; x17 !hr-> v7 ; 
   x18 !hr-> v6 ; x19 !hr-> v5 ; x20 !hr-> v4 ; x21 !hr-> v3  ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_21 : forall heapR x  x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 
                                   v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v23,
  (x !hr-> v23 ;  x3 !hr-> v21 ; x4 !hr-> v20 ; x5 !hr-> v19 ; x6 !hr-> v18 ; x7 !hr-> v17 ; x8 !hr-> v16 ; x9 !hr-> v15 ; 
   x10 !hr-> v14 ; x11 !hr-> v13 ; x12 !hr-> v12 ; x13 !hr-> v11 ; x14 !hr-> v10 ; x15 !hr-> v9 ; x16 !hr-> v8 ; x17 !hr-> v7 ; 
   x18 !hr-> v6 ; x19 !hr-> v5 ; x20 !hr-> v4 ; x21 !hr-> v3 ; x !hr-> v1 ; heapR) 
= (x !hr-> v23 ;  x3 !hr-> v21 ; x4 !hr-> v20 ; x5 !hr-> v19 ; x6 !hr-> v18 ; x7 !hr-> v17 ; x8 !hr-> v16 ; x9 !hr-> v15 ; 
   x10 !hr-> v14 ; x11 !hr-> v13 ; x12 !hr-> v12 ; x13 !hr-> v11 ; x14 !hr-> v10 ; x15 !hr-> v9 ; x16 !hr-> v8 ; x17 !hr-> v7 ; 
   x18 !hr-> v6 ; x19 !hr-> v5 ; x20 !hr-> v4 ; x21 !hr-> v3  ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_22 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 
                                   v1 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23,
  (x !hr-> v23 ; x2 !hr-> v22 ; x3 !hr-> v21 ; x4 !hr-> v20 ; x5 !hr-> v19 ; x6 !hr-> v18 ; x7 !hr-> v17 ; x8 !hr-> v16 ; x9 !hr-> v15 ; 
   x10 !hr-> v14 ; x11 !hr-> v13 ; x12 !hr-> v12 ; x13 !hr-> v11 ; x14 !hr-> v10 ; x15 !hr-> v9 ; x16 !hr-> v8 ; x17 !hr-> v7 ; 
   x18 !hr-> v6 ; x19 !hr-> v5 ; x20 !hr-> v4 ; x21 !hr-> v3 ; x !hr-> v1 ; heapR) 
= (x !hr-> v23 ; x2 !hr-> v22 ; x3 !hr-> v21 ; x4 !hr-> v20 ; x5 !hr-> v19 ; x6 !hr-> v18 ; x7 !hr-> v17 ; x8 !hr-> v16 ; x9 !hr-> v15 ; 
   x10 !hr-> v14 ; x11 !hr-> v13 ; x12 !hr-> v12 ; x13 !hr-> v11 ; x14 !hr-> v10 ; x15 !hr-> v9 ; x16 !hr-> v8 ; x17 !hr-> v7 ; 
   x18 !hr-> v6 ; x19 !hr-> v5 ; x20 !hr-> v4 ; x21 !hr-> v3  ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_23 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23,
  (x !hr-> v23 ; x2 !hr-> v22 ; x3 !hr-> v21 ; x4 !hr-> v20 ; x5 !hr-> v19 ; x6 !hr-> v18 ; x7 !hr-> v17 ; x8 !hr-> v16 ; x9 !hr-> v15 ; 
   x10 !hr-> v14 ; x11 !hr-> v13 ; x12 !hr-> v12 ; x13 !hr-> v11 ; x14 !hr-> v10 ; x15 !hr-> v9 ; x16 !hr-> v8 ; x17 !hr-> v7 ; 
   x18 !hr-> v6 ; x19 !hr-> v5 ; x20 !hr-> v4 ; x21 !hr-> v3 ; x22 !hr-> v2 ; x !hr-> v1 ; heapR) 
= (x !hr-> v23 ; x2 !hr-> v22 ; x3 !hr-> v21 ; x4 !hr-> v20 ; x5 !hr-> v19 ; x6 !hr-> v18 ; x7 !hr-> v17 ; x8 !hr-> v16 ; x9 !hr-> v15 ; 
   x10 !hr-> v14 ; x11 !hr-> v13 ; x12 !hr-> v12 ; x13 !hr-> v11 ; x14 !hr-> v10 ; x15 !hr-> v9 ; x16 !hr-> v8 ; x17 !hr-> v7 ; 
   x18 !hr-> v6 ; x19 !hr-> v5 ; x20 !hr-> v4 ; x21 !hr-> v3 ; x22 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_27 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27,
  (x !hr-> v27 ; x2 !hr-> v26 ; x3 !hr-> v25 ; x4 !hr-> v24 ; x5 !hr-> v23 ; x6 !hr-> v22 ; x7 !hr-> v21 ; x8 !hr-> v20 ; x9 !hr-> v19 ; 
   x10 !hr-> v18 ; x11 !hr-> v17 ; x12 !hr-> v16 ; x13 !hr-> v15 ; x14 !hr-> v14 ; x15 !hr-> v13 ; x16 !hr-> v12 ; x17 !hr-> v11 ; 
   x18 !hr-> v10 ; x19 !hr-> v9 ; x20 !hr-> v8 ; x21 !hr-> v7 ; x22 !hr-> v6 ; x23 !hr-> v5 ; x24 !hr-> v4 ; x25 !hr-> v3 ; x26 !hr-> v2 ; x !hr-> v1 ; heapR) 
= (x !hr-> v27 ; x2 !hr-> v26 ; x3 !hr-> v25 ; x4 !hr-> v24 ; x5 !hr-> v23 ; x6 !hr-> v22 ; x7 !hr-> v21 ; x8 !hr-> v20 ; x9 !hr-> v19 ; 
   x10 !hr-> v18 ; x11 !hr-> v17 ; x12 !hr-> v16 ; x13 !hr-> v15 ; x14 !hr-> v14 ; x15 !hr-> v13 ; x16 !hr-> v12 ; x17 !hr-> v11 ; 
   x18 !hr-> v10 ; x19 !hr-> v9 ; x20 !hr-> v8 ; x21 !hr-> v7 ; x22 !hr-> v6 ; x23 !hr-> v5 ; x24 !hr-> v4 ; x25 !hr-> v3 ; x26 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_28 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28,
  (x !hr-> v27 ; x27 !hr-> v28 ; x2 !hr-> v26 ; x3 !hr-> v25 ; x4 !hr-> v24 ; x5 !hr-> v23 ; x6 !hr-> v22 ; x7 !hr-> v21 ; x8 !hr-> v20 ; x9 !hr-> v19 ; 
   x10 !hr-> v18 ; x11 !hr-> v17 ; x12 !hr-> v16 ; x13 !hr-> v15 ; x14 !hr-> v14 ; x15 !hr-> v13 ; x16 !hr-> v12 ; x17 !hr-> v11 ; 
   x18 !hr-> v10 ; x19 !hr-> v9 ; x20 !hr-> v8 ; x21 !hr-> v7 ; x22 !hr-> v6 ; x23 !hr-> v5 ; x24 !hr-> v4 ; x25 !hr-> v3 ; x26 !hr-> v2 ; x !hr-> v1 ; heapR) 
= (x !hr-> v27 ; x27 !hr-> v28 ; x2 !hr-> v26 ; x3 !hr-> v25 ; x4 !hr-> v24 ; x5 !hr-> v23 ; x6 !hr-> v22 ; x7 !hr-> v21 ; x8 !hr-> v20 ; x9 !hr-> v19 ; 
   x10 !hr-> v18 ; x11 !hr-> v17 ; x12 !hr-> v16 ; x13 !hr-> v15 ; x14 !hr-> v14 ; x15 !hr-> v13 ; x16 !hr-> v12 ; x17 !hr-> v11 ; 
   x18 !hr-> v10 ; x19 !hr-> v9 ; x20 !hr-> v8 ; x21 !hr-> v7 ; x22 !hr-> v6 ; x23 !hr-> v5 ; x24 !hr-> v4 ; x25 !hr-> v3 ; x26 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_29 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29,
  (x !hr-> v27 ; x27 !hr-> v28 ; x2 !hr-> v26 ; x3 !hr-> v25 ; x4 !hr-> v24 ; x5 !hr-> v23 ; x6 !hr-> v22 ; x7 !hr-> v21 ; x8 !hr-> v20 ; x9 !hr-> v19 ; 
   x10 !hr-> v18 ; x11 !hr-> v17 ; x12 !hr-> v16 ; x13 !hr-> v15 ; x14 !hr-> v14 ; x15 !hr-> v13 ; x16 !hr-> v12 ; x17 !hr-> v11 ; x28 !hr-> v29 ; 
   x18 !hr-> v10 ; x19 !hr-> v9 ; x20 !hr-> v8 ; x21 !hr-> v7 ; x22 !hr-> v6 ; x23 !hr-> v5 ; x24 !hr-> v4 ; x25 !hr-> v3 ; x26 !hr-> v2 ; x !hr-> v1 ; heapR) 
= (x !hr-> v27 ; x27 !hr-> v28 ; x2 !hr-> v26 ; x3 !hr-> v25 ; x4 !hr-> v24 ; x5 !hr-> v23 ; x6 !hr-> v22 ; x7 !hr-> v21 ; x8 !hr-> v20 ; x9 !hr-> v19 ; 
   x10 !hr-> v18 ; x11 !hr-> v17 ; x12 !hr-> v16 ; x13 !hr-> v15 ; x14 !hr-> v14 ; x15 !hr-> v13 ; x16 !hr-> v12 ; x17 !hr-> v11 ; x28 !hr-> v29 ;
   x18 !hr-> v10 ; x19 !hr-> v9 ; x20 !hr-> v8 ; x21 !hr-> v7 ; x22 !hr-> v6 ; x23 !hr-> v5 ; x24 !hr-> v4 ; x25 !hr-> v3 ; x26 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_31 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31,
  (x !hr-> v31 ; x2 !hr-> v30 ; x3 !hr-> v29 ; x4 !hr-> v28 ; x5 !hr-> v27 ; x6 !hr-> v26 ; x7 !hr-> v25 ; x8 !hr-> v24 ; x9 !hr-> v23 ; x10 !hr-> v22 ; 
   x11 !hr-> v21 ; x12 !hr-> v20 ; x13 !hr-> v19 ; x14 !hr-> v18 ; x15 !hr-> v17 ; x16 !hr-> v16 ; x17 !hr-> v15 ; x18 !hr-> v14 ; x19 !hr-> v13 ; x20 !hr-> v12 ; 
   x21 !hr-> v11 ; x22 !hr-> v10 ; x23 !hr-> v9 ; x24 !hr-> v8 ; x25 !hr-> v7 ; x26 !hr-> v6 ; x27 !hr-> v5 ; x28 !hr-> v4 ; x29 !hr-> v3 ; x30 !hr-> v2 ; x !hr-> v1 ; heapR) 
= (x !hr-> v31 ; x2 !hr-> v30 ; x3 !hr-> v29 ; x4 !hr-> v28 ; x5 !hr-> v27 ; x6 !hr-> v26 ; x7 !hr-> v25 ; x8 !hr-> v24 ; x9 !hr-> v23 ; x10 !hr-> v22 ; 
   x11 !hr-> v21 ; x12 !hr-> v20 ; x13 !hr-> v19 ; x14 !hr-> v18 ; x15 !hr-> v17 ; x16 !hr-> v16 ; x17 !hr-> v15 ; x18 !hr-> v14 ; x19 !hr-> v13 ; x20 !hr-> v12 ; 
   x21 !hr-> v11 ; x22 !hr-> v10 ; x23 !hr-> v9 ; x24 !hr-> v8 ; x25 !hr-> v7 ; x26 !hr-> v6 ; x27 !hr-> v5 ; x28 !hr-> v4 ; x29 !hr-> v3 ; x30 !hr-> v2 ; heapR) .
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_35 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34  
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 ,
  (x !hr-> v35 ; x2 !hr-> v34 ; x3 !hr-> v33 ; x4 !hr-> v32 ; x5 !hr-> v31 ; x6 !hr-> v30 ; x7 !hr-> v29 ; x8 !hr-> v28 ; x9 !hr-> v27 ;  x10 !hr-> v26 ; x11 !hr-> v25 ; x12 !hr-> v24 ;
   x13 !hr-> v23 ; x14 !hr-> v22 ; x15 !hr-> v21 ; x16 !hr-> v20 ; x17 !hr-> v19 ; x18 !hr-> v18 ; x19 !hr-> v17 ; x20 !hr-> v16 ; x21 !hr-> v15 ; x22 !hr-> v14 ; x23 !hr-> v13 ; 
   x24 !hr-> v12 ; x25 !hr-> v11 ; x26 !hr-> v10 ; x27 !hr-> v9 ; x28 !hr-> v8 ; x29 !hr-> v7 ; x30 !hr-> v6 ; x31 !hr-> v5 ; x32 !hr-> v4 ; x33 !hr-> v3 ; x34 !hr-> v2 ; x !hr-> v1 ; heapR)
= (x !hr-> v35 ; x2 !hr-> v34 ; x3 !hr-> v33 ; x4 !hr-> v32 ; x5 !hr-> v31 ; x6 !hr-> v30 ; x7 !hr-> v29 ; x8 !hr-> v28 ; x9 !hr-> v27 ;  x10 !hr-> v26 ; x11 !hr-> v25 ; x12 !hr-> v24 ;
   x13 !hr-> v23 ; x14 !hr-> v22 ; x15 !hr-> v21 ; x16 !hr-> v20 ; x17 !hr-> v19 ; x18 !hr-> v18 ; x19 !hr-> v17 ; x20 !hr-> v16 ; x21 !hr-> v15 ; x22 !hr-> v14 ; x23 !hr-> v13 ; 
   x24 !hr-> v12 ; x25 !hr-> v11 ; x26 !hr-> v10 ; x27 !hr-> v9 ; x28 !hr-> v8 ; x29 !hr-> v7 ; x30 !hr-> v6 ; x31 !hr-> v5 ; x32 !hr-> v4 ; x33 !hr-> v3 ; x34 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_36 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36,
  (x !hr-> v36 ; x2 !hr-> v35 ; x3 !hr-> v34 ; x4 !hr-> v33 ; x5 !hr-> v32 ; x6 !hr-> v31 ; x7 !hr-> v30 ; x8 !hr-> v29 ; x9 !hr-> v28 ; x10 !hr-> v27 ;  x11 !hr-> v26 ; x12 !hr-> v25 ; 
   x13 !hr-> v24 ; x14 !hr-> v23 ; x15 !hr-> v22 ; x16 !hr-> v21 ; x17 !hr-> v20 ; x18 !hr-> v19 ; x19 !hr-> v18 ; x20 !hr-> v17 ; x21 !hr-> v16 ; x22 !hr-> v15 ; x23 !hr-> v14 ; x24 !hr-> v13 ; 
   x25 !hr-> v12 ; x26 !hr-> v11 ; x27 !hr-> v10 ; x28 !hr-> v9 ; x29 !hr-> v8 ; x30 !hr-> v7 ; x31 !hr-> v6 ; x32 !hr-> v5 ; x33 !hr-> v4 ; x34 !hr-> v3 ; x35 !hr-> v2 ; x !hr-> v1 ; heapR)
= (x !hr-> v36 ; x2 !hr-> v35 ; x3 !hr-> v34 ; x4 !hr-> v33 ; x5 !hr-> v32 ; x6 !hr-> v31 ; x7 !hr-> v30 ; x8 !hr-> v29 ; x9 !hr-> v28 ; x10 !hr-> v27 ;  x11 !hr-> v26 ; x12 !hr-> v25 ; 
   x13 !hr-> v24 ; x14 !hr-> v23 ; x15 !hr-> v22 ; x16 !hr-> v21 ; x17 !hr-> v20 ; x18 !hr-> v19 ; x19 !hr-> v18 ; x20 !hr-> v17 ; x21 !hr-> v16 ; x22 !hr-> v15 ; x23 !hr-> v14 ; x24 !hr-> v13 ; 
   x25 !hr-> v12 ; x26 !hr-> v11 ; x27 !hr-> v10 ; x28 !hr-> v9 ; x29 !hr-> v8 ; x30 !hr-> v7 ; x31 !hr-> v6 ; x32 !hr-> v5 ; x33 !hr-> v4 ; x34 !hr-> v3 ; x35 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_37 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37,
  (x !hr-> v36 ; x2 !hr-> v35 ; x3 !hr-> v34 ; x4 !hr-> v33 ; x5 !hr-> v32 ; x6 !hr-> v31 ; x7 !hr-> v30 ; x8 !hr-> v29 ; x9 !hr-> v28 ; x10 !hr-> v27 ;  x11 !hr-> v26 ; x12 !hr-> v25 ; 
   x13 !hr-> v24 ; x14 !hr-> v23 ; x15 !hr-> v22 ; x16 !hr-> v21 ; x17 !hr-> v20 ; x18 !hr-> v19 ; x19 !hr-> v18 ; x20 !hr-> v17 ; x21 !hr-> v16 ; x22 !hr-> v15 ; x23 !hr-> v14 ; x24 !hr-> v13 ; 
   x25 !hr-> v12 ; x26 !hr-> v11 ; x27 !hr-> v10 ; x28 !hr-> v9 ; x29 !hr-> v8 ; x30 !hr-> v7 ; x31 !hr-> v6 ; x32 !hr-> v5 ; x33 !hr-> v4 ; x34 !hr-> v3 ; x35 !hr-> v2 ; x36 !hr-> v37 ; x !hr-> v1 ; heapR)
= (x !hr-> v36 ; x2 !hr-> v35 ; x3 !hr-> v34 ; x4 !hr-> v33 ; x5 !hr-> v32 ; x6 !hr-> v31 ; x7 !hr-> v30 ; x8 !hr-> v29 ; x9 !hr-> v28 ; x10 !hr-> v27 ;  x11 !hr-> v26 ; x12 !hr-> v25 ; 
   x13 !hr-> v24 ; x14 !hr-> v23 ; x15 !hr-> v22 ; x16 !hr-> v21 ; x17 !hr-> v20 ; x18 !hr-> v19 ; x19 !hr-> v18 ; x20 !hr-> v17 ; x21 !hr-> v16 ; x22 !hr-> v15 ; x23 !hr-> v14 ; x24 !hr-> v13 ; 
   x25 !hr-> v12 ; x26 !hr-> v11 ; x27 !hr-> v10 ; x28 !hr-> v9 ; x29 !hr-> v8 ; x30 !hr-> v7 ; x31 !hr-> v6 ; x32 !hr-> v5 ; x33 !hr-> v4 ; x34 !hr-> v3 ; x35 !hr-> v2 ; x36 !hr-> v37 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_40 : forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40,
  (x !hr-> v40 ; x2 !hr-> v39 ; x3 !hr-> v38 ; x4 !hr-> v37 ; x5 !hr-> v36 ; x6 !hr-> v35 ; x7 !hr-> v34 ; x8 !hr-> v33 ; x9 !hr-> v32 ; x10 !hr-> v31 ; x11 !hr-> v30 ; x12 !hr-> v29 ; x13 !hr-> v28 ; 
   x14 !hr-> v27 ; x15 !hr-> v26 ; x16 !hr-> v25 ; x17 !hr-> v24 ; x18 !hr-> v23 ; x19 !hr-> v22 ; x20 !hr-> v21 ; x21 !hr-> v20 ; x22 !hr-> v19 ; x23 !hr-> v18 ; x24 !hr-> v17 ; x25 !hr-> v16 ; x26 !hr-> v15 ; 
   x27 !hr-> v14 ; x28 !hr-> v13 ; x29 !hr-> v12 ; x30 !hr-> v11 ; x31 !hr-> v10 ; x32 !hr-> v9 ; x33 !hr-> v8 ; x34 !hr-> v7 ; x35 !hr-> v6 ; x36 !hr-> v5 ; x37 !hr-> v4 ; x38 !hr-> v3 ; x39 !hr-> v2 ; x !hr-> v1 ; heapR)
= (x !hr-> v40 ; x2 !hr-> v39 ; x3 !hr-> v38 ; x4 !hr-> v37 ; x5 !hr-> v36 ; x6 !hr-> v35 ; x7 !hr-> v34 ; x8 !hr-> v33 ; x9 !hr-> v32 ; x10 !hr-> v31 ; x11 !hr-> v30 ; x12 !hr-> v29 ; x13 !hr-> v28 ; 
   x14 !hr-> v27 ; x15 !hr-> v26 ; x16 !hr-> v25 ; x17 !hr-> v24 ; x18 !hr-> v23 ; x19 !hr-> v22 ; x20 !hr-> v21 ; x21 !hr-> v20 ; x22 !hr-> v19 ; x23 !hr-> v18 ; x24 !hr-> v17 ; x25 !hr-> v16 ; x26 !hr-> v15 ; 
   x27 !hr-> v14 ; x28 !hr-> v13 ; x29 !hr-> v12 ; x30 !hr-> v11 ; x31 !hr-> v10 ; x32 !hr-> v9 ; x33 !hr-> v8 ; x34 !hr-> v7 ; x35 !hr-> v6 ; x36 !hr-> v5 ; x37 !hr-> v4 ; x38 !hr-> v3 ; x39 !hr-> v2 ; heapR).
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold hR_update.
  destruct (Nat.eqb x x0) eqn:H.
  trivial. trivial.
Qed.

Lemma hR_update_shadow_47: forall heapR x x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 x32 x33 x34 x35 x36 x37 x38 x39 x40 x41 x42 x43 x44 x45 x46
                                   v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47,
  (x !hr-> v40 ; x40 !hr-> v41 ; x41 !hr-> v42 ; x42 !hr-> v43 ; x43 !hr-> v44 ; x44 !hr-> v45 ; x45 !hr-> v46 ; x46 !hr-> v47 ;
   x2 !hr-> v39 ; x3 !hr-> v38 ; x4 !hr-> v37 ; x5 !hr-> v36 ; x6 !hr-> v35 ; x7 !hr-> v34 ; x8 !hr-> v33 ; x9 !hr-> v32 ; x10 !hr-> v31 ; x11 !hr-> v30 ; x12 !hr-> v29 ; x13 !hr-> v28 ; 
   x14 !hr-> v27 ; x15 !hr-> v26 ; x16 !hr-> v25 ; x17 !hr-> v24 ; x18 !hr-> v23 ; x19 !hr-> v22 ; x20 !hr-> v21 ; x21 !hr-> v20 ; x22 !hr-> v19 ; x23 !hr-> v18 ; x24 !hr-> v17 ; x25 !hr-> v16 ; x26 !hr-> v15 ; 
   x27 !hr-> v14 ; x28 !hr-> v13 ; x29 !hr-> v12 ; x30 !hr-> v11 ; x31 !hr-> v10 ; x32 !hr-> v9 ; x33 !hr-> v8 ; x34 !hr-> v7 ; x35 !hr-> v6 ; x36 !hr-> v5 ; x37 !hr-> v4 ; x38 !hr-> v3 ; x39 !hr-> v2 ; x !hr-> v1 ; heapR)
= (x !hr-> v40 ; x40 !hr-> v41 ; x41 !hr-> v42 ; x42 !hr-> v43 ; x43 !hr-> v44 ; x44 !hr-> v45 ; x45 !hr-> v46 ; x46 !hr-> v47 ;
   x2 !hr-> v39 ; x3 !hr-> v38 ; x4 !hr-> v37 ; x5 !hr-> v36 ; x6 !hr-> v35 ; x7 !hr-> v34 ; x8 !hr-> v33 ; x9 !hr-> v32 ; x10 !hr-> v31 ; x11 !hr-> v30 ; x12 !hr-> v29 ; x13 !hr-> v28 ; 
   x14 !hr-> v27 ; x15 !hr-> v26 ; x16 !hr-> v25 ; x17 !hr-> v24 ; x18 !hr-> v23 ; x19 !hr-> v22 ; x20 !hr-> v21 ; x21 !hr-> v20 ; x22 !hr-> v19 ; x23 !hr-> v18 ; x24 !hr-> v17 ; x25 !hr-> v16 ; x26 !hr-> v15 ; 
   x27 !hr-> v14 ; x28 !hr-> v13 ; x29 !hr-> v12 ; x30 !hr-> v11 ; x31 !hr-> v10 ; x32 !hr-> v9 ; x33 !hr-> v8 ; x34 !hr-> v7 ; x35 !hr-> v6 ; x36 !hr-> v5 ; x37 !hr-> v4 ; x38 !hr-> v3 ; x39 !hr-> v2 ; heapR).
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


