Require Import Aid.
Require Import semantic.
Require Import function.
Require Import state.
Require Import Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Import ListNotations.

Lemma InHo : forall n1 l,
  in_list [n1] l = true -> 
  n1 <> 0  -> 
  l = n1.
Proof.
  intros n1 l Hin Hn1.
  destruct (l =? n1) eqn:L1.
  - (* Case: l = n1 *)
    apply beq_eq in L1.
    rewrite L1.
    reflexivity.
  - (* Case: l <> n1 *)
    unfold in_list in Hin.
    destruct (n1 =? l) eqn:Hin'.
    + apply beq_eq in Hin'.
      rewrite Hin'.
      reflexivity.
    + apply Nat.eqb_neq in Hin'.
      exfalso.
      congruence.
Qed.

Lemma InHo1 : forall n1 n2 l,
  in_list [n1;n2] l = true -> 
n1 <> 0 -> n2 <> 0 -> 
l = n1 \/ l = n2.
Proof.
  intros.
    destruct (l =? n1) eqn : L1.
    apply beq_eq in L1.
    rewrite L1.
    left. auto.
    destruct (l =? n2) eqn : L2.
    apply beq_eq in L2.
    rewrite L2.
    right. auto. 
    rewrite beq_neq in L1. rewrite neq_comm in L1. rewrite <- beq_neq in L1.
    rewrite beq_neq in L2. rewrite neq_comm in L2. rewrite <- beq_neq in L2.
    unfold in_list in H.
    rewrite L1 in H. rewrite L2 in H.
    discriminate.
Qed.

Lemma InHo2 : forall n1 n2 n3 l,
  in_list [n1;n2;n3] l = true ->
  n1 <> 0 -> n2 <> 0 -> n3 <> 0 ->
  l = n1 \/ l = n2 \/ l = n3.
Proof.
  intros.
  destruct (l =? n1) eqn: L1.
  - apply beq_eq in L1. rewrite L1. left. auto.
  - destruct (l =? n2) eqn: L2.
    + apply beq_eq in L2. rewrite L2. right. left. auto.
    + destruct (l =? n3) eqn: L3.
      * apply beq_eq in L3. rewrite L3. right. right. auto.
      * rewrite beq_neq in L1, L2, L3.
        rewrite neq_comm in L1, L2, L3.
        rewrite <- beq_neq in L1, L2, L3.
        unfold in_list in H.
        rewrite L1, L2, L3 in H.
        discriminate.
Qed.

Lemma InHo3 : forall n1 n2 n3 n4 l,
  in_list [n1; n2; n3; n4] l = true ->
  n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 ->
  l = n1 \/ l = n2 \/ l = n3 \/ l = n4.

Proof.
intros.
destruct (l =? n1) eqn: L1.
- apply Nat.eqb_eq in L1. rewrite L1. left. auto.
- destruct (l =? n2) eqn: L2.
  + apply Nat.eqb_eq in L2. rewrite L2. right. left. auto.
  + destruct (l =? n3) eqn: L3.
    * apply Nat.eqb_eq in L3. rewrite L3. right. right. auto.
    * destruct (l =? n4) eqn: L4.
      -- apply Nat.eqb_eq in L4. rewrite L4. right. right. right. auto.
      -- unfold in_list in H.
         rewrite beq_neq in L1, L2, L3, L4.
         rewrite neq_comm in L1, L2, L3, L4.
         rewrite <- beq_neq in L1, L2, L3, L4.
         rewrite L1, L2, L3, L4 in H.
         discriminate.
Qed.

Lemma InHo4 : forall n1 n2 n3 n4 n5 l,
  in_list [n1; n2; n3; n4; n5] l = true ->
  n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 ->
  l = n1 \/ l = n2 \/ l = n3 \/ l = n4 \/ l = n5.
Proof.
intros n1 n2 n3 n4 n5 l Hinl Hn1 Hn2 Hn3 Hn4 Hn5.
destruct (l =? n1) eqn: L1.
- apply Nat.eqb_eq in L1. rewrite L1. left. auto.
- destruct (l =? n2) eqn: L2.
  + apply Nat.eqb_eq in L2. rewrite L2. right. left. auto.
  + destruct (l =? n3) eqn: L3.
    * apply Nat.eqb_eq in L3. rewrite L3. right. right. left. auto.
    * destruct (l =? n4) eqn: L4.
      -- apply Nat.eqb_eq in L4. rewrite L4. right. right. right. left. auto.
      -- destruct (l =? n5) eqn: L5.
         ++ apply Nat.eqb_eq in L5. rewrite L5. right. right. right. right. auto.
         ++ unfold in_list in Hinl.
            rewrite beq_neq in L1, L2, L3, L4, L5.
            rewrite neq_comm in L1, L2, L3, L4, L5.
            rewrite <- beq_neq in L1, L2, L3, L4, L5.
            rewrite L1, L2, L3, L4, L5 in Hinl.
            discriminate.
Qed.

Lemma InHo5 : forall n1 n2 n3 n4 n5 n6 l,
  in_list [n1; n2; n3; n4; n5; n6] l = true ->
  n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 ->
  l = n1 \/ l = n2 \/ l = n3 \/ l = n4 \/ l = n5 \/ l = n6.
Proof.
intros n1 n2 n3 n4 n5 n6 l Hinl Hn1 Hn2 Hn3 Hn4 Hn5 Hn6.
destruct (l =? n1) eqn: L1.
- apply Nat.eqb_eq in L1. rewrite L1. left. auto.
- destruct (l =? n2) eqn: L2.
  + apply Nat.eqb_eq in L2. rewrite L2. right. left. auto.
  + destruct (l =? n3) eqn: L3.
    * apply Nat.eqb_eq in L3. rewrite L3. right. right. left. auto.
    * destruct (l =? n4) eqn: L4.
      -- apply Nat.eqb_eq in L4. rewrite L4. right. right. right. left. auto.
      -- destruct (l =? n5) eqn: L5.
         ++ apply Nat.eqb_eq in L5. rewrite L5. right. right. right. right. left. auto.
         ++ destruct (l =? n6) eqn: L6.
            ** apply Nat.eqb_eq in L6. rewrite L6. right. right. right. right. right. auto.
            ** unfold in_list in Hinl.
               rewrite beq_neq in L1, L2, L3, L4, L5, L6.
               rewrite neq_comm in L1, L2, L3, L4, L5, L6.
               rewrite <- beq_neq in L1, L2, L3, L4, L5, L6.
               rewrite L1, L2, L3, L4, L5, L6 in Hinl.
               discriminate.
Qed.

Lemma InHo6 : forall n1 n2 n3 n4 n5 n6 n7 l,
  in_list [n1; n2; n3; n4; n5; n6; n7] l = true ->
  n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 ->
  l = n1 \/ l = n2 \/ l = n3 \/ l = n4 \/ l = n5 \/ l = n6 \/ l = n7.
Proof.
intros n1 n2 n3 n4 n5 n6 n7 l Hinl Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7.
destruct (l =? n1) eqn: L1.
- apply Nat.eqb_eq in L1. rewrite L1. left. auto.
- destruct (l =? n2) eqn: L2.
  + apply Nat.eqb_eq in L2. rewrite L2. right. left. auto.
  + destruct (l =? n3) eqn: L3.
    * apply Nat.eqb_eq in L3. rewrite L3. right. right. left. auto.
    * destruct (l =? n4) eqn: L4.
      -- apply Nat.eqb_eq in L4. rewrite L4. right. right. right. left. auto.
      -- destruct (l =? n5) eqn: L5.
         ++ apply Nat.eqb_eq in L5. rewrite L5. right. right. right. right. left. auto.
         ++ destruct (l =? n6) eqn: L6.
            ** apply Nat.eqb_eq in L6. rewrite L6. right. right. right. right. right. left. auto.
            ** destruct (l =? n7) eqn: L7.
               --- apply Nat.eqb_eq in L7. rewrite L7. right. right. right. right. right. right. auto.
               --- unfold in_list in Hinl.
                  rewrite beq_neq in L1, L2, L3, L4, L5, L6, L7.
                  rewrite neq_comm in L1, L2, L3, L4, L5, L6, L7.
                  rewrite <- beq_neq in L1, L2, L3, L4, L5, L6, L7.
                  rewrite L1, L2, L3, L4, L5, L6, L7 in Hinl.
                  discriminate.
Qed.

Lemma InHo7 : forall n1 n2 n3 n4 n5 n6 n7 n8 l,
  in_list [n1; n2; n3; n4; n5; n6; n7; n8] l = true ->
  n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 ->
  l = n1 \/ l = n2 \/ l = n3 \/ l = n4 \/ l = n5 \/ l = n6 \/ l = n7 \/ l = n8.
Proof.
intros n1 n2 n3 n4 n5 n6 n7 n8 l Hinl Hn1 Hn2 Hn3 Hn4 Hn5 Hn6 Hn7 Hn8.
destruct (l =? n1) eqn: L1.
- apply Nat.eqb_eq in L1. rewrite L1. left. auto.
- destruct (l =? n2) eqn: L2.
  + apply Nat.eqb_eq in L2. rewrite L2. right. left. auto.
  + destruct (l =? n3) eqn: L3.
    * apply Nat.eqb_eq in L3. rewrite L3. right. right. left. auto.
    * destruct (l =? n4) eqn: L4.
      -- apply Nat.eqb_eq in L4. rewrite L4. right. right. right. left. auto.
      -- destruct (l =? n5) eqn: L5.
         ++ apply Nat.eqb_eq in L5. rewrite L5. right. right. right. right. left. auto.
         ++ destruct (l =? n6) eqn: L6.
            ** apply Nat.eqb_eq in L6. rewrite L6. right. right. right. right. right. left. auto.
            ** destruct (l =? n7) eqn: L7.
               --- apply Nat.eqb_eq in L7. rewrite L7. right. right. right. right. right. right. left. auto.
               --- destruct (l =? n8) eqn: L8.
                   +++ apply Nat.eqb_eq in L8. rewrite L8. right. right. right. right. right. right. right. auto.
                   +++ unfold in_list in Hinl.
                       rewrite beq_neq in L1, L2, L3, L4, L5, L6, L7, L8.
                       rewrite neq_comm in L1, L2, L3, L4, L5, L6, L7, L8.
                       rewrite <- beq_neq in L1, L2, L3, L4, L5, L6, L7, L8.
                       rewrite L1, L2, L3, L4, L5, L6, L7, L8 in Hinl.
                       discriminate.
Qed. 

Lemma SafeinHo1_2 : forall (l1 l2 : list (option nat)) l n1 n2  (HeapO: heapO),
in_list [n1] l = true ->
n1 <> 0 -> n2 <> 0 -> 
n1 <> n2 -> 
exists k , (n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo in H.
  rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. 
Qed.

Lemma SafeinHo1_3 : forall (l1 l2 l3: list (option nat)) l n1 n2 n3 (HeapO: heapO),
in_list [n1] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> 
n1 <> n2 -> n1 <> n3 ->
n2 <> n3 ->
exists k , (n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo in H.
  rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. 
Qed.

Lemma SafeinHo1in3 : forall (l1 l2 l3: list (option nat)) l n1 n2 n3 (HeapO: heapO),
in_list [n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> 
n1 <> n2 -> n1 <> n3 ->
n2 <> n3 ->
exists k , (n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo in H.
  rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. 
Qed.

Lemma SafeinHo1_4 : forall (l1 l2 l3 l4: list (option nat)) l n1 n2 n3 n4,
in_list [n1] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> 
n2 <> n3 -> n2 <> n4 -> 
n3 <> n4 -> 
exists k , (n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; emp_heapO) l = k.
Proof.
  intros.
  apply InHo in H.
  rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto.
Qed.

Lemma SafeinHo1_5 : forall (l1 l2 l3 l4 l5 : list (option nat)) l n1 n2 n3 n4 n5 ,
in_list [n1] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n1 <> n5 ->
n2 <> n3 -> n2 <> n4 -> n2 <> n5 ->
n3 <> n4 -> n3 <> n5 -> 
n4 <> n5 ->  
exists k , (n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; emp_heapO) l = k.
Proof.
  intros.
  apply InHo in H.
  rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. 
Qed.

Lemma SafeinHo1_5_ : forall (l1 l2 l3 l4 l5 : list (option nat)) l n1 n2 n3 n4 n5 ,
in_list [n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n1 <> n5 ->
n2 <> n3 -> n2 <> n4 -> n2 <> n5 ->
n3 <> n4 -> n3 <> n5 -> 
n4 <> n5 ->  
exists k , (n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; emp_heapO) l = k.
Proof.
  intros.
  apply InHo in H.
  rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto.
Qed.


Lemma SafeinHo1_7 : forall (l1 l2 l3 l4 l5 l6 l7: list (option nat)) l n1 n2 n3 n4 n5 n6 n7,
in_list [n1] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> 
n2 <> n3 -> n2 <> n4 -> n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> 
n3 <> n4 -> n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> 
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> 
n5 <> n6 -> n5 <> n7 -> 
n6 <> n7 -> 
exists k , (n7 !ho-> l7;n6 !ho-> l6;n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; emp_heapO) l = k.
Proof.
  intros.
  apply InHo in H.
  rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto.
Qed.


Lemma SafeinHo2_3 : forall (l1 l2 l3: list (option nat)) l n1 n2 n3 (HeapO: heapO),
in_list [n1;n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n3 <> n2 ->
exists k , (n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo1 in H.
  destruct H; rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
Qed.

Lemma SafeinHo2_4 : forall (l1 l2 l3 l4: list (option nat)) l n1 n2 n3 n4,
in_list [n1;n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> 
n2 <> n3 -> n2 <> n4 -> 
n3 <> n4 -> 
exists k , (n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; emp_heapO) l = k.
Proof.
  intros.
  apply InHo1 in H.
  destruct H; rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto.
Qed.

Lemma SafeinHo2_4_ : forall (l1 l2 l3 l4: list (option nat)) l n1 n2 n3 n4,
in_list [n1;n3] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> 
n2 <> n3 -> n2 <> n4 -> 
n3 <> n4 -> 
exists k , (n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; emp_heapO) l = k.
Proof.
  intros.
  apply InHo1 in H.
  destruct H; rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
Qed.

Lemma SafeinHo2in4 : forall (l1 l2 l3 l4: list (option nat)) l n1 n2 n3 n4,
in_list [n2;n3] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> 
n2 <> n3 -> n2 <> n4 -> 
n3 <> n4 -> 
exists k , (n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; emp_heapO) l = k.
Proof.
  intros.
  apply InHo1 in H.
  destruct H; rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. 
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
Qed.

Lemma SafeinHo2_5 : forall (l1 l2 l3 l4 l5  : list (option nat)) l n1 n2 n3 n4 n5  ,
in_list [n1;n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n1 <> n5 -> 
n2 <> n3 -> n2 <> n4 -> n2 <> n5 ->
n3 <> n4 -> n3 <> n5 -> 
n4 <> n5 -> 

exists k , (n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; emp_heapO) l = k.
Proof.
  intros.
  apply InHo1 in H.
  destruct H; rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. 
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. 
Qed.

Lemma SafeinHo2_6 : forall (l1 l2 l3 l4 l5 l6 : list (option nat)) l n1 n2 n3 n4 n5 n6 ,
in_list [n1;n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n1 <> n5 -> n1 <> n6 -> 
n2 <> n3 -> n2 <> n4 -> n2 <> n5 -> n2 <> n6 -> 
n3 <> n4 -> n3 <> n5 -> n3 <> n6 -> 
n4 <> n5 -> n4 <> n6 ->  
n5 <> n6 -> 
exists k , (n6 !ho-> l6;n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; emp_heapO) l = k.
Proof.
  intros.
  apply InHo1 in H.
  destruct H; rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo2_6_ : forall (l1 l2 l3 l4 l5 l6 : list (option nat)) l n1 n2 n3 n4 n5 n6 ,
in_list [n2;n5] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n1 <> n5 -> n1 <> n6 -> 
n2 <> n3 -> n2 <> n4 -> n2 <> n5 -> n2 <> n6 -> 
n3 <> n4 -> n3 <> n5 -> n3 <> n6 -> 
n4 <> n5 -> n4 <> n6 ->  
n5 <> n6 -> 
exists k , (n6 !ho-> l6;n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; emp_heapO) l = k.
Proof.
  intros.
  apply InHo1 in H.
  destruct H; rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. 
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. 
Qed.

Lemma SafeinHo2in6 : forall (l1 l2 l3 l4 l5 l6 : list (option nat)) l n1 n2 n3 n4 n5 n6 ,
in_list [n1;n5] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n1 <> n5 -> n1 <> n6 -> 
n2 <> n3 -> n2 <> n4 -> n2 <> n5 -> n2 <> n6 -> 
n3 <> n4 -> n3 <> n5 -> n3 <> n6 -> 
n4 <> n5 -> n4 <> n6 ->  
n5 <> n6 -> 
exists k , (n6 !ho-> l6;n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; emp_heapO) l = k.
Proof.
  intros.
  apply InHo1 in H.
  destruct H; rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto.
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. 
Qed.

Lemma SafeinHo2_7 : forall (l1 l2 l3 l4 l5 l6 l7: list (option nat)) l n1 n2 n3 n4 n5 n6 n7,
in_list [n1;n2] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> 
n2 <> n3 -> n2 <> n4 -> n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> 
n3 <> n4 -> n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> 
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> 
n5 <> n6 -> n5 <> n7 -> 
n6 <> n7 -> 
exists k , (n7 !ho-> l7;n6 !ho-> l6;n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; emp_heapO) l = k.
Proof.
  intros.
  apply InHo1 in H.
  destruct H; rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo3_4 : forall (l1 l2 l3 l4: list (option nat)) l n1 n2 n3 n4 (HeapO: heapO),
in_list [n1;n2;n3] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 -> 
n2 <> n3 -> n2 <> n4 -> 
n3 <> n4 -> 
exists k , (n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo2 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto.
  rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. 
Qed.

Lemma SafeinHo3_5 : forall (l1 l2 l3 l4 l5 : list (option nat)) l n1 n2 n3 n4 n5  (HeapO: heapO),
in_list [n1;n2;n3] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> 
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> 
n3 <> n4 ->  n3 <> n5 -> 
n4 <> n5 -> 

exists k , ( n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo2 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
  rewrite H.
  exists (Some l3).
  rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. 
Qed.

Lemma SafeinHo3_6 : forall (l1 l2 l3 l4 l5 l6: list (option nat)) l n1 n2 n3 n4 n5 n6 (HeapO: heapO),
in_list [n1;n2;n3] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> 
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> 
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> 
n4 <> n5 -> n4 <> n6 -> 
n5 <> n6 -> 

exists k , ( n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo2 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto.  
  rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. 
Qed.

Lemma SafeinHo3_7 : forall (l1 l2 l3 l4 l5 l6 l7: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 (HeapO: heapO),
in_list [n1;n2;n3] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 ->
n5 <> n6 -> n5 <> n7 ->
n6 <> n7 -> 
exists k , ( n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo2 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. 
  rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. 
Qed.

Lemma SafeinHo3_7_ : forall (l1 l2 l3 l4 l5 l6 l7: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 (HeapO: heapO),
in_list [n2;n5;n6] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 ->
n5 <> n6 -> n5 <> n7 ->
n6 <> n7 -> 
exists k , ( n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo2 in H.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. 
  rewrite H.
  exists (Some l6).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. 
Qed.

Lemma SafeinHo3_10 : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 (HeapO: heapO),
in_list [n1;n2;n3] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 -> n1 <> n10 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 -> n2 <> n10 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 -> n3 <> n10 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 -> n4 <> n10 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 -> n5 <> n10 ->
n6 <> n7 -> n6 <> n8 -> n6 <> n9 -> n6 <> n10 ->
n7 <> n8 -> n7 <> n9 -> n7 <> n10 ->
n8 <> n9 -> n8 <> n10 ->
n9 <> n10 ->
exists k , ( n10 !ho-> l10; n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo2 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo3_10_ : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 (HeapO: heapO),
in_list [n1;n3;n4] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 -> n1 <> n10 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 -> n2 <> n10 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 -> n3 <> n10 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 -> n4 <> n10 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 -> n5 <> n10 ->
n6 <> n7 -> n6 <> n8 -> n6 <> n9 -> n6 <> n10 ->
n7 <> n8 -> n7 <> n9 -> n7 <> n10 ->
n8 <> n9 -> n8 <> n10 ->
n9 <> n10 ->
exists k , ( n10 !ho-> l10; n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo2 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. 
  rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo4_5 : forall (l1 l2 l3 l4 l5: list (option nat)) l n1 n2 n3 n4 n5 (HeapO: heapO),
in_list [n1;n2;n3;n4] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> 
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> 
n3 <> n4 ->  n3 <> n5 -> 
n4 <> n5 -> 
exists k , ( n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo3 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto.
  rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo4_8 : forall (l1 l2 l3 l4 l5 l6 l7 l8: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 (HeapO: heapO),
in_list [n1;n2;n3;n4] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 ->
n6 <> n7 -> n6 <> n8 ->
n7 <> n8 ->
exists k , ( n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo3 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto.
  rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo4_8_ : forall (l1 l2 l3 l4 l5 l6 l7 l8: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 (HeapO: heapO),
in_list [n2;n5;n6;n7] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 ->
n6 <> n7 -> n6 <> n8 ->
n7 <> n8 ->
exists k , ( n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo3 in H.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l6).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto.
  rewrite H.
  exists (Some l7).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo4in8 : forall (l1 l2 l3 l4 l5 l6 l7 l8: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 (HeapO: heapO),
in_list [n2;n3;n4;n7] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 ->
n6 <> n7 -> n6 <> n8 ->
n7 <> n8 ->
exists k , ( n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo3 in H.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto.
  rewrite H.
  exists (Some l7).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto.
Qed.


Lemma SafeinHo5_5 : forall (l1 l2 l3 l4 l5 : list (option nat)) l n1 n2 n3 n4 n5  (HeapO: heapO),
in_list [n1;n2;n3;n4;n5] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> 
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> 
n3 <> n4 ->  n3 <> n5 -> 
n4 <> n5 -> 

exists k , ( n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo4 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto.
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. 
  rewrite H.
  exists (Some l5).
  rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo5_6 : forall (l1 l2 l3 l4 l5 l6: list (option nat)) l n1 n2 n3 n4 n5 n6 (HeapO: heapO),
in_list [n1;n2;n3;n4;n5] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 ->
n4 <> n5 -> n4 <> n6 ->
n5 <> n6 ->
exists k , ( n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo4 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto.
  rewrite H.
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo5_7 : forall (l1 l2 l3 l4 l5 l6 l7: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 (HeapO: heapO),
in_list [n1;n2;n3;n4;n5] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> 
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> 
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> 
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> 
n5 <> n6 -> n5 <> n7 -> 
n6 <> n7 -> 
exists k , ( n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo4 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
  rewrite H.
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo4_7 : forall (l1 l2 l3 l4 l5 l6 l7 : list (option nat)) l n1 n2 n3 n4 n5 n6 n7 (HeapO: heapO),
in_list [n1;n2;n3;n4] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> 
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> 
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> 
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> 
n5 <> n6 -> n5 <> n7 -> 
n6 <> n7 -> 
exists k , ( n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo3 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. 
  rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. 
Qed.

Lemma SafeinHo4_11 : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 (HeapO: heapO),
in_list [n1;n2;n3;n4] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 -> n1 <> n10 -> n1 <> n11 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 -> n2 <> n10 -> n2 <> n11 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 -> n3 <> n10 -> n3 <> n11 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 -> n4 <> n10 -> n4 <> n11 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 -> n5 <> n10 -> n5 <> n11 ->
n6 <> n7 -> n6 <> n8 -> n6 <> n9 -> n6 <> n10 -> n6 <> n11 ->
n7 <> n8 -> n7 <> n9 -> n7 <> n10 -> n7 <> n11 ->
n8 <> n9 -> n8 <> n10 -> n8 <> n11 ->
n9 <> n10 -> n9 <> n11 ->
n10 <> n11 ->
exists k , ( n11 !ho-> l11; n10 !ho-> l10; n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo3 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo4_11_ : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 (HeapO: heapO),
in_list [n1;n3;n4;n10] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 -> n1 <> n10 -> n1 <> n11 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 -> n2 <> n10 -> n2 <> n11 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 -> n3 <> n10 -> n3 <> n11 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 -> n4 <> n10 -> n4 <> n11 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 -> n5 <> n10 -> n5 <> n11 ->
n6 <> n7 -> n6 <> n8 -> n6 <> n9 -> n6 <> n10 -> n6 <> n11 ->
n7 <> n8 -> n7 <> n9 -> n7 <> n10 -> n7 <> n11 ->
n8 <> n9 -> n8 <> n10 -> n8 <> n11 ->
n9 <> n10 -> n9 <> n11 ->
n10 <> n11 ->
exists k , ( n11 !ho-> l11; n10 !ho-> l10; n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo3 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto.
  rewrite H.
  exists (Some l10).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo5_9 : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 (HeapO: heapO),
in_list [n1;n2;n3;n4;n5] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 ->
n6 <> n7 -> n6 <> n8 -> n6 <> n9 ->
n7 <> n8 -> n7 <> n9 ->
n8 <> n9 ->
exists k , ( n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo4 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto.
  rewrite H.
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo5_9_ : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 (HeapO: heapO),
in_list [n2;n5;n6;n7;n8] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 ->
n6 <> n7 -> n6 <> n8 -> n6 <> n9 ->
n7 <> n8 -> n7 <> n9 ->
n8 <> n9 ->
exists k , ( n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo4 in H.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l6).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l7).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. 
  rewrite H.
  exists (Some l8).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. 
Qed.

Lemma SafeinHo5in9 : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 (HeapO: heapO),
in_list [n2;n3;n4;n7;n8] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 ->
n6 <> n7 -> n6 <> n8 -> n6 <> n9 ->
n7 <> n8 -> n7 <> n9 ->
n8 <> n9 ->
exists k , ( n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo4 in H.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l7).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. 
  rewrite H.
  exists (Some l8).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. 
Qed.


Lemma SafeinHo5_12 : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 (HeapO: heapO),
in_list [n1;n2;n3;n4;n5] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 -> n1 <> n10 -> n1 <> n11 -> n1 <> n12 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 -> n2 <> n10 -> n2 <> n11 -> n2 <> n12 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 -> n3 <> n10 -> n3 <> n11 -> n3 <> n12 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 -> n4 <> n10 -> n4 <> n11 -> n4 <> n12 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 -> n5 <> n10 -> n5 <> n11 -> n5 <> n12 ->
n6 <> n7 -> n6 <> n8 -> n6 <> n9 -> n6 <> n10 -> n6 <> n11 -> n6 <> n12 ->
n7 <> n8 -> n7 <> n9 -> n7 <> n10 -> n7 <> n11 -> n7 <> n12 ->
n8 <> n9 -> n8 <> n10 -> n8 <> n11 -> n8 <> n12 ->
n9 <> n10 -> n9 <> n11 -> n9 <> n12 ->
n10 <> n11 -> n10 <> n12 ->
n11 <> n12 ->
exists k , ( n12 !ho-> l12; n11 !ho-> l11; n10 !ho-> l10; n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo4 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H.
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo5_12_ : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 (HeapO: heapO),
in_list [n1;n3;n4;n10;n11] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 -> n1 <> n10 -> n1 <> n11 -> n1 <> n12 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 -> n2 <> n10 -> n2 <> n11 -> n2 <> n12 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 -> n3 <> n10 -> n3 <> n11 -> n3 <> n12 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 -> n4 <> n10 -> n4 <> n11 -> n4 <> n12 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 -> n5 <> n10 -> n5 <> n11 -> n5 <> n12 ->
n6 <> n7 -> n6 <> n8 -> n6 <> n9 -> n6 <> n10 -> n6 <> n11 -> n6 <> n12 ->
n7 <> n8 -> n7 <> n9 -> n7 <> n10 -> n7 <> n11 -> n7 <> n12 ->
n8 <> n9 -> n8 <> n10 -> n8 <> n11 -> n8 <> n12 ->
n9 <> n10 -> n9 <> n11 -> n9 <> n12 ->
n10 <> n11 -> n10 <> n12 ->
n11 <> n12 ->
exists k , ( n12 !ho-> l12; n11 !ho-> l11; n10 !ho-> l10; n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo4 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l10).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. 
  rewrite H.
  exists (Some l11).
  rewrite hO_update_neq.  rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. 
Qed.

Lemma SafeinHo6_7 : forall (l1 l2 l3 l4 l5 l6 l7: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 (HeapO: heapO),
in_list [n1;n2;n3;n4;n5;n6] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 ->
n5 <> n6 -> n5 <> n7 ->
n6 <> n7 ->
exists k , ( n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo5 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto.
  rewrite H.
  exists (Some l6).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo6in10 : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 (HeapO: heapO),
in_list [n2;n3;n4;n7;n8;n9] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> 
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 -> n1 <> n10 -> 
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 -> n2 <> n10 -> 
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 -> n3 <> n10 -> 
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 -> n4 <> n10 -> 
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 -> n5 <> n10 -> 
n6 <> n7 -> n6 <> n8 -> n6 <> n9 -> n6 <> n10 ->
n7 <> n8 -> n7 <> n9 -> n7 <> n10 -> 
n8 <> n9 -> n8 <> n10 -> 
n9 <> n10 -> 
exists k , ( n10 !ho-> l10; n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo5 in H.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l7).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l8).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto.
  rewrite H.
  exists (Some l9).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. 
Qed.

Lemma SafeinHo6_13 : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 (HeapO: heapO),
in_list [n1;n2;n3;n4;n5;n6] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 -> n1 <> n10 -> n1 <> n11 -> n1 <> n12 -> n1 <> n13 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 -> n2 <> n10 -> n2 <> n11 -> n2 <> n12 -> n2 <> n13 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 -> n3 <> n10 -> n3 <> n11 -> n3 <> n12 -> n3 <> n13 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 -> n4 <> n10 -> n4 <> n11 -> n4 <> n12 -> n4 <> n13 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 -> n5 <> n10 -> n5 <> n11 -> n5 <> n12 -> n5 <> n13 ->
n6 <> n7 -> n6 <> n8 -> n6 <> n9 -> n6 <> n10 -> n6 <> n11 -> n6 <> n12 -> n6 <> n13 ->
n7 <> n8 -> n7 <> n9 -> n7 <> n10 -> n7 <> n11 -> n7 <> n12 -> n7 <> n13 ->
n8 <> n9 -> n8 <> n10 -> n8 <> n11 -> n8 <> n12 -> n8 <> n13 ->
n9 <> n10 -> n9 <> n11 -> n9 <> n12 -> n9 <> n13 ->
n10 <> n11 -> n10 <> n12 -> n10 <> n13 ->
n11 <> n12 -> n11 <> n13 ->
n12 <> n13 ->
exists k , ( n13 !ho-> l13; n12 !ho-> l12; n11 !ho-> l11; n10 !ho-> l10; n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo5 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H.
  exists (Some l6).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. 
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
Qed.

Lemma SafeinHo6_13_ : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 (HeapO: heapO),
in_list [n1;n3;n4;n10;n11;n12] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 -> n1 <> n10 -> n1 <> n11 -> n1 <> n12 -> n1 <> n13 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 -> n2 <> n10 -> n2 <> n11 -> n2 <> n12 -> n2 <> n13 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 -> n3 <> n10 -> n3 <> n11 -> n3 <> n12 -> n3 <> n13 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 -> n4 <> n10 -> n4 <> n11 -> n4 <> n12 -> n4 <> n13 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 -> n5 <> n10 -> n5 <> n11 -> n5 <> n12 -> n5 <> n13 ->
n6 <> n7 -> n6 <> n8 -> n6 <> n9 -> n6 <> n10 -> n6 <> n11 -> n6 <> n12 -> n6 <> n13 ->
n7 <> n8 -> n7 <> n9 -> n7 <> n10 -> n7 <> n11 -> n7 <> n12 -> n7 <> n13 ->
n8 <> n9 -> n8 <> n10 -> n8 <> n11 -> n8 <> n12 -> n8 <> n13 ->
n9 <> n10 -> n9 <> n11 -> n9 <> n12 -> n9 <> n13 ->
n10 <> n11 -> n10 <> n12 -> n10 <> n13 ->
n11 <> n12 -> n11 <> n13 ->
n12 <> n13 ->
exists k , ( n13 !ho-> l13; n12 !ho-> l12; n11 !ho-> l11; n10 !ho-> l10; n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo5 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l10).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some l11).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto.  
  rewrite H.
  exists (Some l12).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. 
Qed.

Lemma SafeinHo7_8 : forall (l1 l2 l3 l4 l5 l6 l7 l8: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 (HeapO: heapO),
in_list [n1;n2;n3;n4;n5;n6;n7] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 ->
n6 <> n7 -> n6 <> n8 ->
n7 <> n8 ->
exists k , ( n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo6 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l6).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto.
  rewrite H.
  exists (Some l7).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto.
Qed.

Lemma SafeinHo8_9 : forall (l1 l2 l3 l4 l5 l6 l7 l8 l9: list (option nat)) l n1 n2 n3 n4 n5 n6 n7 n8 n9 (HeapO: heapO),
in_list [n1;n2;n3;n4;n5;n6;n7;n8] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 ->
n1 <> n2 -> n1 <> n3 -> n1 <> n4 ->  n1 <> n5 -> n1 <> n6 -> n1 <> n7 -> n1 <> n8 -> n1 <> n9 ->
n2 <> n3 -> n2 <> n4 ->  n2 <> n5 -> n2 <> n6 -> n2 <> n7 -> n2 <> n8 -> n2 <> n9 ->
n3 <> n4 ->  n3 <> n5 -> n3 <> n6 -> n3 <> n7 -> n3 <> n8 -> n3 <> n9 ->
n4 <> n5 -> n4 <> n6 -> n4 <> n7 -> n4 <> n8 -> n4 <> n9 ->
n5 <> n6 -> n5 <> n7 -> n5 <> n8 -> n5 <> n9 ->
n6 <> n7 -> n6 <> n8 -> n6 <> n9 ->
n7 <> n8 -> n7 <> n9 ->
n8 <> n9 ->
exists k , ( n9 !ho-> l9; n8 !ho-> l8; n7 !ho-> l7; n6 !ho-> l6; n5 !ho-> l5; n4 !ho-> l4;n3 !ho-> l3;n2 !ho-> l2; n1 !ho-> l1; HeapO) l = k.
Proof.
  intros.
  apply InHo7 in H.
  destruct H. rewrite H.
  exists (Some l1).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l2).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l3).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l4).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l5).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l6).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto. auto.
  destruct H. rewrite H.
  exists (Some l7).
  rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.
  auto. auto.
  rewrite H.
  exists (Some l8).
  rewrite hO_update_neq. rewrite hO_update_eq. reflexivity.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto.
Qed.