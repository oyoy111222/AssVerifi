Require Import Aid.
Require Import semantic.
Require Import function.
Require Import state.
Require Import Coq.Strings.String.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Lists.List.
Import ListNotations.

Lemma oneqv : forall (l : option nat) n,
  n <> 0 ->
  (o2v l =? n) = beq_op_nat (v2o n) l.
Proof.
  intros.
  destruct l; simpl.
  - rewrite beq_comm. auto.
  - destruct n. destruct H. auto.
    auto.
Qed.

Lemma InHr : forall (l : option nat) n1 n2,
in_list_list [v2o n2; v2o n1] l = true ->
n1 <> 0 -> n2 <> 0 -> 
o2v l = n1 \/ o2v l = n2.
Proof.
    intros.
    destruct ((o2v l) =? n1) eqn : L1.
    apply beq_eq in L1.
    rewrite L1.
    left. auto.
    destruct ((o2v l) =? n2) eqn : L2.
    apply beq_eq in L2.
    rewrite L2.
    right. auto. rewrite oneqv in L1.
    rewrite oneqv in L2.
    unfold in_list_list in H.
    rewrite L1 in H. rewrite L2 in H.
    discriminate. auto. auto.
Qed.

Lemma InHr1 : forall (l : option nat) n1 n2 n3,
in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 ->
o2v l = n1 \/ o2v l = n2 \/ o2v l = n3.
Proof.
    intros.
    destruct ((o2v l) =? n1) eqn : L1.
    apply beq_eq in L1.
    rewrite L1.
    left. auto.
    destruct ((o2v l) =? n2) eqn : L2.
    apply beq_eq in L2.
    rewrite L2.
    right. auto. rewrite oneqv in L1.
    rewrite oneqv in L2.
    unfold in_list_list in H.
    rewrite L1 in H. rewrite L2 in H.
    destruct ((o2v l) =? n3) eqn : L3.
    apply beq_eq in L3.
    rewrite L3. right. right. reflexivity.
    rewrite oneqv in L3.
    rewrite L3 in H.
    discriminate. auto. auto. auto.
Qed.

Lemma InHr2 : forall (l : option nat) n1 n2 n3 n4,
in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 ->
o2v l = n1 \/ o2v l = n2 \/ o2v l = n3 \/ o2v l = n4.

Proof.
    intros.
    destruct ((o2v l) =? n1) eqn : L1.
    apply beq_eq in L1.
    rewrite L1.
    left. auto.
    destruct ((o2v l) =? n2) eqn : L2.
    apply beq_eq in L2.
    rewrite L2.
    right. auto. rewrite oneqv in L1.
    rewrite oneqv in L2.
    unfold in_list_list in H.
    rewrite L1 in H. rewrite L2 in H.
    destruct ((o2v l) =? n3) eqn : L3.
    apply beq_eq in L3.
    rewrite L3. right. right. auto.
    rewrite oneqv in L3.
    rewrite L3 in H.
    destruct ((o2v l) =? n4) eqn : L4.
    apply beq_eq in L4. auto.
    rewrite oneqv in L4.
    rewrite L4 in H.
    discriminate. auto. auto. auto. auto.
Qed.

Lemma SafeinHr2_2 : forall (l : option nat) n1 n2 n3 n4,
 in_list_list [v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> 
 n1 <> n2 ->

 exists k , (n2 !hr-> n4; n1 !hr-> n3; emp_heapR) (o2v l) = k.

Proof.
  intros.
  apply InHr in H.
  destruct H; rewrite H.
  exists (Some n3).
  rewrite hR_update_neq. rewrite hR_update_eq. reflexivity.
  auto.
  exists (Some n4).
  rewrite hR_update_eq. reflexivity.
  auto. auto.
Qed.

Lemma SafeinHr2_11 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 ,
 in_list_list [v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> 
 n8<>n9 -> n8<>n10 -> n8<>n11 -> 
 n9<>n10 -> n9<>n11 -> 
 n10<>n11 ->

 exists k ,(n11 !hr-> n22; n10 !hr-> n21; n9 !hr-> n20; n8 !hr-> n19; n7 !hr-> n18; n6 !hr-> n17; n5 !hr-> n16; n4 !hr-> n15; n3 !hr-> n14; n2 !hr-> n13; n1 !hr-> n12;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr in H.
  destruct H. rewrite H.
  exists (Some n12).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H.
  exists (Some n13).
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. 
Qed.

Lemma SafeinHr2_14 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23 n24 n25 n26 n27 n28,
 in_list_list [v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> 
 n12<>n13 -> n12<>n14 -> 
 n13<>n14 -> 

 exists k ,(n14 !hr-> n28; n13 !hr-> n27; n12 !hr-> n26; n11 !hr-> n25; n10 !hr-> n24; n9 !hr-> n23; n8 !hr-> n22; n7 !hr-> n21; n6 !hr-> n20; n5 !hr-> n19; n4 !hr-> n18; n3 !hr-> n17; n2 !hr-> n16; n1 !hr-> n15;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr in H.
  destruct H. rewrite H.
  exists (Some n15).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H.
  exists (Some n16).
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. 
Qed.

Lemma SafeinHr2_21 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                     n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42,
 in_list_list [v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->  n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 ->  
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 ->  
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 ->
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> 
 n19<>n20 -> n19<>n21 -> 
 n20<>n21 ->  

 exists k ,( n21 !hr-> n42; n20 !hr-> n41; n19 !hr-> n40; n18 !hr-> n39; n17 !hr-> n38; n16 !hr-> n37; n15 !hr-> n36; n14 !hr-> n35; n13 !hr-> n34; n12 !hr-> n33; n11 !hr-> n32; n10 !hr-> n31; n9 !hr-> n30; n8 !hr-> n29; n7 !hr-> n28; n6 !hr-> n27; n5 !hr-> n26; n4 !hr-> n25; n3 !hr-> n24; n2 !hr-> n23; n1 !hr-> n22;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr in H.
  destruct H. rewrite H.
  exists (Some n22).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
  rewrite H.
  exists (Some n23).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. 
Qed.

Lemma SafeinHr2_27 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54  ,
 in_list_list [v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 ->
 n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 ->  
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 ->
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 ->  
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> 
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 ->
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> 
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 ->
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 ->
 n24<>n25 -> n24<>n26 -> n24<>n27 ->
 n25<>n26 -> n25<>n27 ->
 n26<>n27 -> 

 exists k ,( n27 !hr-> n54; n26 !hr-> n53; n25 !hr-> n52; n24 !hr-> n51; n23 !hr-> n50; n22 !hr-> n49; n21 !hr-> n48; n20 !hr-> n47; n19 !hr-> n46; n18 !hr-> n45; n17 !hr-> n44; n16 !hr-> n43; n15 !hr-> n42; n14 !hr-> n41; n13 !hr-> n40; n12 !hr-> n39; n11 !hr-> n38; n10 !hr-> n37; n9 !hr-> n36; n8 !hr-> n35; n7 !hr-> n34; n6 !hr-> n33; n5 !hr-> n32; n4 !hr-> n31; n3 !hr-> n30; n2 !hr-> n29; n1 !hr-> n28;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr in H.
  destruct H. rewrite H.
  exists (Some n28).
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. 
  rewrite H.
  exists (Some n29).
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto.  
  auto. auto. 
Qed.

Lemma SafeinHr2_30 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 n57 n58 n59 n60 ,
 in_list_list [v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 ->
 n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 -> n29 <> 0 -> n30 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> n1<>n29 -> n1<>n30 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> n2<>n29 -> n2<>n30 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> n3<>n29 -> n3<>n30 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> n4<>n29 -> n4<>n30 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> n5<>n29 -> n5<>n30 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> n6<>n29 -> n6<>n30 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> n7<>n29 -> n7<>n30 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> n8<>n29 -> n8<>n30 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> n9<>n29 -> n9<>n30 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> n10<>n29 -> n10<>n30 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> n11<>n29 -> n11<>n30 ->  
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> n12<>n29 -> n12<>n30 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> n13<>n29 -> n13<>n30 ->  
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> n14<>n29 -> n14<>n30 ->  
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> n15<>n29 -> n15<>n30 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> n16<>n29 -> n16<>n30 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> n17<>n29 -> n17<>n30 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> n18<>n29 -> n18<>n30 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> n19<>n29 -> n19<>n30 ->
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> n20<>n29 -> n20<>n30 ->
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> n21<>n29 -> n21<>n30 -> 
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> n22<>n29 -> n22<>n30 ->
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> n23<>n29 -> n23<>n30 ->
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 -> n2<>n29 -> n24<>n30 ->
 n25<>n26 -> n25<>n27 -> n25<>n28 -> n25<>n29 -> n25<>n30 -> 
 n26<>n27 -> n26<>n28 -> n26<>n29 -> n26<>n30 ->
 n27<>n28 -> n27<>n29 -> n27<>n30 -> 
 n28<>n29 -> n28<>n30 ->
 n29<>n30 -> 

 exists k ,( n30 !hr-> n60; n29 !hr-> n59; n28 !hr-> n58; n27 !hr-> n57; n26 !hr-> n56; n25 !hr-> n55; n24 !hr-> n54; n23 !hr-> n53; n22 !hr-> n52; n21 !hr-> n51; n20 !hr-> n50; n19 !hr-> n49; n18 !hr-> n48; n17 !hr-> n47; n16 !hr-> n46; n15 !hr-> n45; n14 !hr-> n44; n13 !hr-> n43; n12 !hr-> n42; n11 !hr-> n41; n10 !hr-> n40; n9 !hr-> n39; n8 !hr-> n38; n7 !hr-> n37; n6 !hr-> n36; n5 !hr-> n35; n4 !hr-> n34; n3 !hr-> n33; n2 !hr-> n32; n1 !hr-> n31;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr in H.
  destruct H. rewrite H.
  exists (Some n31).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H.
  exists (Some n32).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. 
Qed.

Lemma SafeinHr3_3 : forall (l : option nat) n1 n2 n3 n4 n5 n6 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> 
 n1<>n2 -> n1<>n3 -> 
 n2<>n3 -> 

 exists k ,(n3 !hr-> n6; n2 !hr-> n5; n1 !hr-> n4;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n4).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. 
  destruct H. rewrite H.
  exists (Some n5).
  rewrite hR_update_neq.   
  rewrite hR_update_eq.
  reflexivity.
  auto.
  rewrite H. 
  exists (Some n6). 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. 
Qed.  

Lemma SafeinHr3_4 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> 
 n2<>n3 -> n2<>n4 -> 
 n3<>n4 -> 

 exists k ,(n4 !hr-> n8; n3 !hr-> n7; n2 !hr-> n6; n1 !hr-> n5;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n5).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto.  
  destruct H. rewrite H.
  exists (Some n6).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.   
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. 
  rewrite H. 
  exists (Some n7).
  rewrite hR_update_neq.  
  rewrite hR_update_eq.
  reflexivity.
  auto. 
  auto. auto. auto. 
Qed.  


Lemma SafeinHr3_5 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 ->  
 n2<>n3 -> n2<>n4 -> n2<>n5 -> 
 n3<>n4 -> n3<>n5 -> 
 n4<>n5 -> 

 exists k ,(n5 !hr-> n10; n4 !hr-> n9; n3 !hr-> n8; n2 !hr-> n7; n1 !hr-> n6;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n6).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto.  
  destruct H. rewrite H.
  exists (Some n7).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.   
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. 
  rewrite H. 
  exists (Some n8).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.  
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. 
  auto. auto. auto. 
Qed.  

Lemma SafeinHr3_6 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> 
 n4<>n5 -> n4<>n6 -> 
 n5<>n6 ->

 exists k ,(n6 !hr-> n12; n5 !hr-> n11; n4 !hr-> n10; n3 !hr-> n9; n2 !hr-> n8; n1 !hr-> n7;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n7).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n8).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.   
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n9).
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.  
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. 
  auto. auto. auto. 
Qed.  

Lemma SafeinHr3_7 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 ->
 n5<>n6 -> n5<>n7 ->
 n6<>n7 -> 

 exists k ,(n7 !hr-> n14; n6 !hr-> n13; n5 !hr-> n12; n4 !hr-> n11; n3 !hr-> n10; n2 !hr-> n9; n1 !hr-> n8;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n8).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n9).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.   
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n10).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.  
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. 
  auto. auto. auto. 
Qed.  

Lemma SafeinHr3_8 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 ->
 n6<>n7 -> n6<>n8 ->
 n7<>n8 ->

 exists k ,(n8 !hr-> n16; n7 !hr-> n15; n6 !hr-> n14; n5 !hr-> n13; n4 !hr-> n12; n3 !hr-> n11; n2 !hr-> n10; n1 !hr-> n9;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n9).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n10).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.   
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n11).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.  
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. 
  auto. auto. auto. 
Qed.  

Lemma SafeinHr3_9 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18  (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 ->  
 n6<>n7 -> n6<>n8 -> n6<>n9 ->  
 n7<>n8 -> n7<>n9 -> 
 n8<>n9 -> 

 exists k ,( n9 !hr-> n18; n8 !hr-> n17; n7 !hr-> n16; n6 !hr-> n15; n5 !hr-> n14; n4 !hr-> n13; n3 !hr-> n12; n2 !hr-> n11; n1 !hr-> n10;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n10).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n12).
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto.
  auto. auto. auto. 
Qed.  

Lemma SafeinHr3_10 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 ->  
 n7<>n8 -> n7<>n9 -> n7<>n10 -> 
 n8<>n9 -> n8<>n10 -> 
 n9<>n10 ->

 exists k ,( n10 !hr-> n20; n9 !hr-> n19; n8 !hr-> n18; n7 !hr-> n17; n6 !hr-> n16; n5 !hr-> n15; n4 !hr-> n14; n3 !hr-> n13; n2 !hr-> n12; n1 !hr-> n11;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n12).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n13).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. 
Qed.  


Lemma SafeinHr3_11 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 ->
 n8<>n9 -> n8<>n10 -> n8<>n11 ->
 n9<>n10 -> n9<>n11 -> 
 n10<>n11 -> 

 exists k ,( n11 !hr-> n22; n10 !hr-> n21; n9 !hr-> n20; n8 !hr-> n19; n7 !hr-> n18; n6 !hr-> n17; n5 !hr-> n16; n4 !hr-> n15; n3 !hr-> n14; n2 !hr-> n13; n1 !hr-> n12;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n12).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n13).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.  
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n14).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.  
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. 
Qed.  

Lemma SafeinHr3_12 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23 n24 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> 
 n8<>n9 -> n8<>n10 -> n8<>n11 -> n8<>n12 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> 
 n10<>n11 -> n10<>n12 ->
 n11<>n12 ->

 exists k ,(n12 !hr-> n24; n11 !hr-> n23; n10 !hr-> n22; n9 !hr-> n21; n8 !hr-> n20; n7 !hr-> n19; n6 !hr-> n18; n5 !hr-> n17; n4 !hr-> n16; n3 !hr-> n15; n2 !hr-> n14; n1 !hr-> n13;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n13).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n14).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.  
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n15).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.  
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. 
Qed.  

Lemma SafeinHr3_13 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> 
 n12 <> 0 -> n13 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 ->
 n11<>n12 -> n11<>n13 -> 
 n12<>n13 -> 

 exists k ,(n13 !hr-> n26; n12 !hr-> n25; n11 !hr-> n24; n10 !hr-> n23; n9 !hr-> n22; n8 !hr-> n21; n7 !hr-> n20; n6 !hr-> n19; n5 !hr-> n18; n4 !hr-> n17; n3 !hr-> n16; n2 !hr-> n15; n1 !hr-> n14; HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n14).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n15).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n16).
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
Qed.

Lemma SafeinHr3_14 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> 
 n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> 
 n12<>n13 -> n12<>n14 -> 
 n13<>n14 -> 

 exists k ,( n14 !hr-> n28; n13 !hr-> n27; n12 !hr-> n26; n11 !hr-> n25; n10 !hr-> n24; n9 !hr-> n23; n8 !hr-> n22; n7 !hr-> n21; n6 !hr-> n20; n5 !hr-> n19; n4 !hr-> n18; n3 !hr-> n17; n2 !hr-> n16; n1 !hr-> n15; HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n15).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n16).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n17).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
Qed.  

Lemma SafeinHr3_15 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> 
 n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 ->   
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> 
 n13<>n14 -> n13<>n15 -> 
 n14<>n15 ->

 exists k ,(n15 !hr-> n30; n14 !hr-> n29; n13 !hr-> n28; n12 !hr-> n27; n11 !hr-> n26; n10 !hr-> n25; n9 !hr-> n24; n8 !hr-> n23; n7 !hr-> n22; n6 !hr-> n21; n5 !hr-> n20; n4 !hr-> n19; n3 !hr-> n18; n2 !hr-> n17; n1 !hr-> n16; HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n16).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n17).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n18).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
Qed.  

Lemma SafeinHr3_16 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> 
 n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 ->
 n14<>n15 -> n14<>n16 ->
 n15<>n16 -> 

 exists k ,(n16 !hr-> n32; n15 !hr-> n31; n14 !hr-> n30; n13 !hr-> n29; n12 !hr-> n28; n11 !hr-> n27; n10 !hr-> n26; n9 !hr-> n25; n8 !hr-> n24; n7 !hr-> n23; n6 !hr-> n22; n5 !hr-> n21; n4 !hr-> n20; n3 !hr-> n19; n2 !hr-> n18; n1 !hr-> n17;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n17).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n18).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n19).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
Qed.  

Lemma SafeinHr3_17 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> 
 n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 ->
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 ->
 n14<>n15 -> n14<>n16 -> n14<>n17 ->
 n15<>n16 -> n15<>n17 ->
 n16<>n17 -> 

 exists k ,(n17 !hr-> n34; n16 !hr-> n33; n15 !hr-> n32; n14 !hr-> n31; n13 !hr-> n30; n12 !hr-> n29; n11 !hr-> n28; n10 !hr-> n27; n9 !hr-> n26; n8 !hr-> n25; n7 !hr-> n24; n6 !hr-> n23; n5 !hr-> n22; n4 !hr-> n21; n3 !hr-> n20; n2 !hr-> n19; n1 !hr-> n18;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n18).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n19).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n20).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
Qed.  

Lemma SafeinHr3_18 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 (HeapR: heapR) ,
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> 
 n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 ->  
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> 
 n16<>n17 -> n16<>n18 -> 
 n17<>n18 -> 
 exists k ,( n18 !hr-> n36; n17 !hr-> n35; n16 !hr-> n34; n15 !hr-> n33; n14 !hr-> n32; n13 !hr-> n31; n12 !hr-> n30; n11 !hr-> n29; n10 !hr-> n28; n9 !hr-> n27; n8 !hr-> n26; n7 !hr-> n25; n6 !hr-> n24; n5 !hr-> n23; n4 !hr-> n22; n3 !hr-> n21; n2 !hr-> n20; n1 !hr-> n19;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n19).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n20).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.  
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n21).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
Qed.  

Lemma SafeinHr3_19 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 (HeapR: heapR) ,
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->  n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 ->
 n16<>n17 -> n16<>n18 -> n16<>n19 ->
 n17<>n18 -> n17<>n19 -> 
 n18<>n19 -> 

 exists k ,( n19 !hr-> n38; n18 !hr-> n37; n17 !hr-> n36; n16 !hr-> n35; n15 !hr-> n34; n14 !hr-> n33; n13 !hr-> n32; n12 !hr-> n31; n11 !hr-> n30; n10 !hr-> n29; n9 !hr-> n28; n8 !hr-> n27; n7 !hr-> n26; n6 !hr-> n25; n5 !hr-> n24; n4 !hr-> n23; n3 !hr-> n22; n2 !hr-> n21; n1 !hr-> n20;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n20).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n21).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n22).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
Qed.  


Lemma SafeinHr3_20 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 (HeapR: heapR) ,
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->  n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 ->
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 ->
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 ->
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 ->
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 ->
 n17<>n18 -> n17<>n19 -> n17<>n20 ->
 n18<>n19 -> n18<>n20 ->
 n19<>n20 ->

 exists k ,( n20 !hr-> n40; n19 !hr-> n39; n18 !hr-> n38; n17 !hr-> n37; n16 !hr-> n36; n15 !hr-> n35; n14 !hr-> n34; n13 !hr-> n33; n12 !hr-> n32; n11 !hr-> n31; n10 !hr-> n30; n9 !hr-> n29; n8 !hr-> n28; n7 !hr-> n27; n6 !hr-> n26; n5 !hr-> n25; n4 !hr-> n24; n3 !hr-> n23; n2 !hr-> n22; n1 !hr-> n21;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n21).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n22).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n23).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
Qed.  

Lemma SafeinHr3_21 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42,
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->  n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 ->  
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 ->  
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 ->  
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 ->
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 ->
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 ->
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 ->
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 ->
 n18<>n19 -> n18<>n20 -> n18<>n21 ->
 n19<>n20 -> n19<>n21 ->
 n20<>n21 ->

 exists k ,( n21 !hr-> n42; n20 !hr-> n41; n19 !hr-> n40; n18 !hr-> n39; n17 !hr-> n38; n16 !hr-> n37; n15 !hr-> n36; n14 !hr-> n35; n13 !hr-> n34; n12 !hr-> n33; n11 !hr-> n32; n10 !hr-> n31; n9 !hr-> n30; n8 !hr-> n29; n7 !hr-> n28; n6 !hr-> n27; n5 !hr-> n26; n4 !hr-> n25; n3 !hr-> n24; n2 !hr-> n23; n1 !hr-> n22;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n22).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
  destruct H. rewrite H.
  exists (Some n23).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
  rewrite H. 
  exists (Some n24).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
Qed.  

Lemma SafeinHr3_22 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->  n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 ->
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> 
 n20<>n21 -> n20<>n22 -> 
 n21<>n22 -> 

 exists k ,( n22 !hr-> n44; n21 !hr-> n43; n20 !hr-> n42; n19 !hr-> n41; n18 !hr-> n40; n17 !hr-> n39; n16 !hr-> n38; n15 !hr-> n37; n14 !hr-> n36; n13 !hr-> n35; n12 !hr-> n34; n11 !hr-> n33; n10 !hr-> n32; n9 !hr-> n31; n8 !hr-> n30; n7 !hr-> n29; n6 !hr-> n28; n5 !hr-> n27; n4 !hr-> n26; n3 !hr-> n25; n2 !hr-> n24; n1 !hr-> n23;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n23).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n24).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n25).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
Qed.  


Lemma SafeinHr3_23 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->  n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 ->
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 ->  
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 ->
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 ->
 n20<>n21 -> n20<>n22 -> n20<>n23 ->  
 n21<>n22 -> n21<>n23 ->
 n22<>n23 -> 

 exists k ,( n23 !hr-> n46; n22 !hr-> n45; n21 !hr-> n44; n20 !hr-> n43; n19 !hr-> n42; n18 !hr-> n41; n17 !hr-> n40; n16 !hr-> n39; n15 !hr-> n38; n14 !hr-> n37; n13 !hr-> n36; n12 !hr-> n35; n11 !hr-> n34; n10 !hr-> n33; n9 !hr-> n32; n8 !hr-> n31; n7 !hr-> n30; n6 !hr-> n29; n5 !hr-> n28; n4 !hr-> n27; n3 !hr-> n26; n2 !hr-> n25; n1 !hr-> n24;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n24).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n25).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n26).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
Qed.  

Lemma SafeinHr3_24 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 ,
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->  n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 ->  
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 ->  
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 ->
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> 
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 ->  
 n21<>n22 -> n21<>n23 -> n21<>n24 -> 
 n22<>n23 -> n22<>n24 -> 
 n23<>n24 -> 

 exists k ,( n24 !hr-> n48; n23 !hr-> n47; n22 !hr-> n46; n21 !hr-> n45; n20 !hr-> n44; n19 !hr-> n43; n18 !hr-> n42; n17 !hr-> n41; n16 !hr-> n40; n15 !hr-> n39; n14 !hr-> n38; n13 !hr-> n37; n12 !hr-> n36; n11 !hr-> n35; n10 !hr-> n34; n9 !hr-> n33; n8 !hr-> n32; n7 !hr-> n31; n6 !hr-> n30; n5 !hr-> n29; n4 !hr-> n28; n3 !hr-> n27; n2 !hr-> n26; n1 !hr-> n25;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n25).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
  destruct H. rewrite H.
  exists (Some n26).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
  rewrite H. 
  exists (Some n27).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
Qed.  

Lemma SafeinHr3_26 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 (HeapR: heapR),
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 ->
 n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 ->
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 ->
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 ->
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 ->
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 ->
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 ->
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> 
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> 
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 ->
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 ->
 n23<>n24 -> n23<>n25 -> n23<>n26 ->
 n24<>n25 -> n24<>n26 ->
 n25<>n26 ->

 exists k ,( n26 !hr-> n52; n25 !hr-> n51; n24 !hr-> n50; n23 !hr-> n49; n22 !hr-> n48; n21 !hr-> n47; n20 !hr-> n46; n19 !hr-> n45; n18 !hr-> n44; n17 !hr-> n43; n16 !hr-> n42; n15 !hr-> n41; n14 !hr-> n40; n13 !hr-> n39; n12 !hr-> n38; n11 !hr-> n37; n10 !hr-> n36; n9 !hr-> n35; n8 !hr-> n34; n7 !hr-> n33; n6 !hr-> n32; n5 !hr-> n31; n4 !hr-> n30; n3 !hr-> n29; n2 !hr-> n28; n1 !hr-> n27;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n27).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto.
  destruct H. rewrite H.
  exists (Some n28).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.
  rewrite H.
  exists (Some n29).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. 
  auto. auto. auto.
Qed.


Lemma SafeinHr3_29 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 n57 n58 ,
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 ->
 n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 -> n29 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> n1<>n29 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> n2<>n29 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> n3<>n29 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> n4<>n29 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> n5<>n29 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> n6<>n29 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> n7<>n29 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> n8<>n29 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> n9<>n29 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> n10<>n29 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> n11<>n29 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> n12<>n29 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> n13<>n29 ->  
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> n14<>n29 ->  
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> n15<>n29 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> n16<>n29 ->
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> n17<>n29 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> n18<>n29 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> n19<>n29 ->
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> n20<>n29 -> 
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> n21<>n29 -> 
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> n22<>n29 -> 
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> n23<>n29 -> 
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 -> n2<>n29 -> 
 n25<>n26 -> n25<>n27 -> n25<>n28 -> n25<>n29 -> 
 n26<>n27 -> n26<>n28 -> n26<>n29 -> 
 n27<>n28 -> n27<>n29 -> 
 n28<>n29 -> 

 exists k ,( n29 !hr-> n58; n28 !hr-> n57; n27 !hr-> n56; n26 !hr-> n55; n25 !hr-> n54; n24 !hr-> n53; n23 !hr-> n52; n22 !hr-> n51; n21 !hr-> n50; n20 !hr-> n49; n19 !hr-> n48; n18 !hr-> n47; n17 !hr-> n46; n16 !hr-> n45; n15 !hr-> n44; n14 !hr-> n43; n13 !hr-> n42; n12 !hr-> n41; n11 !hr-> n40; n10 !hr-> n39; n9 !hr-> n38; n8 !hr-> n37; n7 !hr-> n36; n6 !hr-> n35; n5 !hr-> n34; n4 !hr-> n33; n3 !hr-> n32; n2 !hr-> n31; n1 !hr-> n30;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n30).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n31).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto.
  rewrite H.
  exists (Some n32).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. 
  auto. auto. auto.
Qed.

Lemma SafeinHr3_30 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 n57 n58 n59 n60 ,
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 ->
 n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 -> n29 <> 0 -> n30 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> n1<>n29 -> n1<>n30 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> n2<>n29 -> n2<>n30 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> n3<>n29 -> n3<>n30 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> n4<>n29 -> n4<>n30 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> n5<>n29 -> n5<>n30 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> n6<>n29 -> n6<>n30 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> n7<>n29 -> n7<>n30 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> n8<>n29 -> n8<>n30 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> n9<>n29 -> n9<>n30 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> n10<>n29 -> n10<>n30 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> n11<>n29 -> n11<>n30 ->  
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> n12<>n29 -> n12<>n30 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> n13<>n29 -> n13<>n30 ->  
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> n14<>n29 -> n14<>n30 ->  
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> n15<>n29 -> n15<>n30 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> n16<>n29 -> n16<>n30 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> n17<>n29 -> n17<>n30 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> n18<>n29 -> n18<>n30 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> n19<>n29 -> n19<>n30 ->
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> n20<>n29 -> n20<>n30 ->
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> n21<>n29 -> n21<>n30 -> 
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> n22<>n29 -> n22<>n30 ->
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> n23<>n29 -> n23<>n30 ->
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 -> n2<>n29 -> n24<>n30 ->
 n25<>n26 -> n25<>n27 -> n25<>n28 -> n25<>n29 -> n25<>n30 -> 
 n26<>n27 -> n26<>n28 -> n26<>n29 -> n26<>n30 ->
 n27<>n28 -> n27<>n29 -> n27<>n30 -> 
 n28<>n29 -> n28<>n30 ->
 n29<>n30 -> 

 exists k ,( n30 !hr-> n60; n29 !hr-> n59; n28 !hr-> n58; n27 !hr-> n57; n26 !hr-> n56; n25 !hr-> n55; n24 !hr-> n54; n23 !hr-> n53; n22 !hr-> n52; n21 !hr-> n51; n20 !hr-> n50; n19 !hr-> n49; n18 !hr-> n48; n17 !hr-> n47; n16 !hr-> n46; n15 !hr-> n45; n14 !hr-> n44; n13 !hr-> n43; n12 !hr-> n42; n11 !hr-> n41; n10 !hr-> n40; n9 !hr-> n39; n8 !hr-> n38; n7 !hr-> n37; n6 !hr-> n36; n5 !hr-> n35; n4 !hr-> n34; n3 !hr-> n33; n2 !hr-> n32; n1 !hr-> n31;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n31).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H.
  exists (Some n32).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H.
  exists (Some n33).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto.  
  auto. auto. auto.
Qed.

Lemma SafeinHr3_33 :  forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 n57 n58 n59 n60 n61 n62 n63 n64 n65
                    n66 ,
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> 
 n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 -> n29 <> 0 -> n30 <> 0 -> n31 <> 0 -> n32 <> 0 -> n33 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> n1<>n29 -> n1<>n30 -> n1<>n31 -> n1<>n32 -> n1<>n33 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> n2<>n29 -> n2<>n30 -> n2<>n31 -> n2<>n32 -> n2<>n33 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> n3<>n29 -> n3<>n30 -> n3<>n31 -> n3<>n32 -> n3<>n33 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> n4<>n29 -> n4<>n30 -> n4<>n31 -> n4<>n32 -> n4<>n33 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> n5<>n29 -> n5<>n30 -> n5<>n31 -> n5<>n32 -> n5<>n33 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> n6<>n29 -> n6<>n30 -> n6<>n31 -> n6<>n32 -> n6<>n33 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> n7<>n29 -> n7<>n30 -> n7<>n31 -> n7<>n32 -> n7<>n33 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> n8<>n29 -> n8<>n30 -> n8<>n31 -> n8<>n32 -> n8<>n33 ->  
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> n9<>n29 -> n9<>n30 -> n9<>n31 -> n9<>n32 -> n9<>n33 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> n10<>n29 -> n10<>n30 -> n10<>n31 -> n10<>n32 -> n10<>n33 ->  
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> n11<>n29 -> n11<>n30 -> n11<>n31 -> n11<>n32 -> n11<>n33 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> n12<>n29 -> n12<>n30 -> n12<>n31 -> n12<>n32 -> n12<>n33 ->
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> n13<>n29 -> n13<>n30 -> n13<>n31 -> n13<>n32 -> n13<>n33 ->
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> n14<>n29 -> n14<>n30 -> n14<>n31 -> n14<>n32 -> n14<>n33 ->
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> n15<>n29 -> n15<>n30 -> n15<>n31 -> n15<>n32 -> n15<>n33 ->
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> n16<>n29 -> n16<>n30 -> n16<>n31 -> n16<>n32 -> n16<>n33 ->
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> n17<>n29 -> n17<>n30 -> n17<>n31 -> n17<>n32 -> n17<>n33 ->
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> n18<>n29 -> n18<>n30 -> n18<>n31 -> n18<>n32 -> n18<>n33 ->
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> n19<>n29 -> n19<>n30 -> n19<>n31 -> n19<>n32 -> n19<>n33 ->
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> n20<>n29 -> n20<>n30 -> n20<>n31 -> n20<>n32 -> n20<>n33 ->
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> n21<>n29 -> n21<>n30 -> n21<>n31 -> n21<>n32 -> n21<>n33 ->
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> n22<>n29 -> n22<>n30 -> n22<>n31 -> n22<>n32 -> n22<>n33 ->
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> n23<>n29 -> n23<>n30 -> n23<>n31 -> n23<>n32 -> n23<>n33 ->
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 -> n24<>n29 -> n24<>n30 -> n24<>n31 -> n24<>n32 -> n24<>n33 ->
 n25<>n26 -> n25<>n27 -> n25<>n28 -> n25<>n29 -> n25<>n30 -> n25<>n31 -> n25<>n32 -> n25<>n33 ->
 n26<>n27 -> n26<>n28 -> n26<>n29 -> n26<>n30 -> n26<>n31 -> n26<>n32 -> n26<>n33 ->
 n27<>n28 -> n27<>n29 -> n27<>n30 -> n27<>n31 -> n27<>n32 -> n27<>n33 ->
 n28<>n29 -> n28<>n30 -> n28<>n31 -> n28<>n32 -> n28<>n33 ->
 n29<>n30 -> n29<>n31 -> n29<>n32 -> n29<>n33 ->
 n30<>n31 -> n30<>n32 -> n30<>n33 ->
 n31<>n32 -> n31<>n33 -> 
 n32<>n33 ->

 exists k ,( n33 !hr-> n66; n32 !hr-> n65; n31 !hr-> n64; n30 !hr-> n63; n29 !hr-> n62; n28 !hr-> n61; n27 !hr-> n60; n26 !hr-> n59; n25 !hr-> n58; n24 !hr-> n57; n23 !hr-> n56; n22 !hr-> n55; n21 !hr-> n54; n20 !hr-> n53; n19 !hr-> n52; n18 !hr-> n51; n17 !hr-> n50; n16 !hr-> n49; n15 !hr-> n48; n14 !hr-> n47; n13 !hr-> n46; n12 !hr-> n45; n11 !hr-> n44; n10 !hr-> n43; n9 !hr-> n42; n8 !hr-> n41; n7 !hr-> n40; n6 !hr-> n39; n5 !hr-> n38; n4 !hr-> n37; n3 !hr-> n36; n2 !hr-> n35; n1 !hr-> n34;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n34).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
  destruct H. rewrite H.
  exists (Some n35).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
  rewrite H. 
  exists (Some n36).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.   
  auto. auto. auto.
Qed.  


Lemma SafeinHr3_36 :  forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 n57 n58 n59 n60 n61 n62 n63 n64 n65
                    n66 n67 n68 n69 n70 n71 n72 ,
 in_list_list [v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> 
 n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 -> n29 <> 0 -> n30 <> 0 -> n31 <> 0 -> n32 <> 0 -> n33 <> 0 -> n34 <> 0 -> n35 <> 0 -> n36 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> n1<>n29 -> n1<>n30 -> n1<>n31 -> n1<>n32 -> n1<>n33 -> n1<>n34 -> n1<>n35 -> n1<>n36 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> n2<>n29 -> n2<>n30 -> n2<>n31 -> n2<>n32 -> n2<>n33 -> n2<>n34 -> n2<>n35 -> n2<>n36 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> n3<>n29 -> n3<>n30 -> n3<>n31 -> n3<>n32 -> n3<>n33 -> n3<>n34 -> n3<>n35 -> n3<>n36 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> n4<>n29 -> n4<>n30 -> n4<>n31 -> n4<>n32 -> n4<>n33 -> n4<>n34 -> n4<>n35 -> n4<>n36 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> n5<>n29 -> n5<>n30 -> n5<>n31 -> n5<>n32 -> n5<>n33 -> n5<>n34 -> n5<>n35 -> n5<>n36 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> n6<>n29 -> n6<>n30 -> n6<>n31 -> n6<>n32 -> n6<>n33 -> n6<>n34 -> n6<>n35 -> n6<>n36 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> n7<>n29 -> n7<>n30 -> n7<>n31 -> n7<>n32 -> n7<>n33 -> n7<>n34 -> n7<>n35 -> n7<>n36 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> n8<>n29 -> n8<>n30 -> n8<>n31 -> n8<>n32 -> n8<>n33 -> n8<>n34 -> n8<>n35 -> n8<>n36 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> n9<>n29 -> n9<>n30 -> n9<>n31 -> n9<>n32 -> n9<>n33 -> n9<>n34 -> n9<>n35 -> n9<>n36 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> n10<>n29 -> n10<>n30 -> n10<>n31 -> n10<>n32 -> n10<>n33 -> n10<>n34 -> n10<>n35 -> n10<>n36 ->  
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> n11<>n29 -> n11<>n30 -> n11<>n31 -> n11<>n32 -> n11<>n33 -> n11<>n34 -> n11<>n35 -> n11<>n36 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> n12<>n29 -> n12<>n30 -> n12<>n31 -> n12<>n32 -> n12<>n33 -> n12<>n34 -> n12<>n35 -> n12<>n36 ->
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> n13<>n29 -> n13<>n30 -> n13<>n31 -> n13<>n32 -> n13<>n33 -> n13<>n34 -> n13<>n35 -> n13<>n36 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> n14<>n29 -> n14<>n30 -> n14<>n31 -> n14<>n32 -> n14<>n33 -> n14<>n34 -> n14<>n35 -> n14<>n36 ->
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> n15<>n29 -> n15<>n30 -> n15<>n31 -> n15<>n32 -> n15<>n33 -> n15<>n34 -> n15<>n35 -> n15<>n36 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> n16<>n29 -> n16<>n30 -> n16<>n31 -> n16<>n32 -> n16<>n33 -> n16<>n34 -> n16<>n35 -> n16<>n36 ->
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> n17<>n29 -> n17<>n30 -> n17<>n31 -> n17<>n32 -> n17<>n33 -> n17<>n34 -> n17<>n35 -> n17<>n36 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> n18<>n29 -> n18<>n30 -> n18<>n31 -> n18<>n32 -> n18<>n33 -> n18<>n34 -> n18<>n35 -> n18<>n36 ->
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> n19<>n29 -> n19<>n30 -> n19<>n31 -> n19<>n32 -> n19<>n33 -> n19<>n34 -> n19<>n35 -> n19<>n36 ->
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> n20<>n29 -> n20<>n30 -> n20<>n31 -> n20<>n32 -> n20<>n33 -> n20<>n34 -> n20<>n35 -> n20<>n36 ->
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> n21<>n29 -> n21<>n30 -> n21<>n31 -> n21<>n32 -> n21<>n33 -> n21<>n34 -> n21<>n35 -> n21<>n36 ->
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> n22<>n29 -> n22<>n30 -> n22<>n31 -> n22<>n32 -> n22<>n33 -> n22<>n34 -> n22<>n35 -> n22<>n36 ->
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> n23<>n29 -> n23<>n30 -> n23<>n31 -> n23<>n32 -> n23<>n33 -> n23<>n34 -> n23<>n35 -> n23<>n36 ->
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 -> n24<>n29 -> n24<>n30 -> n24<>n31 -> n24<>n32 -> n24<>n33 -> n24<>n34 -> n24<>n35 -> n24<>n36 ->
 n25<>n26 -> n25<>n27 -> n25<>n28 -> n25<>n29 -> n25<>n30 -> n25<>n31 -> n25<>n32 -> n25<>n33 -> n25<>n34 -> n25<>n35 -> n25<>n36 ->
 n26<>n27 -> n26<>n28 -> n26<>n29 -> n26<>n30 -> n26<>n31 -> n26<>n32 -> n26<>n33 -> n26<>n34 -> n26<>n35 -> n26<>n36 ->
 n27<>n28 -> n27<>n29 -> n27<>n30 -> n27<>n31 -> n27<>n32 -> n27<>n33 -> n27<>n34 -> n27<>n35 -> n27<>n36 ->
 n28<>n29 -> n28<>n30 -> n28<>n31 -> n28<>n32 -> n28<>n33 -> n28<>n34 -> n28<>n35 -> n28<>n36 ->
 n29<>n30 -> n29<>n31 -> n29<>n32 -> n29<>n33 -> n29<>n34 -> n29<>n35 -> n29<>n36 -> 
 n30<>n31 -> n30<>n32 -> n30<>n33 -> n30<>n34 -> n30<>n35 -> n30<>n36 -> 
 n31<>n32 -> n31<>n33 -> n31<>n34 -> n31<>n35 -> n31<>n36 -> 
 n32<>n33 -> n32<>n34 -> n32<>n35 -> n32<>n36 ->
 n33<>n34 -> n33<>n35 -> n33<>n36 -> 
 n34<>n35 -> n34<>n36 -> 
 n35<>n36 ->

 exists k ,( n36 !hr-> n72; n35 !hr-> n71; n34 !hr-> n70; n33 !hr-> n69; n32 !hr-> n68; n31 !hr-> n67; n30 !hr-> n66; n29 !hr-> n65; n28 !hr-> n64; n27 !hr-> n63; n26 !hr-> n62; n25 !hr-> n61; n24 !hr-> n60; n23 !hr-> n59; n22 !hr-> n58; n21 !hr-> n57; n20 !hr-> n56; n19 !hr-> n55; n18 !hr-> n54; n17 !hr-> n53; n16 !hr-> n52; n15 !hr-> n51; n14 !hr-> n50; n13 !hr-> n49; n12 !hr-> n48; n11 !hr-> n47; n10 !hr-> n46; n9 !hr-> n45; n8 !hr-> n44; n7 !hr-> n43; n6 !hr-> n42; n5 !hr-> n41; n4 !hr-> n40; n3 !hr-> n39; n2 !hr-> n38; n1 !hr-> n37;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr1 in H.
  destruct H. rewrite H.
  exists (Some n37).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
  destruct H. rewrite H.
  exists (Some n38).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
  rewrite H. 
  exists (Some n39).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.   
  auto. auto. auto.
Qed.  

Lemma SafeinHr4_10 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 (HeapR: heapR),
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> 
 n8<>n9 -> n8<>n10 -> 
 n9<>n10 -> 

 exists k ,(n10 !hr-> n20; n9 !hr-> n19; n8 !hr-> n18; n7 !hr-> n17; n6 !hr-> n16; n5 !hr-> n15; n4 !hr-> n14; n3 !hr-> n13; n2 !hr-> n12; n1 !hr-> n11;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n11).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n12).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n13).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n14).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_12 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 ,
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> 
 n12 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 ->
 n8<>n9 -> n8<>n10 -> n8<>n11 -> n8<>n12 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> 
 n10<>n11 -> n10<>n12 -> 
 n11<>n12 -> 

 exists k ,(n12 !hr-> n24; n11 !hr-> n23; n10 !hr-> n22; n9 !hr-> n21; n8 !hr-> n20; n7 !hr-> n19; n6 !hr-> n18; n5 !hr-> n17; n4 !hr-> n16; n3 !hr-> n15; n2 !hr-> n14; n1 !hr-> n13;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n13).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n14).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n15).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n16).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_13 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26,
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> 
 n12 <> 0 -> n13 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 ->
 n8<>n9 -> n8<>n10 -> n8<>n11 -> n8<>n12 -> n8<>n13 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 ->
 n11<>n12 -> n11<>n13 ->
 n12<>n13 ->

 exists k ,(n13 !hr-> n26; n12 !hr-> n25; n11 !hr-> n24; n10 !hr-> n23; n9 !hr-> n22; n8 !hr-> n21; n7 !hr-> n20; n6 !hr-> n19; n5 !hr-> n18; n4 !hr-> n17; n3 !hr-> n16; n2 !hr-> n15; n1 !hr-> n14;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n14).
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_eq.
  reflexivity.
  destruct H. rewrite H. 
  exists (Some n15).
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto. 
  rewrite hR_update_eq.
  reflexivity.
  destruct H. rewrite H. 
  exists (Some n16).
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto. 
  rewrite hR_update_eq.
  reflexivity.
  rewrite H. 
  exists (Some n17).
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto.
  rewrite hR_update_neq; auto. 
  rewrite hR_update_neq; auto. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_16 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 (HeapR: heapR) ,
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> 
 n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> 
 n8<>n9 -> n8<>n10 -> n8<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> 
 n14<>n15 -> n14<>n16 -> 
 n15<>n16 -> 

 exists k ,(n16 !hr-> n32; n15 !hr-> n31; n14 !hr-> n30; n13 !hr-> n29; n12 !hr-> n28; n11 !hr-> n27; n10 !hr-> n26; n9 !hr-> n25; n8 !hr-> n24; n7 !hr-> n23; n6 !hr-> n22; n5 !hr-> n21; n4 !hr-> n20; n3 !hr-> n19; n2 !hr-> n18; n1 !hr-> n17;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n17).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n18).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n19).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n20).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_18 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 ,
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> 
 n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> 
 n8<>n9 -> n8<>n10 -> n8<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> 
 n16<>n17 -> n16<>n18 ->
 n17<>n18 -> 

 exists k ,( n18 !hr-> n36; n17 !hr-> n35; n16 !hr-> n34; n15 !hr-> n33; n14 !hr-> n32; n13 !hr-> n31; n12 !hr-> n30; n11 !hr-> n29; n10 !hr-> n28; n9 !hr-> n27; n8 !hr-> n26; n7 !hr-> n25; n6 !hr-> n24; n5 !hr-> n23; n4 !hr-> n22; n3 !hr-> n21; n2 !hr-> n20; n1 !hr-> n19;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n19).
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n20).
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n21).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n22).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_21 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42 ,
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> 
 n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 ->
 n8<>n9 -> n8<>n10 -> n8<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 ->
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 ->
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 ->
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 ->
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 ->
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 ->
 n18<>n19 -> n18<>n20 -> n18<>n21 ->
 n19<>n20 -> n19<>n21 ->
 n20<>n21 ->

 exists k ,(n21 !hr-> n42; n20 !hr-> n41; n19 !hr-> n40; n18 !hr-> n39; n17 !hr-> n38; n16 !hr-> n37; n15 !hr-> n36; n14 !hr-> n35; n13 !hr-> n34; n12 !hr-> n33; n11 !hr-> n32; n10 !hr-> n31; n9 !hr-> n30; n8 !hr-> n29; n7 !hr-> n28; n6 !hr-> n27; n5 !hr-> n26; n4 !hr-> n25; n3 !hr-> n24; n2 !hr-> n23; n1 !hr-> n22;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n22).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n23).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n24).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n25).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_22 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20
                    n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42 n43 n44
                    (HeapR: heapR) ,
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> 
 n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> 
 n20<>n21 -> n20<>n22 ->
 n21<>n22 ->  

 exists k ,( n22 !hr-> n44; n21 !hr-> n43; n20 !hr-> n42; n19 !hr-> n41; n18 !hr-> n40; n17 !hr-> n39; n16 !hr-> n38; n15 !hr-> n37; n14 !hr-> n36; n13 !hr-> n35; n12 !hr-> n34; n11 !hr-> n33; n10 !hr-> n32; n9 !hr-> n31; n8 !hr-> n30; n7 !hr-> n29; n6 !hr-> n28; n5 !hr-> n27; n4 !hr-> n26; n3 !hr-> n25; n2 !hr-> n24; n1 !hr-> n23;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n23).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n24).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n25).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n26).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_23 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 ,
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->  n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 ->  
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> 
 n20<>n21 -> n20<>n22 -> n20<>n23 -> 
 n21<>n22 -> n21<>n23 -> 
 n22<>n23 -> 

 exists k ,( n23 !hr-> n46; n22 !hr-> n45; n21 !hr-> n44; n20 !hr-> n43; n19 !hr-> n42; n18 !hr-> n41; n17 !hr-> n40; n16 !hr-> n39; n15 !hr-> n38; n14 !hr-> n37; n13 !hr-> n36; n12 !hr-> n35; n11 !hr-> n34; n10 !hr-> n33; n9 !hr-> n32; n8 !hr-> n31; n7 !hr-> n30; n6 !hr-> n29; n5 !hr-> n28; n4 !hr-> n27; n3 !hr-> n26; n2 !hr-> n25; n1 !hr-> n24;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n24). 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n25).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.  
  destruct H. rewrite H. 
  exists (Some n26).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.  
  rewrite H. 
  exists (Some n27). 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. 
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_25 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 ,
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->  n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 ->
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 ->
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 ->
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 ->
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 ->
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> 
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 ->
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> 
 n22<>n23 -> n22<>n24 -> n22<>n25 -> 
 n23<>n24 -> n23<>n25 ->
 n24<>n25 -> 

 exists k ,( n25 !hr-> n50; n24 !hr-> n49; n23 !hr-> n48; n22 !hr-> n47; n21 !hr-> n46; n20 !hr-> n45; n19 !hr-> n44; n18 !hr-> n43; n17 !hr-> n42; n16 !hr-> n41; n15 !hr-> n40; n14 !hr-> n39; n13 !hr-> n38; n12 !hr-> n37; n11 !hr-> n36; n10 !hr-> n35; n9 !hr-> n34; n8 !hr-> n33; n7 !hr-> n32; n6 !hr-> n31; n5 !hr-> n30; n4 !hr-> n29; n3 !hr-> n28; n2 !hr-> n27; n1 !hr-> n26;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n26). 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n27).
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n28).
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n29). 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. 
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_26 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52  (HeapR: heapR),
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->  n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 ->  
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 ->
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> 
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> 
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 ->
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> 
 n23<>n24 -> n23<>n25 -> n23<>n26 -> 
 n24<>n25 -> n24<>n26 -> 
 n25<>n26 -> 

 exists k ,( n26 !hr-> n52; n25 !hr-> n51; n24 !hr-> n50; n23 !hr-> n49; n22 !hr-> n48; n21 !hr-> n47; n20 !hr-> n46; n19 !hr-> n45; n18 !hr-> n44; n17 !hr-> n43; n16 !hr-> n42; n15 !hr-> n41; n14 !hr-> n40; n13 !hr-> n39; n12 !hr-> n38; n11 !hr-> n37; n10 !hr-> n36; n9 !hr-> n35; n8 !hr-> n34; n7 !hr-> n33; n6 !hr-> n32; n5 !hr-> n31; n4 !hr-> n30; n3 !hr-> n29; n2 !hr-> n28; n1 !hr-> n27; HeapR ) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n27).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n28).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n29).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n30).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto.
  auto. auto. auto. auto.
Qed.



Lemma SafeinHr4_27 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 (HeapR: heapR),
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->  n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 ->  
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 ->
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> 
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> 
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> 
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 ->
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> 
 n24<>n25 -> n24<>n26 -> n24<>n27 ->   
 n25<>n26 -> n25<>n27 -> 
 n26<>n27 -> 

 exists k ,( n27 !hr-> n54; n26 !hr-> n53; n25 !hr-> n52; n24 !hr-> n51; n23 !hr-> n50; n22 !hr-> n49; n21 !hr-> n48; n20 !hr-> n47; n19 !hr-> n46; n18 !hr-> n45; n17 !hr-> n44; n16 !hr-> n43; n15 !hr-> n42; n14 !hr-> n41; n13 !hr-> n40; n12 !hr-> n39; n11 !hr-> n38; n10 !hr-> n37; n9 !hr-> n36; n8 !hr-> n35; n7 !hr-> n34; n6 !hr-> n33; n5 !hr-> n32; n4 !hr-> n31; n3 !hr-> n30; n2 !hr-> n29; n1 !hr-> n28; HeapR ) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n28).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n29).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n30).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n31).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. 
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_28 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 (HeapR: heapR),
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0-> n9 <> 0 -> n10 <> 0 -> n11 <> 0 ->  n12 <> 0 -> n13 <> 0 -> n14 <> 0 ->
 n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> 
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> 
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> 
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> 
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> 
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 ->  
 n25<>n26 -> n25<>n27 -> n25<>n28 -> 
 n26<>n27 -> n26<>n28 -> 
 n27<>n28 -> 

 exists k ,( n28 !hr-> n56; n27 !hr-> n55; n26 !hr-> n54; n25 !hr-> n53; n24 !hr-> n52; n23 !hr-> n51; n22 !hr-> n50; n21 !hr-> n49; n20 !hr-> n48; n19 !hr-> n47; n18 !hr-> n46; n17 !hr-> n45; n16 !hr-> n44; n15 !hr-> n43; n14 !hr-> n42; n13 !hr-> n41; n12 !hr-> n40; n11 !hr-> n39; n10 !hr-> n38; n9 !hr-> n37; n8 !hr-> n36; n7 !hr-> n35; n6 !hr-> n34; n5 !hr-> n33; n4 !hr-> n32; n3 !hr-> n31; n2 !hr-> n30; n1 !hr-> n29; HeapR ) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n29).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n30).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n31).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n32).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. 
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_28_ : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 n57 n58 n59 n60 ,
 in_list_list [v2o n6; v2o n5; v2o n4; v2o n3] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 ->
 n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 -> n29 <> 0 -> n30 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> n1<>n29 -> n1<>n30 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> n2<>n29 -> n2<>n30 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> n3<>n29 -> n3<>n30 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> n4<>n29 -> n4<>n30 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> n5<>n29 -> n5<>n30 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> n6<>n29 -> n6<>n30 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> n7<>n29 -> n7<>n30 ->  
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> n8<>n29 -> n8<>n30 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> n9<>n29 -> n9<>n30 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> n10<>n29 -> n10<>n30 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> n11<>n29 -> n11<>n30 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> n12<>n29 -> n12<>n30 ->
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> n13<>n29 -> n13<>n30 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> n14<>n29 -> n14<>n30 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> n15<>n29 -> n15<>n30 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> n16<>n29 -> n16<>n30 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> n17<>n29 -> n17<>n30 ->
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> n18<>n29 -> n18<>n30 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> n19<>n29 -> n19<>n30 -> 
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> n20<>n29 -> n20<>n30 ->
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> n21<>n29 -> n21<>n30 -> 
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> n22<>n29 -> n22<>n30 -> 
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> n23<>n29 -> n23<>n30 -> 
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 -> n2<>n29 -> n24<>n30 ->
 n25<>n26 -> n25<>n27 -> n25<>n28 -> n25<>n29 -> n25<>n30 -> 
 n26<>n27 -> n26<>n28 -> n26<>n29 -> n26<>n30 -> 
 n27<>n28 -> n27<>n29 -> n27<>n30 -> 
 n28<>n29 -> n28<>n30 -> 
 n29<>n30 -> 

 exists k ,( n30 !hr-> n60; n29 !hr-> n59; n28 !hr-> n58; n27 !hr-> n57; n26 !hr-> n56; n25 !hr-> n55; n24 !hr-> n54; n23 !hr-> n53; n22 !hr-> n52; n21 !hr-> n51; n20 !hr-> n50; n19 !hr-> n49; n18 !hr-> n48; n17 !hr-> n47; n16 !hr-> n46; n15 !hr-> n45; n14 !hr-> n44; n13 !hr-> n43; n12 !hr-> n42; n11 !hr-> n41; n10 !hr-> n40; n9 !hr-> n39; n8 !hr-> n38; n7 !hr-> n37; n6 !hr-> n36; n5 !hr-> n35; n4 !hr-> n34; n3 !hr-> n33; n2 !hr-> n32; n1 !hr-> n31;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n33).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n34).
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n35).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n36). 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_30 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 n57 n58 n59 n60 (HeapR: heapR),
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 ->
 n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 -> n29 <> 0 -> n30 <> 0 -> 
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> n1<>n29 -> n1<>n30 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> n2<>n29 -> n2<>n30 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> n3<>n29 -> n3<>n30 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> n4<>n29 -> n4<>n30 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> n5<>n29 -> n5<>n30 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> n6<>n29 -> n6<>n30 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> n7<>n29 -> n7<>n30 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> n8<>n29 -> n8<>n30 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> n9<>n29 -> n9<>n30 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> n10<>n29 -> n10<>n30 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> n11<>n29 -> n11<>n30 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> n12<>n29 -> n12<>n30 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> n13<>n29 -> n13<>n30 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> n14<>n29 -> n14<>n30 ->
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> n15<>n29 -> n15<>n30 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> n16<>n29 -> n16<>n30 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> n17<>n29 -> n17<>n30 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> n18<>n29 -> n18<>n30 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> n19<>n29 -> n19<>n30 -> 
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> n20<>n29 -> n20<>n30 -> 
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> n21<>n29 -> n21<>n30 -> 
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> n22<>n29 -> n22<>n30 -> 
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> n23<>n29 -> n23<>n30 -> 
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 -> n2<>n29 -> n24<>n30 -> 
 n25<>n26 -> n25<>n27 -> n25<>n28 -> n25<>n29 -> n25<>n30 -> 
 n26<>n27 -> n26<>n28 -> n26<>n29 -> n26<>n30 -> 
 n27<>n28 -> n27<>n29 -> n27<>n30 ->
 n28<>n29 -> n28<>n30 -> 
 n29<>n30 -> 

 exists k ,( n30 !hr-> n60; n29 !hr-> n59; n28 !hr-> n58; n27 !hr-> n57; n26 !hr-> n56; n25 !hr-> n55; n24 !hr-> n54; n23 !hr-> n53; n22 !hr-> n52; n21 !hr-> n51; n20 !hr-> n50; n19 !hr-> n49; n18 !hr-> n48; n17 !hr-> n47; n16 !hr-> n46; n15 !hr-> n45; n14 !hr-> n44; n13 !hr-> n43; n12 !hr-> n42; n11 !hr-> n41; n10 !hr-> n40; n9 !hr-> n39; n8 !hr-> n38; n7 !hr-> n37; n6 !hr-> n36; n5 !hr-> n35; n4 !hr-> n34; n3 !hr-> n33; n2 !hr-> n32; n1 !hr-> n31;  HeapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n31).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n32).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n33).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n34). 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.
Qed.


Lemma SafeinHr4_32_ : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 n57 n58 n59 n60 n61 n62 n63 n64 n65
                    n66 n67 n68 ,
 in_list_list [v2o n6; v2o n5; v2o n4; v2o n3] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 ->
 n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 -> n29 <> 0 -> n30 <> 0 -> n31 <> 0 -> n32 <> 0 -> n33 <> 0 -> n34 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> n1<>n29 -> n1<>n30 -> n1<>n31 -> n1<>n32 -> n1<>n33 -> n1<>n34 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> n2<>n29 -> n2<>n30 -> n2<>n31 -> n2<>n32 -> n2<>n33 -> n2<>n34 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> n3<>n29 -> n3<>n30 -> n3<>n31 -> n3<>n32 -> n3<>n33 -> n3<>n34 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> n4<>n29 -> n4<>n30 -> n4<>n31 -> n4<>n32 -> n4<>n33 -> n4<>n34 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> n5<>n29 -> n5<>n30 -> n5<>n31 -> n5<>n32 -> n5<>n33 -> n5<>n34 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> n6<>n29 -> n6<>n30 -> n6<>n31 -> n6<>n32 -> n6<>n33 -> n6<>n34 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> n7<>n29 -> n7<>n30 -> n7<>n31 -> n7<>n32 -> n7<>n33 -> n7<>n34 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> n8<>n29 -> n8<>n30 -> n8<>n31 -> n8<>n32 -> n8<>n33 -> n8<>n34 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> n9<>n29 -> n9<>n30 -> n9<>n31 -> n9<>n32 -> n9<>n33 -> n9<>n34 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> n10<>n29 -> n10<>n30 -> n10<>n31 -> n10<>n32 -> n10<>n33 -> n10<>n34 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> n11<>n29 -> n11<>n30 -> n11<>n31 -> n11<>n32 -> n11<>n33 -> n11<>n34 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> n12<>n29 -> n12<>n30 -> n12<>n31 -> n12<>n32 -> n12<>n33 -> n12<>n34 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> n13<>n29 -> n13<>n30 -> n13<>n31 -> n13<>n32 -> n13<>n33 -> n13<>n34 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> n14<>n29 -> n14<>n30 -> n14<>n31 -> n14<>n32 -> n14<>n33 -> n14<>n34 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> n15<>n29 -> n15<>n30 -> n15<>n31 -> n15<>n32 -> n15<>n33 -> n15<>n34 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> n16<>n29 -> n16<>n30 -> n16<>n31 -> n16<>n32 -> n16<>n33 -> n16<>n34 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> n17<>n29 -> n17<>n30 -> n17<>n31 -> n17<>n32 -> n17<>n33 -> n17<>n34 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> n18<>n29 -> n18<>n30 -> n18<>n31 -> n18<>n32 -> n18<>n33 -> n18<>n34 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> n19<>n29 -> n19<>n30 -> n19<>n31 -> n19<>n32 -> n19<>n33 -> n19<>n34 -> 
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> n20<>n29 -> n20<>n30 -> n20<>n31 -> n20<>n32 -> n20<>n33 -> n20<>n34 -> 
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> n21<>n29 -> n21<>n30 -> n21<>n31 -> n21<>n32 -> n21<>n33 -> n21<>n34 -> 
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> n22<>n29 -> n22<>n30 -> n22<>n31 -> n22<>n32 -> n22<>n33 -> n22<>n34 -> 
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> n23<>n29 -> n23<>n30 -> n23<>n31 -> n23<>n32 -> n23<>n33 -> n23<>n34 -> 
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 -> n2<>n29 -> n24<>n30 -> n24<>n31 -> n24<>n32 -> n24<>n33 -> n24<>n34 -> 
 n25<>n26 -> n25<>n27 -> n25<>n28 -> n25<>n29 -> n25<>n30 -> n25<>n31 -> n25<>n32 -> n25<>n33 -> n25<>n34 -> 
 n26<>n27 -> n26<>n28 -> n26<>n29 -> n26<>n30 -> n26<>n31 -> n26<>n32 -> n26<>n33 -> n26<>n34 -> 
 n27<>n28 -> n27<>n29 -> n27<>n30 -> n27<>n31 -> n27<>n32 -> n27<>n33 -> n27<>n34 -> 
 n28<>n29 -> n28<>n30 -> n28<>n31 -> n28<>n32 -> n28<>n33 -> n28<>n34 -> 
 n29<>n30 -> n29<>n31 -> n29<>n32 -> n29<>n33 -> n29<>n34 -> 
 n30<>n31 -> n30<>n32 -> n30<>n33 -> n30<>n34 ->
 n31<>n32 -> n31<>n33 -> n31<>n34 ->  
 n32<>n33 -> n32<>n34 -> 
 n33<>n34 -> 

 exists k ,( n34 !hr-> n68; n33 !hr-> n67; n32 !hr-> n66; n31 !hr-> n65; n30 !hr-> n64; n29 !hr-> n63; n28 !hr-> n62; n27 !hr-> n61; n26 !hr-> n60; n25 !hr-> n59; n24 !hr-> n58; n23 !hr-> n57; n22 !hr-> n56; n21 !hr-> n55; n20 !hr-> n54; n19 !hr-> n53; n18 !hr-> n52; n17 !hr-> n51; n16 !hr-> n50; n15 !hr-> n49; n14 !hr-> n48; n13 !hr-> n47; n12 !hr-> n46; n11 !hr-> n45; n10 !hr-> n44; n9 !hr-> n43; n8 !hr-> n42; n7 !hr-> n41; n6 !hr-> n40; n5 !hr-> n39; n4 !hr-> n38; n3 !hr-> n37; n2 !hr-> n36; n1 !hr-> n35;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n37).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n38).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n39).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n40). 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_33 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 n57 n58 n59 n60 n61 n62 n63 n64 n65
                    n66 ,
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 ->
 n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 -> n29 <> 0 -> n30 <> 0 -> n31 <> 0 -> n32 <> 0 -> n33 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> n1<>n29 -> n1<>n30 -> n1<>n31 -> n1<>n32 -> n1<>n33 ->
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> n2<>n29 -> n2<>n30 -> n2<>n31 -> n2<>n32 -> n2<>n33 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> n3<>n29 -> n3<>n30 -> n3<>n31 -> n3<>n32 -> n3<>n33 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> n4<>n29 -> n4<>n30 -> n4<>n31 -> n4<>n32 -> n4<>n33 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> n5<>n29 -> n5<>n30 -> n5<>n31 -> n5<>n32 -> n5<>n33 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> n6<>n29 -> n6<>n30 -> n6<>n31 -> n6<>n32 -> n6<>n33 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> n7<>n29 -> n7<>n30 -> n7<>n31 -> n7<>n32 -> n7<>n33 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> n8<>n29 -> n8<>n30 -> n8<>n31 -> n8<>n32 -> n8<>n33 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> n9<>n29 -> n9<>n30 -> n9<>n31 -> n9<>n32 -> n9<>n33 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> n10<>n29 -> n10<>n30 -> n10<>n31 -> n10<>n32 -> n10<>n33 ->
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> n11<>n29 -> n11<>n30 -> n11<>n31 -> n11<>n32 -> n11<>n33 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> n12<>n29 -> n12<>n30 -> n12<>n31 -> n12<>n32 -> n12<>n33 ->
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> n13<>n29 -> n13<>n30 -> n13<>n31 -> n13<>n32 -> n13<>n33 ->
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> n14<>n29 -> n14<>n30 -> n14<>n31 -> n14<>n32 -> n14<>n33 ->
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> n15<>n29 -> n15<>n30 -> n15<>n31 -> n15<>n32 -> n15<>n33 ->
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> n16<>n29 -> n16<>n30 -> n16<>n31 -> n16<>n32 -> n16<>n33 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> n17<>n29 -> n17<>n30 -> n17<>n31 -> n17<>n32 -> n17<>n33 ->
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> n18<>n29 -> n18<>n30 -> n18<>n31 -> n18<>n32 -> n18<>n33 ->
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> n19<>n29 -> n19<>n30 -> n19<>n31 -> n19<>n32 -> n19<>n33 ->
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> n20<>n29 -> n20<>n30 -> n20<>n31 -> n20<>n32 -> n20<>n33 ->
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> n21<>n29 -> n21<>n30 -> n21<>n31 -> n21<>n32 -> n21<>n33 ->
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> n22<>n29 -> n22<>n30 -> n22<>n31 -> n22<>n32 -> n22<>n33 ->
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> n23<>n29 -> n23<>n30 -> n23<>n31 -> n23<>n32 -> n23<>n33 -> 
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 -> n2<>n29 -> n24<>n30 -> n24<>n31 -> n24<>n32 -> n24<>n33 ->
 n25<>n26 -> n25<>n27 -> n25<>n28 -> n25<>n29 -> n25<>n30 -> n25<>n31 -> n25<>n32 -> n25<>n33 ->
 n26<>n27 -> n26<>n28 -> n26<>n29 -> n26<>n30 -> n26<>n31 -> n26<>n32 -> n26<>n33 ->
 n27<>n28 -> n27<>n29 -> n27<>n30 -> n27<>n31 -> n27<>n32 -> n27<>n33 ->
 n28<>n29 -> n28<>n30 -> n28<>n31 -> n28<>n32 -> n28<>n33 ->
 n29<>n30 -> n29<>n31 -> n29<>n32 -> n29<>n33 ->
 n30<>n31 -> n30<>n32 -> n30<>n33 ->
 n31<>n32 -> n31<>n33 ->
 n32<>n33 ->

 exists k ,( n33 !hr-> n66; n32 !hr-> n65; n31 !hr-> n64; n30 !hr-> n63; n29 !hr-> n62; n28 !hr-> n61; n27 !hr-> n60; n26 !hr-> n59; n25 !hr-> n58; n24 !hr-> n57; n23 !hr-> n56; n22 !hr-> n55; n21 !hr-> n54; n20 !hr-> n53; n19 !hr-> n52; n18 !hr-> n51; n17 !hr-> n50; n16 !hr-> n49; n15 !hr-> n48; n14 !hr-> n47; n13 !hr-> n46; n12 !hr-> n45; n11 !hr-> n44; n10 !hr-> n43; n9 !hr-> n42; n8 !hr-> n41; n7 !hr-> n40; n6 !hr-> n39; n5 !hr-> n38; n4 !hr-> n37; n3 !hr-> n36; n2 !hr-> n35; n1 !hr-> n34;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n34).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n35).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n36).
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n37). 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_34 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 n57 n58 n59 n60 n61 n62 n63 n64 n65
                    n66 n67 n68 ,
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 ->
 n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 -> n29 <> 0 -> n30 <> 0 -> n31 <> 0 -> n32 <> 0 -> n33 <> 0 -> n34 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> n1<>n29 -> n1<>n30 -> n1<>n31 -> n1<>n32 -> n1<>n33 -> n1<>n34 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> n2<>n29 -> n2<>n30 -> n2<>n31 -> n2<>n32 -> n2<>n33 -> n2<>n34 -> 
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> n3<>n29 -> n3<>n30 -> n3<>n31 -> n3<>n32 -> n3<>n33 -> n3<>n34 -> 
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> n4<>n29 -> n4<>n30 -> n4<>n31 -> n4<>n32 -> n4<>n33 -> n4<>n34 -> 
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> n5<>n29 -> n5<>n30 -> n5<>n31 -> n5<>n32 -> n5<>n33 -> n5<>n34 -> 
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> n6<>n29 -> n6<>n30 -> n6<>n31 -> n6<>n32 -> n6<>n33 -> n6<>n34 -> 
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> n7<>n29 -> n7<>n30 -> n7<>n31 -> n7<>n32 -> n7<>n33 -> n7<>n34 -> 
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> n8<>n29 -> n8<>n30 -> n8<>n31 -> n8<>n32 -> n8<>n33 -> n8<>n34 -> 
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> n9<>n29 -> n9<>n30 -> n9<>n31 -> n9<>n32 -> n9<>n33 -> n9<>n34 -> 
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> n10<>n29 -> n10<>n30 -> n10<>n31 -> n10<>n32 -> n10<>n33 -> n10<>n34 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> n11<>n29 -> n11<>n30 -> n11<>n31 -> n11<>n32 -> n11<>n33 -> n11<>n34 -> 
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> n12<>n29 -> n12<>n30 -> n12<>n31 -> n12<>n32 -> n12<>n33 -> n12<>n34 -> 
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> n13<>n29 -> n13<>n30 -> n13<>n31 -> n13<>n32 -> n13<>n33 -> n13<>n34 -> 
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> n14<>n29 -> n14<>n30 -> n14<>n31 -> n14<>n32 -> n14<>n33 -> n14<>n34 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> n15<>n29 -> n15<>n30 -> n15<>n31 -> n15<>n32 -> n15<>n33 -> n15<>n34 -> 
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> n16<>n29 -> n16<>n30 -> n16<>n31 -> n16<>n32 -> n16<>n33 -> n16<>n34 -> 
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> n17<>n29 -> n17<>n30 -> n17<>n31 -> n17<>n32 -> n17<>n33 -> n17<>n34 -> 
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> n18<>n29 -> n18<>n30 -> n18<>n31 -> n18<>n32 -> n18<>n33 -> n18<>n34 -> 
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> n19<>n29 -> n19<>n30 -> n19<>n31 -> n19<>n32 -> n19<>n33 -> n19<>n34 -> 
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> n20<>n29 -> n20<>n30 -> n20<>n31 -> n20<>n32 -> n20<>n33 -> n20<>n34 -> 
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> n21<>n29 -> n21<>n30 -> n21<>n31 -> n21<>n32 -> n21<>n33 -> n21<>n34 -> 
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> n22<>n29 -> n22<>n30 -> n22<>n31 -> n22<>n32 -> n22<>n33 -> n22<>n34 -> 
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> n23<>n29 -> n23<>n30 -> n23<>n31 -> n23<>n32 -> n23<>n33 -> n23<>n34 -> 
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 -> n2<>n29 -> n24<>n30 -> n24<>n31 -> n24<>n32 -> n24<>n33 -> n24<>n34 -> 
 n25<>n26 -> n25<>n27 -> n25<>n28 -> n25<>n29 -> n25<>n30 -> n25<>n31 -> n25<>n32 -> n25<>n33 -> n25<>n34 -> 
 n26<>n27 -> n26<>n28 -> n26<>n29 -> n26<>n30 -> n26<>n31 -> n26<>n32 -> n26<>n33 -> n26<>n34 -> 
 n27<>n28 -> n27<>n29 -> n27<>n30 -> n27<>n31 -> n27<>n32 -> n27<>n33 -> n27<>n34 -> 
 n28<>n29 -> n28<>n30 -> n28<>n31 -> n28<>n32 -> n28<>n33 -> n28<>n34 -> 
 n29<>n30 -> n29<>n31 -> n29<>n32 -> n29<>n33 -> n29<>n34 -> 
 n30<>n31 -> n30<>n32 -> n30<>n33 -> n30<>n34 ->
 n31<>n32 -> n31<>n33 -> n31<>n34 ->  
 n32<>n33 -> n32<>n34 -> 
 n33<>n34 -> 

 exists k ,( n34 !hr-> n68; n33 !hr-> n67; n32 !hr-> n66; n31 !hr-> n65; n30 !hr-> n64; n29 !hr-> n63; n28 !hr-> n62; n27 !hr-> n61; n26 !hr-> n60; n25 !hr-> n59; n24 !hr-> n58; n23 !hr-> n57; n22 !hr-> n56; n21 !hr-> n55; n20 !hr-> n54; n19 !hr-> n53; n18 !hr-> n52; n17 !hr-> n51; n16 !hr-> n50; n15 !hr-> n49; n14 !hr-> n48; n13 !hr-> n47; n12 !hr-> n46; n11 !hr-> n45; n10 !hr-> n44; n9 !hr-> n43; n8 !hr-> n42; n7 !hr-> n41; n6 !hr-> n40; n5 !hr-> n39; n4 !hr-> n38; n3 !hr-> n37; n2 !hr-> n36; n1 !hr-> n35;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n35).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n36).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  destruct H. rewrite H. 
  exists (Some n37).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n38). 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_40 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 n57 n58 n59 n60 n61 n62 n63 n64 n65
                    n66 n67 n68 n69 n70 n71 n72 n73 n74 n75 n76 n77 n78 n79 n80 ,
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> 
 n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 -> n29 <> 0 -> n30 <> 0 -> n31 <> 0 -> n32 <> 0 -> n33 <> 0 -> n34 <> 0 -> n35 <> 0 -> n36 <> 0 -> n37 <> 0 -> n38 <> 0 -> n39 <> 0 -> n40 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> n1<>n29 -> n1<>n30 -> n1<>n31 -> n1<>n32 -> n1<>n33 -> n1<>n34 -> n1<>n35 -> n1<>n36 -> n1<>n37 -> n1<>n38 -> n1<>n39 -> n1<>n40 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> n2<>n29 -> n2<>n30 -> n2<>n31 -> n2<>n32 -> n2<>n33 -> n2<>n34 -> n2<>n35 -> n2<>n36 -> n2<>n37 -> n2<>n38 -> n2<>n39 -> n2<>n40 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> n3<>n29 -> n3<>n30 -> n3<>n31 -> n3<>n32 -> n3<>n33 -> n3<>n34 -> n3<>n35 -> n3<>n36 -> n3<>n37 -> n3<>n38 -> n3<>n39 -> n3<>n40 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> n4<>n29 -> n4<>n30 -> n4<>n31 -> n4<>n32 -> n4<>n33 -> n4<>n34 -> n4<>n35 -> n4<>n36 -> n4<>n37 -> n4<>n38 -> n4<>n39 -> n4<>n40 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> n5<>n29 -> n5<>n30 -> n5<>n31 -> n5<>n32 -> n5<>n33 -> n5<>n34 -> n5<>n35 -> n5<>n36 -> n5<>n37 -> n5<>n38 -> n5<>n39 -> n5<>n40 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> n6<>n29 -> n6<>n30 -> n6<>n31 -> n6<>n32 -> n6<>n33 -> n6<>n34 -> n6<>n35 -> n6<>n36 -> n6<>n37 -> n6<>n38 -> n6<>n39 -> n6<>n40 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> n7<>n29 -> n7<>n30 -> n7<>n31 -> n7<>n32 -> n7<>n33 -> n7<>n34 -> n7<>n35 -> n7<>n36 -> n7<>n37 -> n7<>n38 -> n7<>n39 -> n7<>n40 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> n8<>n29 -> n8<>n30 -> n8<>n31 -> n8<>n32 -> n8<>n33 -> n8<>n34 -> n8<>n35 -> n8<>n36 -> n8<>n37 -> n8<>n38 -> n8<>n39 -> n8<>n40 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> n9<>n29 -> n9<>n30 -> n9<>n31 -> n9<>n32 -> n9<>n33 -> n9<>n34 -> n9<>n35 -> n9<>n36 -> n9<>n37 -> n9<>n38 -> n9<>n39 -> n9<>n40 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> n10<>n29 -> n10<>n30 -> n10<>n31 -> n10<>n32 -> n10<>n33 -> n10<>n34 -> n10<>n35 -> n10<>n36 -> n10<>n37 -> n10<>n38 -> n10<>n39 -> n10<>n40 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> n11<>n29 -> n11<>n30 -> n11<>n31 -> n11<>n32 -> n11<>n33 -> n11<>n34 -> n11<>n35 -> n11<>n36 -> n11<>n37 -> n11<>n38 -> n11<>n39 -> n11<>n40 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> n12<>n29 -> n12<>n30 -> n12<>n31 -> n12<>n32 -> n12<>n33 -> n12<>n34 -> n12<>n35 -> n12<>n36 -> n12<>n37 -> n12<>n38 -> n12<>n39 -> n12<>n40 ->
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> n13<>n29 -> n13<>n30 -> n13<>n31 -> n13<>n32 -> n13<>n33 -> n13<>n34 -> n13<>n35 -> n13<>n36 -> n13<>n37 -> n13<>n38 -> n13<>n39 -> n13<>n40 ->
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> n14<>n29 -> n14<>n30 -> n14<>n31 -> n14<>n32 -> n14<>n33 -> n14<>n34 -> n14<>n35 -> n14<>n36 -> n14<>n37 -> n14<>n38 -> n14<>n39 -> n14<>n40 -> 
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> n15<>n29 -> n15<>n30 -> n15<>n31 -> n15<>n32 -> n15<>n33 -> n15<>n34 -> n15<>n35 -> n15<>n36 -> n15<>n37 -> n15<>n38 -> n15<>n39 -> n15<>n40 ->
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> n16<>n29 -> n16<>n30 -> n16<>n31 -> n16<>n32 -> n16<>n33 -> n16<>n34 -> n16<>n35 -> n16<>n36 -> n16<>n37 -> n16<>n38 -> n16<>n39 -> n16<>n40 ->
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> n17<>n29 -> n17<>n30 -> n17<>n31 -> n17<>n32 -> n17<>n33 -> n17<>n34 -> n17<>n35 -> n17<>n36 -> n17<>n37 -> n17<>n38 -> n17<>n39 -> n17<>n40 ->
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> n18<>n29 -> n18<>n30 -> n18<>n31 -> n18<>n32 -> n18<>n33 -> n18<>n34 -> n18<>n35 -> n18<>n36 -> n18<>n37 -> n18<>n38 -> n18<>n39 -> n18<>n40 ->
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> n19<>n29 -> n19<>n30 -> n19<>n31 -> n19<>n32 -> n19<>n33 -> n19<>n34 -> n19<>n35 -> n19<>n36 -> n19<>n37 -> n19<>n38 -> n19<>n39 -> n19<>n40 ->
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> n20<>n29 -> n20<>n30 -> n20<>n31 -> n20<>n32 -> n20<>n33 -> n20<>n34 -> n20<>n35 -> n20<>n36 -> n20<>n37 -> n20<>n38 -> n20<>n39 -> n20<>n40 ->
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> n21<>n29 -> n21<>n30 -> n21<>n31 -> n21<>n32 -> n21<>n33 -> n21<>n34 -> n21<>n35 -> n21<>n36 -> n21<>n37 -> n21<>n38 -> n21<>n39 -> n21<>n40 ->
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> n22<>n29 -> n22<>n30 -> n22<>n31 -> n22<>n32 -> n22<>n33 -> n22<>n34 -> n22<>n35 -> n22<>n36 -> n22<>n37 -> n22<>n38 -> n22<>n39 -> n22<>n40 ->
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> n23<>n29 -> n23<>n30 -> n23<>n31 -> n23<>n32 -> n23<>n33 -> n23<>n34 -> n23<>n35 -> n23<>n36 -> n23<>n37 -> n23<>n38 -> n23<>n39 -> n23<>n40 ->
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 -> n24<>n29 -> n24<>n30 -> n24<>n31 -> n24<>n32 -> n24<>n33 -> n24<>n34 -> n24<>n35 -> n24<>n36 -> n24<>n37 -> n24<>n38 -> n24<>n39 -> n24<>n40 ->
 n25<>n26 -> n25<>n27 -> n25<>n28 -> n25<>n29 -> n25<>n30 -> n25<>n31 -> n25<>n32 -> n25<>n33 -> n25<>n34 -> n25<>n35 -> n25<>n36 -> n25<>n37 -> n25<>n38 -> n25<>n39 -> n25<>n40 ->
 n26<>n27 -> n26<>n28 -> n26<>n29 -> n26<>n30 -> n26<>n31 -> n26<>n32 -> n26<>n33 -> n26<>n34 -> n26<>n35 -> n26<>n36 -> n26<>n37 -> n26<>n38 -> n26<>n39 -> n26<>n40 ->
 n27<>n28 -> n27<>n29 -> n27<>n30 -> n27<>n31 -> n27<>n32 -> n27<>n33 -> n27<>n34 -> n27<>n35 -> n27<>n36 -> n27<>n37 -> n27<>n38 -> n27<>n39 -> n27<>n40 ->
 n28<>n29 -> n28<>n30 -> n28<>n31 -> n28<>n32 -> n28<>n33 -> n28<>n34 -> n28<>n35 -> n28<>n36 -> n28<>n37 -> n28<>n38 -> n28<>n39 -> n28<>n40 ->
 n29<>n30 -> n29<>n31 -> n29<>n32 -> n29<>n33 -> n29<>n34 -> n29<>n35 -> n29<>n36 -> n29<>n37 -> n29<>n38 -> n29<>n39 -> n29<>n40 ->
 n30<>n31 -> n30<>n32 -> n30<>n33 -> n30<>n34 -> n30<>n35 -> n30<>n36 -> n30<>n37 -> n30<>n38 -> n30<>n39 -> n30<>n40 ->
 n31<>n32 -> n31<>n33 -> n31<>n34 -> n31<>n35 -> n31<>n36 -> n31<>n37 -> n31<>n38 -> n31<>n39 -> n31<>n40 -> 
 n32<>n33 -> n32<>n34 -> n32<>n35 -> n32<>n36 -> n32<>n37 -> n32<>n38 -> n32<>n39 -> n32<>n40 ->
 n33<>n34 -> n33<>n35 -> n33<>n36 -> n33<>n37 -> n33<>n38 -> n33<>n39 -> n33<>n40 ->
 n34<>n35 -> n34<>n36 -> n34<>n37 -> n34<>n38 -> n34<>n39 -> n34<>n40 ->
 n35<>n36 -> n35<>n37 -> n35<>n38 -> n35<>n39 -> n35<>n40 ->
 n36<>n37 -> n36<>n38 -> n36<>n39 -> n36<>n40 ->
 n37<>n38 -> n37<>n39 -> n37<>n40 ->
 n38<>n39 -> n38<>n40 ->
 n39<>n40 ->

 exists k ,( n40 !hr-> n80; n39 !hr-> n79; n38 !hr-> n78; n37 !hr-> n77; n36 !hr-> n76; n35 !hr-> n75; n34 !hr-> n74; n33 !hr-> n73; n32 !hr-> n72; n31 !hr-> n71; n30 !hr-> n70; n29 !hr-> n69; n28 !hr-> n68; n27 !hr-> n67; n26 !hr-> n66; n25 !hr-> n65; n24 !hr-> n64; n23 !hr-> n63; n22 !hr-> n62; n21 !hr-> n61; n20 !hr-> n60; n19 !hr-> n59; n18 !hr-> n58; n17 !hr-> n57; n16 !hr-> n56; n15 !hr-> n55; n14 !hr-> n54; n13 !hr-> n53; n12 !hr-> n52; n11 !hr-> n51; n10 !hr-> n50; n9 !hr-> n49; n8 !hr-> n48; n7 !hr-> n47; n6 !hr-> n46; n5 !hr-> n45; n4 !hr-> n44; n3 !hr-> n43; n2 !hr-> n42; n1 !hr-> n41;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n41).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n42).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n43).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  rewrite H. 
  exists (Some n44). 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.
Qed.

Lemma SafeinHr4_46 : forall (l : option nat) n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19
                    n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 n41 n42
                    n43 n44 n45 n46 n47 n48 n49 n50 n51 n52 n53 n54 n55 n56 n57 n58 n59 n60 n61 n62 n63 n64 n65
                    n66 n67 n68 n69 n70 n71 n72 n73 n74 n75 n76 n77 n78 n79 n80 n81 n82 n83 n84 n85 n86 n87 n88
                    n89 n90 n91 n92,
 in_list_list [v2o n4; v2o n3; v2o n2; v2o n1] l = true ->
 n1 <> 0 -> n2 <> 0 -> n3 <> 0 -> n4 <> 0 -> n5 <> 0 -> n6 <> 0 -> n7 <> 0 -> n8 <> 0 -> n9 <> 0 -> n10 <> 0 -> n11 <> 0 -> n12 <> 0 -> n13 <> 0 -> n14 <> 0 -> n15 <> 0 -> n16 <> 0 -> n17 <> 0 -> n18 <> 0 -> n19 <> 0 -> n20 <> 0 -> n21 <> 0 -> 
 n22 <> 0 -> n23 <> 0 -> n24 <> 0 -> n25 <> 0 -> n26 <> 0 -> n27 <> 0 -> n28 <> 0 -> n29 <> 0 -> n30 <> 0 -> n31 <> 0 -> n32 <> 0 -> n33 <> 0 -> n34 <> 0 -> n35 <> 0 -> n36 <> 0 -> n37 <> 0 -> n38 <> 0 -> n39 <> 0 -> n40 <> 0 -> n41 <> 0 -> n42 <> 0 -> n43 <> 0 -> n44 <> 0 -> n45 <> 0 -> n46 <> 0 ->
 n1<>n2 -> n1<>n3 -> n1<>n4 -> n1<>n5 -> n1<>n6 -> n1<>n7 -> n1<>n8 -> n1<>n9 -> n1<>n10 -> n1<>n11 -> n1<>n12 -> n1<>n13 -> n1<>n14 -> n1<>n15 -> n1<>n16 -> n1<>n17 -> n1<>n18 -> n1<>n19 -> n1<>n20 -> n1<>n21 -> n1<>n22 -> n1<>n23 -> n1<>n24 -> n1<>n25 -> n1<>n26 -> n1<>n27 -> n1<>n28 -> n1<>n29 -> n1<>n30 -> n1<>n31 -> n1<>n32 -> n1<>n33 -> n1<>n34 -> n1<>n35 -> n1<>n36 -> n1<>n37 -> n1<>n38 -> n1<>n39 -> n1<>n40 -> n1<>n41 -> n1<>n42 -> n1<>n43 -> n1<>n44 -> n1<>n45 -> n1<>n46 -> 
 n2<>n3 -> n2<>n4 -> n2<>n5 -> n2<>n6 -> n2<>n7 -> n2<>n8 -> n2<>n9 -> n2<>n10 -> n2<>n11 -> n2<>n12 -> n2<>n13 -> n2<>n14 -> n2<>n15 -> n2<>n16 -> n2<>n17 -> n2<>n18 -> n2<>n19 -> n2<>n20 -> n2<>n21 -> n2<>n22 -> n2<>n23 -> n2<>n24 -> n2<>n25 -> n2<>n26 -> n2<>n27 -> n2<>n28 -> n2<>n29 -> n2<>n30 -> n2<>n31 -> n2<>n32 -> n2<>n33 -> n2<>n34 -> n2<>n35 -> n2<>n36 -> n2<>n37 -> n2<>n38 -> n2<>n39 -> n2<>n40 -> n2<>n41 -> n2<>n42 -> n2<>n43 -> n2<>n44 -> n2<>n45 -> n2<>n46 ->
 n3<>n4 -> n3<>n5 -> n3<>n6 -> n3<>n7 -> n3<>n8 -> n3<>n9 -> n3<>n10 -> n3<>n11 -> n3<>n12 -> n3<>n13 -> n3<>n14 -> n3<>n15 -> n3<>n16 -> n3<>n17 -> n3<>n18 -> n3<>n19 -> n3<>n20 -> n3<>n21 -> n3<>n22 -> n3<>n23 -> n3<>n24 -> n3<>n25 -> n3<>n26 -> n3<>n27 -> n3<>n28 -> n3<>n29 -> n3<>n30 -> n3<>n31 -> n3<>n32 -> n3<>n33 -> n3<>n34 -> n3<>n35 -> n3<>n36 -> n3<>n37 -> n3<>n38 -> n3<>n39 -> n3<>n40 -> n3<>n41 -> n3<>n42 -> n3<>n43 -> n3<>n44 -> n3<>n45 -> n3<>n46 ->
 n4<>n5 -> n4<>n6 -> n4<>n7 -> n4<>n8 -> n4<>n9 -> n4<>n10 -> n4<>n11 -> n4<>n12 -> n4<>n13 -> n4<>n14 -> n4<>n15 -> n4<>n16 -> n4<>n17 -> n4<>n18 -> n4<>n19 -> n4<>n20 -> n4<>n21 -> n4<>n22 -> n4<>n23 -> n4<>n24 -> n4<>n25 -> n4<>n26 -> n4<>n27 -> n4<>n28 -> n4<>n29 -> n4<>n30 -> n4<>n31 -> n4<>n32 -> n4<>n33 -> n4<>n34 -> n4<>n35 -> n4<>n36 -> n4<>n37 -> n4<>n38 -> n4<>n39 -> n4<>n40 -> n4<>n41 -> n4<>n42 -> n4<>n43 -> n4<>n44 -> n4<>n45 -> n4<>n46 ->
 n5<>n6 -> n5<>n7 -> n5<>n8 -> n5<>n9 -> n5<>n10 -> n5<>n11 -> n5<>n12 -> n5<>n13 -> n5<>n14 -> n5<>n15 -> n5<>n16 -> n5<>n17 -> n5<>n18 -> n5<>n19 -> n5<>n20 -> n5<>n21 -> n5<>n22 -> n5<>n23 -> n5<>n24 -> n5<>n25 -> n5<>n26 -> n5<>n27 -> n5<>n28 -> n5<>n29 -> n5<>n30 -> n5<>n31 -> n5<>n32 -> n5<>n33 -> n5<>n34 -> n5<>n35 -> n5<>n36 -> n5<>n37 -> n5<>n38 -> n5<>n39 -> n5<>n40 -> n5<>n41 -> n5<>n42 -> n5<>n43 -> n5<>n44 -> n5<>n45 -> n5<>n46 ->
 n6<>n7 -> n6<>n8 -> n6<>n9 -> n6<>n10 -> n6<>n11 -> n6<>n12 -> n6<>n13 -> n6<>n14 -> n6<>n15 -> n6<>n16 -> n6<>n17 -> n6<>n18 -> n6<>n19 -> n6<>n20 -> n6<>n21 -> n6<>n22 -> n6<>n23 -> n6<>n24 -> n6<>n25 -> n6<>n26 -> n6<>n27 -> n6<>n28 -> n6<>n29 -> n6<>n30 -> n6<>n31 -> n6<>n32 -> n6<>n33 -> n6<>n34 -> n6<>n35 -> n6<>n36 -> n6<>n37 -> n6<>n38 -> n6<>n39 -> n6<>n40 -> n6<>n41 -> n6<>n42 -> n6<>n43 -> n6<>n44 -> n6<>n45 -> n6<>n46 ->
 n7<>n8 -> n7<>n9 -> n7<>n10 -> n7<>n11 -> n7<>n12 -> n7<>n13 -> n7<>n14 -> n7<>n15 -> n7<>n16 -> n7<>n17 -> n7<>n18 -> n7<>n19 -> n7<>n20 -> n7<>n21 -> n7<>n22 -> n7<>n23 -> n7<>n24 -> n7<>n25 -> n7<>n26 -> n7<>n27 -> n7<>n28 -> n7<>n29 -> n7<>n30 -> n7<>n31 -> n7<>n32 -> n7<>n33 -> n7<>n34 -> n7<>n35 -> n7<>n36 -> n7<>n37 -> n7<>n38 -> n7<>n39 -> n7<>n40 -> n7<>n41 -> n7<>n42 -> n7<>n43 -> n7<>n44 -> n7<>n45 -> n7<>n46 ->
 n8<>n9 -> n8<>n10 -> n5<>n11 -> n8<>n12 -> n8<>n13 -> n8<>n14 -> n8<>n15 -> n8<>n16 -> n8<>n17 -> n8<>n18 -> n8<>n19 -> n8<>n20 -> n8<>n21 -> n8<>n22 -> n8<>n23 -> n8<>n24 -> n8<>n25 -> n8<>n26 -> n8<>n27 -> n8<>n28 -> n8<>n29 -> n8<>n30 -> n8<>n31 -> n8<>n32 -> n8<>n33 -> n8<>n34 -> n8<>n35 -> n8<>n36 -> n8<>n37 -> n8<>n38 -> n8<>n39 -> n8<>n40 -> n8<>n41 -> n8<>n42 -> n8<>n43 -> n8<>n44 -> n8<>n45 -> n8<>n46 ->
 n9<>n10 -> n9<>n11 -> n9<>n12 -> n9<>n13 -> n9<>n14 -> n9<>n15 -> n9<>n16 -> n9<>n17 -> n9<>n18 -> n9<>n19 -> n9<>n20 -> n9<>n21 -> n9<>n22 -> n9<>n23 -> n9<>n24 -> n9<>n25 -> n9<>n26 -> n9<>n27 -> n9<>n28 -> n9<>n29 -> n9<>n30 -> n9<>n31 -> n9<>n32 -> n9<>n33 -> n9<>n34 -> n9<>n35 -> n9<>n36 -> n9<>n37 -> n9<>n38 -> n9<>n39 -> n9<>n40 -> n9<>n41 -> n9<>n42 -> n9<>n43 -> n9<>n44 -> n9<>n45 -> n9<>n46 ->
 n10<>n11 -> n10<>n12 -> n10<>n13 -> n10<>n14 -> n10<>n15 -> n10<>n16 -> n10<>n17 -> n10<>n18 -> n10<>n19 -> n10<>n20 -> n10<>n21 -> n10<>n22 -> n10<>n23 -> n10<>n24 -> n10<>n25 -> n10<>n26 -> n10<>n27 -> n10<>n28 -> n10<>n29 -> n10<>n30 -> n10<>n31 -> n10<>n32 -> n10<>n33 -> n10<>n34 -> n10<>n35 -> n10<>n36 -> n10<>n37 -> n10<>n38 -> n10<>n39 -> n10<>n40 -> n10<>n41 -> n10<>n42 -> n10<>n43 -> n10<>n44 -> n10<>n45 -> n10<>n46 -> 
 n11<>n12 -> n11<>n13 -> n11<>n14 -> n11<>n15 -> n11<>n16 -> n11<>n17 -> n11<>n18 -> n11<>n19 -> n11<>n20 -> n11<>n21 -> n11<>n22 -> n11<>n23 -> n11<>n24 -> n11<>n25 -> n11<>n26 -> n11<>n27 -> n11<>n28 -> n11<>n29 -> n11<>n30 -> n11<>n31 -> n11<>n32 -> n11<>n33 -> n11<>n34 -> n11<>n35 -> n11<>n36 -> n11<>n37 -> n11<>n38 -> n11<>n39 -> n11<>n40 -> n11<>n41 -> n11<>n42 -> n11<>n43 -> n11<>n44 -> n11<>n45 -> n11<>n46 ->
 n12<>n13 -> n12<>n14 -> n12<>n15 -> n12<>n16 -> n12<>n17 -> n12<>n18 -> n12<>n19 -> n12<>n20 -> n12<>n21 -> n12<>n22 -> n12<>n23 -> n12<>n24 -> n12<>n25 -> n12<>n26 -> n12<>n27 -> n12<>n28 -> n12<>n29 -> n12<>n30 -> n12<>n31 -> n12<>n32 -> n12<>n33 -> n12<>n34 -> n12<>n35 -> n12<>n36 -> n12<>n37 -> n12<>n38 -> n12<>n39 -> n12<>n40 -> n12<>n41 -> n12<>n42 -> n12<>n43 -> n12<>n44 -> n12<>n45 -> n12<>n46 ->
 n13<>n14 -> n13<>n15 -> n13<>n16 -> n13<>n17 -> n13<>n18 -> n13<>n19 -> n13<>n20 -> n13<>n21 -> n13<>n22 -> n13<>n23 -> n13<>n24 -> n13<>n25 -> n13<>n26 -> n13<>n27 -> n13<>n28 -> n13<>n29 -> n13<>n30 -> n13<>n31 -> n13<>n32 -> n13<>n33 -> n13<>n34 -> n13<>n35 -> n13<>n36 -> n13<>n37 -> n13<>n38 -> n13<>n39 -> n13<>n40 -> n13<>n41 -> n13<>n42 -> n13<>n43 -> n13<>n44 -> n13<>n45 -> n13<>n46 ->
 n14<>n15 -> n14<>n16 -> n14<>n17 -> n14<>n18 -> n14<>n19 -> n14<>n20 -> n14<>n21 -> n14<>n22 -> n14<>n23 -> n14<>n24 -> n14<>n25 -> n14<>n26 -> n14<>n27 -> n14<>n28 -> n14<>n29 -> n14<>n30 -> n14<>n31 -> n14<>n32 -> n14<>n33 -> n14<>n34 -> n14<>n35 -> n14<>n36 -> n14<>n37 -> n14<>n38 -> n14<>n39 -> n14<>n40 -> n14<>n41 -> n14<>n42 -> n14<>n43 -> n14<>n44 -> n14<>n45 -> n14<>n46 ->
 n15<>n16 -> n15<>n17 -> n15<>n18 -> n15<>n19 -> n15<>n20 -> n15<>n21 -> n15<>n22 -> n15<>n23 -> n15<>n24 -> n15<>n25 -> n15<>n26 -> n15<>n27 -> n15<>n28 -> n15<>n29 -> n15<>n30 -> n15<>n31 -> n15<>n32 -> n15<>n33 -> n15<>n34 -> n15<>n35 -> n15<>n36 -> n15<>n37 -> n15<>n38 -> n15<>n39 -> n15<>n40 -> n15<>n41 -> n15<>n42 -> n15<>n43 -> n15<>n44 -> n15<>n45 -> n15<>n46 ->
 n16<>n17 -> n16<>n18 -> n16<>n19 -> n16<>n20 -> n16<>n21 -> n16<>n22 -> n16<>n23 -> n16<>n24 -> n16<>n25 -> n16<>n26 -> n16<>n27 -> n16<>n28 -> n16<>n29 -> n16<>n30 -> n16<>n31 -> n16<>n32 -> n16<>n33 -> n16<>n34 -> n16<>n35 -> n16<>n36 -> n16<>n37 -> n16<>n38 -> n16<>n39 -> n16<>n40 -> n16<>n41 -> n16<>n42 -> n16<>n43 -> n16<>n44 -> n16<>n45 -> n16<>n46 ->
 n17<>n18 -> n17<>n19 -> n17<>n20 -> n17<>n21 -> n17<>n22 -> n17<>n23 -> n17<>n24 -> n17<>n25 -> n17<>n26 -> n17<>n27 -> n17<>n28 -> n17<>n29 -> n17<>n30 -> n17<>n31 -> n17<>n32 -> n17<>n33 -> n17<>n34 -> n17<>n35 -> n17<>n36 -> n17<>n37 -> n17<>n38 -> n17<>n39 -> n17<>n40 -> n17<>n41 -> n17<>n42 -> n17<>n43 -> n17<>n44 -> n17<>n45 -> n17<>n46 ->
 n18<>n19 -> n18<>n20 -> n18<>n21 -> n18<>n22 -> n18<>n23 -> n18<>n24 -> n18<>n25 -> n18<>n26 -> n18<>n27 -> n18<>n28 -> n18<>n29 -> n18<>n30 -> n18<>n31 -> n18<>n32 -> n18<>n33 -> n18<>n34 -> n18<>n35 -> n18<>n36 -> n18<>n37 -> n18<>n38 -> n18<>n39 -> n18<>n40 -> n18<>n41 -> n18<>n42 -> n18<>n43 -> n18<>n44 -> n18<>n45 -> n18<>n46 ->
 n19<>n20 -> n19<>n21 -> n19<>n22 -> n19<>n23 -> n19<>n24 -> n19<>n25 -> n19<>n26 -> n19<>n27 -> n19<>n28 -> n19<>n29 -> n19<>n30 -> n19<>n31 -> n19<>n32 -> n19<>n33 -> n19<>n34 -> n19<>n35 -> n19<>n36 -> n19<>n37 -> n19<>n38 -> n19<>n39 -> n19<>n40 -> n19<>n41 -> n19<>n42 -> n19<>n43 -> n19<>n44 -> n19<>n45 -> n19<>n46 ->
 n20<>n21 -> n20<>n22 -> n20<>n23 -> n20<>n24 -> n20<>n25 -> n20<>n26 -> n20<>n27 -> n20<>n28 -> n20<>n29 -> n20<>n30 -> n20<>n31 -> n20<>n32 -> n20<>n33 -> n20<>n34 -> n20<>n35 -> n20<>n36 -> n20<>n37 -> n20<>n38 -> n20<>n39 -> n20<>n40 -> n20<>n41 -> n20<>n42 -> n20<>n43 -> n20<>n44 -> n20<>n45 -> n20<>n46 ->
 n21<>n22 -> n21<>n23 -> n21<>n24 -> n21<>n25 -> n21<>n26 -> n21<>n27 -> n21<>n28 -> n21<>n29 -> n21<>n30 -> n21<>n31 -> n21<>n32 -> n21<>n33 -> n21<>n34 -> n21<>n35 -> n21<>n36 -> n21<>n37 -> n21<>n38 -> n21<>n39 -> n21<>n40 -> n21<>n41 -> n21<>n42 -> n21<>n43 -> n21<>n44 -> n21<>n45 -> n21<>n46 ->
 n22<>n23 -> n22<>n24 -> n22<>n25 -> n22<>n26 -> n22<>n27 -> n22<>n28 -> n22<>n29 -> n22<>n30 -> n22<>n31 -> n22<>n32 -> n22<>n33 -> n22<>n34 -> n22<>n35 -> n22<>n36 -> n22<>n37 -> n22<>n38 -> n22<>n39 -> n22<>n40 -> n22<>n41 -> n22<>n42 -> n22<>n43 -> n22<>n44 -> n22<>n45 -> n22<>n46 ->
 n23<>n24 -> n23<>n25 -> n23<>n26 -> n23<>n27 -> n23<>n28 -> n23<>n29 -> n23<>n30 -> n23<>n31 -> n23<>n32 -> n23<>n33 -> n23<>n34 -> n23<>n35 -> n23<>n36 -> n23<>n37 -> n23<>n38 -> n23<>n39 -> n23<>n40 -> n23<>n41 -> n23<>n42 -> n23<>n43 -> n23<>n44 -> n23<>n45 -> n23<>n46 ->
 n24<>n25 -> n24<>n26 -> n24<>n27 -> n24<>n28 -> n24<>n29 -> n24<>n30 -> n24<>n31 -> n24<>n32 -> n24<>n33 -> n24<>n34 -> n24<>n35 -> n24<>n36 -> n24<>n37 -> n24<>n38 -> n24<>n39 -> n24<>n40 -> n24<>n41 -> n24<>n42 -> n24<>n43 -> n24<>n44 -> n24<>n45 -> n24<>n46 ->
 n25<>n26 -> n25<>n27 -> n25<>n28 -> n25<>n29 -> n25<>n30 -> n25<>n31 -> n25<>n32 -> n25<>n33 -> n25<>n34 -> n25<>n35 -> n25<>n36 -> n25<>n37 -> n25<>n38 -> n25<>n39 -> n25<>n40 -> n25<>n41 -> n25<>n42 -> n25<>n43 -> n25<>n44 -> n25<>n45 -> n25<>n46 ->
 n26<>n27 -> n26<>n28 -> n26<>n29 -> n26<>n30 -> n26<>n31 -> n26<>n32 -> n26<>n33 -> n26<>n34 -> n26<>n35 -> n26<>n36 -> n26<>n37 -> n26<>n38 -> n26<>n39 -> n26<>n40 -> n26<>n41 -> n26<>n42 -> n26<>n43 -> n26<>n44 -> n26<>n45 -> n26<>n46 ->
 n27<>n28 -> n27<>n29 -> n27<>n30 -> n27<>n31 -> n27<>n32 -> n27<>n33 -> n27<>n34 -> n27<>n35 -> n27<>n36 -> n27<>n37 -> n27<>n38 -> n27<>n39 -> n27<>n40 -> n27<>n41 -> n27<>n42 -> n27<>n43 -> n27<>n44 -> n27<>n45 -> n27<>n46 ->
 n28<>n29 -> n28<>n30 -> n28<>n31 -> n28<>n32 -> n28<>n33 -> n28<>n34 -> n28<>n35 -> n28<>n36 -> n28<>n37 -> n28<>n38 -> n28<>n39 -> n28<>n40 -> n28<>n41 -> n28<>n42 -> n28<>n43 -> n28<>n44 -> n28<>n45 -> n28<>n46 ->
 n29<>n30 -> n29<>n31 -> n29<>n32 -> n29<>n33 -> n29<>n34 -> n29<>n35 -> n29<>n36 -> n29<>n37 -> n29<>n38 -> n29<>n39 -> n29<>n40 -> n29<>n41 -> n29<>n42 -> n29<>n43 -> n29<>n44 -> n29<>n45 -> n29<>n46 ->
 n30<>n31 -> n30<>n32 -> n30<>n33 -> n30<>n34 -> n30<>n35 -> n30<>n36 -> n30<>n37 -> n30<>n38 -> n30<>n39 -> n30<>n40 -> n30<>n41 -> n30<>n42 -> n30<>n43 -> n30<>n44 -> n30<>n45 -> n30<>n46 ->
 n31<>n32 -> n31<>n33 -> n31<>n34 -> n31<>n35 -> n31<>n36 -> n31<>n37 -> n31<>n38 -> n31<>n39 -> n31<>n40 -> n31<>n41 -> n31<>n42 -> n31<>n43 -> n31<>n44 -> n31<>n45 -> n31<>n46 ->
 n32<>n33 -> n32<>n34 -> n32<>n35 -> n32<>n36 -> n32<>n37 -> n32<>n38 -> n32<>n39 -> n32<>n40 -> n32<>n41 -> n32<>n42 -> n32<>n43 -> n32<>n44 -> n32<>n45 -> n32<>n46 ->
 n33<>n34 -> n33<>n35 -> n33<>n36 -> n33<>n37 -> n33<>n38 -> n33<>n39 -> n33<>n40 -> n33<>n41 -> n33<>n42 -> n33<>n43 -> n33<>n44 -> n33<>n45 -> n33<>n46 ->
 n34<>n35 -> n34<>n36 -> n34<>n37 -> n34<>n38 -> n34<>n39 -> n34<>n40 -> n34<>n41 -> n34<>n42 -> n34<>n43 -> n34<>n44 -> n34<>n45 -> n34<>n46 ->
 n35<>n36 -> n35<>n37 -> n35<>n38 -> n35<>n39 -> n35<>n40 -> n35<>n41 -> n35<>n42 -> n35<>n43 -> n35<>n44 -> n35<>n45 -> n35<>n46 ->
 n36<>n37 -> n36<>n38 -> n36<>n39 -> n36<>n40 -> n36<>n41 -> n36<>n42 -> n36<>n43 -> n36<>n44 -> n36<>n45 -> n36<>n46 ->
 n37<>n38 -> n37<>n39 -> n37<>n40 -> n37<>n41 -> n37<>n42 -> n37<>n43 -> n37<>n44 -> n37<>n45 -> n37<>n46 ->
 n38<>n39 -> n38<>n40 -> n38<>n41 -> n38<>n42 -> n38<>n43 -> n38<>n44 -> n38<>n45 -> n38<>n46 ->
 n39<>n40 -> n39<>n41 -> n39<>n42 -> n39<>n43 -> n39<>n44 -> n39<>n45 -> n39<>n46 ->
 n40<>n41 -> n40<>n42 -> n40<>n43 -> n40<>n44 -> n40<>n45 -> n40<>n46 ->
 n41<>n42 -> n41<>n43 -> n41<>n44 -> n41<>n45 -> n41<>n46 ->
 n42<>n43 -> n42<>n44 -> n42<>n45 -> n42<>n46 ->
 n43<>n44 -> n43<>n45 -> n43<>n46 ->
 n44<>n45 -> n44<>n46 ->
 n45<>n46 ->

 exists k ,( n46 !hr-> n92; n45 !hr-> n91; n44 !hr-> n90; n43 !hr-> n89; n42 !hr-> n88; n41 !hr-> n87; n40 !hr-> n86; n39 !hr-> n85; n38 !hr-> n84; n37 !hr-> n83; n36 !hr-> n82; n35 !hr-> n81; n34 !hr-> n80; n33 !hr-> n79; n32 !hr-> n78; n31 !hr-> n77; n30 !hr-> n76; n29 !hr-> n75; n28 !hr-> n74; n27 !hr-> n73; n26 !hr-> n72; n25 !hr-> n71; n24 !hr-> n70; n23 !hr-> n69; n22 !hr-> n68; n21 !hr-> n67; n20 !hr-> n66; n19 !hr-> n65; n18 !hr-> n64; n17 !hr-> n63; n16 !hr-> n62; n15 !hr-> n61; n14 !hr-> n60; n13 !hr-> n59; n12 !hr-> n58; n11 !hr-> n57; n10 !hr-> n56; n9 !hr-> n55; n8 !hr-> n54; n7 !hr-> n53; n6 !hr-> n52; n5 !hr-> n51; n4 !hr-> n50; n3 !hr-> n49; n2 !hr-> n48; n1 !hr-> n47;  emp_heapR) (o2v l) = k.

Proof.
  intros. 
  apply InHr2 in H.
  destruct H. rewrite H.
  exists (Some n47).
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n48).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  destruct H. rewrite H. 
  exists (Some n49).
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  rewrite H. 
  exists (Some n50). 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_neq. 
  rewrite hR_update_neq.
  rewrite hR_update_neq.
  rewrite hR_update_eq.
  reflexivity.
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
  auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
  auto. auto. auto. auto.
Qed.