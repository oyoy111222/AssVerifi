Require Import CSSsVerification6.
Require Import function.
Require Import SafeinHo.
Require Import SafeinHr.
Require Import NeqDefinition.
Require Export language.
Require Export semantic.
Require Export state.
Require Import BinNums.
Require Import Coq.Lists.List.
Require Import ZArith.
Import ListNotations.

Definition Example_6 :=
  (o1_ZD ::=plan_ZD (Atuple4 (128;128;0;0)));;
  (o1_GY ::=plan_GY (Atuple3 (0;0;10)));;
  (o1_QYC ::=plan_QYC (Atuple2 (1;10)));;
  (p1_M0 ::=asgn (OId o1_ZD));;
  (p1_M0 ::=att (OId o1_GY));;
  (p1_M0 ::=att (OId o1_QYC));;
  (c1 add 1);;
  (IF (BTr ZD1 C1) THEN SKIP ELSE CAbt FI).

Fact Example_6_Correct :

forall (oloc_1 oloc_2 oloc_3  :nat)
       (rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9  :nat),

neq0_3 oloc_1 oloc_2 oloc_3  ->
neq0_9 rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 ->

neq_3  oloc_1 oloc_2 oloc_3  ->
neq_9  rloc_1 rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9  -> 

empty_st =[Example_6]=> Abt.

Proof.
  unfold neq0_3, neq0_9, neq_3, neq_9.
  intros oloc_1 oloc_2 oloc_3 .
  intros rloc_1 rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 .
  intros H_neq0_oloc H_neq0_rloc H_neq_oloc H_neq_rloc.
  destruct H_neq0_oloc as (H1_o & H2_o & H3_o ).
  destruct H_neq0_rloc as (H1_r & H2_r & H3_r & H4_r & H5_r & H6_r & H7_r & H8_r & H9_r ).
  destruct H_neq_oloc as (
  Ho1_2 & Ho1_3 & Ho2_3 
  ).
  destruct H_neq_rloc as (
  Hr1_2 & Hr1_3 & Hr1_4 & Hr1_5 & Hr1_6 & Hr1_7 & Hr1_8 & Hr1_9 &  
  Hr2_3 & Hr2_4 & Hr2_5 & Hr2_6 & Hr2_7 & Hr2_8 & Hr2_9 & 
  Hr3_4 & Hr3_5 & Hr3_6 & Hr3_7 & Hr3_8 & Hr3_9 & 
  Hr4_5 & Hr4_6 & Hr4_7 & Hr4_8 & Hr4_9 & 
  Hr5_6 & Hr5_7 & Hr5_8 & Hr5_9 & 
  Hr6_7 & Hr6_8 & Hr6_9 & 
  Hr7_8 & Hr7_9 & 
  Hr8_9 
  ).

   eapply E_Seq.
 - eapply E_Oplan_Tuple4 with (loc := oloc_1) (loc1 := rloc_1) (loc2 := rloc_2) (loc3 := rloc_3)(loc4 := rloc_4); reflexivity.

 - eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_2) (loc1 := rloc_5) (loc2 := rloc_6) (loc3 := rloc_7).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.

   eapply E_Seq.
   eapply E_Oplan_Tuple2 with (loc := oloc_3) (loc1 := rloc_8) (loc2 := rloc_9); auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.

   eapply E_Seq.
   eapply E_Sasgn  with (loc := oloc_1).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_2).
   simpl. reflexivity.
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo1_3; auto.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl. reflexivity.
   simpl. rewrite sS_update_eq;  reflexivity.
   intros. 
   apply SafeinHo2_3; auto.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_IfFalse.
   simpl. 
   unfold unfoldWing.
   simpl. reflexivity.
   eapply E_Abt.
   Unshelve. 
   auto. 
Qed.



