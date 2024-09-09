Require Import CSSsVerification_Abt.
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

Definition EX_Abt :=
  (o1_ZD ::=plan_ZD (Atuple4 (128;128;1;1)));;
  (o1_GY ::=plan_GY (Atuple3 (0;0;10)));;
  (o1_QYC ::=plan_QYC (Atuple2 (1;10)));;
  (o1_TF ::=plan_TF (Atuple3 (51;10;20)));;
  (p1_M0 ::=asgn (OId o1_ZD));;
  (p1_M0 ::=att (OId o1_GY));;
  (p1_M0 ::=att (OId o1_QYC));;
  (p1_M0 ::=att (OId o1_TF));;
  (c1 add 1);;
  (IF (BTr ZD1 C1) THEN SKIP ELSE CAbt FI);;
  (o2_ZD ::=plan_ZD (Atuple4 (113;128;1;1)));;
  (IF (BZd ZD1 ZD2) THEN SKIP ELSE CAbt FI).


Fact EX_Abt_Error :

forall (oloc_1 oloc_2 oloc_3 oloc_4 oloc_5 :nat)
       (rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
        rloc_14 rloc_15 rloc_16 :nat),

neq0_5  oloc_1 oloc_2 oloc_3 oloc_4 oloc_5 ->
neq0_16 rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
        rloc_14 rloc_15 rloc_16 ->

neq_5 oloc_1 oloc_2 oloc_3 oloc_4 oloc_5 ->
neq_16 rloc_1 rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
       rloc_14 rloc_15 rloc_16 -> 

empty_st =[EX_Abt]=> Abt.

Proof.
  unfold neq0_5, neq0_16, neq_5, neq_16.
  intros oloc_1 oloc_2 oloc_3 oloc_4 oloc_5.
  intros rloc_1 rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
         rloc_14 rloc_15 rloc_16.
  intros H_neq0_oloc H_neq0_rloc H_neq_oloc H_neq_rloc.
  destruct H_neq0_oloc as (H1_o & H2_o & H3_o & H4_o & H5_o).
  destruct H_neq0_rloc as (H1_r & H2_r & H3_r & H4_r & H5_r & H6_r & H7_r & H8_r & H9_r & H10_r & H11_r & H12_r & H13_r & 
                           H14_r & H15_r & H16_r).
  destruct H_neq_oloc as (
  Ho1_2 & Ho1_3 & Ho1_4 & Ho1_5 & 
  Ho2_3 & Ho2_4 & Ho2_5 & 
  Ho3_4 & Ho3_5 &
  Ho4_5 
  ).
  destruct H_neq_rloc as (
  Hr1_2 & Hr1_3 & Hr1_4 & Hr1_5 & Hr1_6 & Hr1_7 & Hr1_8 & Hr1_9 & Hr1_10 & Hr1_11 & Hr1_12 & Hr1_13 & Hr1_14 & Hr1_15 & Hr1_16 & 
  Hr2_3 & Hr2_4 & Hr2_5 & Hr2_6 & Hr2_7 & Hr2_8 & Hr2_9 & Hr2_10 & Hr2_11 & Hr2_12 & Hr2_13 & Hr2_14 & Hr2_15 & Hr2_16 &
  Hr3_4 & Hr3_5 & Hr3_6 & Hr3_7 & Hr3_8 & Hr3_9 & Hr3_10 & Hr3_11 & Hr3_12 & Hr3_13 & Hr3_14 & Hr3_15 & Hr3_16 & 
  Hr4_5 & Hr4_6 & Hr4_7 & Hr4_8 & Hr4_9 & Hr4_10 & Hr4_11 & Hr4_12 & Hr4_13 & Hr4_14 & Hr4_15 & Hr4_16 & 
  Hr5_6 & Hr5_7 & Hr5_8 & Hr5_9 & Hr5_10 & Hr5_11 & Hr5_12 & Hr5_13 & Hr5_14 & Hr5_15 & Hr5_16 & 
  Hr6_7 & Hr6_8 & Hr6_9 & Hr6_10 & Hr6_11 & Hr6_12 & Hr6_13 & Hr6_14 & Hr6_15 & Hr6_16 & 
  Hr7_8 & Hr7_9 & Hr7_10 & Hr7_11 & Hr7_12 & Hr7_13 & Hr7_14 & Hr7_15 & Hr7_16 & 
  Hr8_9 & Hr8_10 & Hr8_11 & Hr8_12 & Hr8_13 & Hr8_14 & Hr8_15 & Hr8_16 & 
  Hr9_10 & Hr9_11 & Hr9_12 & Hr9_13 & Hr9_14 & Hr9_15 & Hr9_16 & 
  Hr10_11 & Hr10_12 & Hr10_13 & Hr10_14 & Hr10_15 & Hr10_16 & 
  Hr11_12 & Hr11_13 & Hr11_14 & Hr11_15 & Hr11_16 &
  Hr12_13 & Hr12_14 & Hr12_15 & Hr12_16 & 
  Hr13_14 & Hr13_15 & Hr13_16 & 
  Hr14_15 & Hr14_16 & 
  Hr15_16 
  ).

  eapply E_Seq.
 - eapply E_Oplan_Tuple4 with (loc := oloc_1) (loc1 := rloc_1) (loc2 := rloc_2) (loc3 := rloc_3)(loc4 := rloc_4).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity.
   reflexivity.

 - eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_2) (loc1 := rloc_5) (loc2 := rloc_6) (loc3 := rloc_7).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_5.
   apply sym_not_eq; apply Hr3_5.
   apply sym_not_eq; apply Hr2_5.
   apply sym_not_eq; apply Hr1_5.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_6.
   apply sym_not_eq; apply Hr3_6.
   apply sym_not_eq; apply Hr2_6.
   apply sym_not_eq; apply Hr1_6.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_7.
   apply sym_not_eq; apply Hr3_7.
   apply sym_not_eq; apply Hr2_7.
   apply sym_not_eq; apply Hr1_7.
   rewrite hO_update_neq.
   reflexivity.
   auto.

   eapply E_Seq.
   eapply E_Oplan_Tuple2 with (loc := oloc_3) (loc1 := rloc_8) (loc2 := rloc_9).
   simpl; reflexivity.
   simpl; reflexivity.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_8.
   apply sym_not_eq; apply Hr3_8.
   apply sym_not_eq; apply Hr2_8.
   apply sym_not_eq; apply Hr1_8.
   apply sym_not_eq; apply Hr7_8.
   apply sym_not_eq; apply Hr6_8.
   apply sym_not_eq; apply Hr5_8.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_9.
   apply sym_not_eq; apply Hr3_9.
   apply sym_not_eq; apply Hr2_9.
   apply sym_not_eq; apply Hr1_9.
   apply sym_not_eq; apply Hr7_9.
   apply sym_not_eq; apply Hr6_9.
   apply sym_not_eq; apply Hr5_9.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_4) (loc1 := rloc_10) (loc2 := rloc_11)(loc3 := rloc_12).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_10.
   apply sym_not_eq; apply Hr3_10.
   apply sym_not_eq; apply Hr2_10.
   apply sym_not_eq; apply Hr1_10.
   apply sym_not_eq; apply Hr7_10.
   apply sym_not_eq; apply Hr6_10.
   apply sym_not_eq; apply Hr5_10.
   apply sym_not_eq; apply Hr9_10.
   apply sym_not_eq; apply Hr8_10.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_11.
   apply sym_not_eq; apply Hr3_11.
   apply sym_not_eq; apply Hr2_11.
   apply sym_not_eq; apply Hr1_11.
   apply sym_not_eq; apply Hr7_11.
   apply sym_not_eq; apply Hr6_11.
   apply sym_not_eq; apply Hr5_11.
   apply sym_not_eq; apply Hr9_11.
   apply sym_not_eq; apply Hr8_11.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_12.
   apply sym_not_eq; apply Hr3_12.
   apply sym_not_eq; apply Hr2_12.
   apply sym_not_eq; apply Hr1_12.
   apply sym_not_eq; apply Hr7_12.
   apply sym_not_eq; apply Hr6_12.
   apply sym_not_eq; apply Hr5_12.
   apply sym_not_eq; apply Hr9_12.
   apply sym_not_eq; apply Hr8_12.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto.

   eapply E_Seq.
   eapply E_Sasgn  with (loc := oloc_1).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_2).
   simpl. reflexivity.
   rewrite sS_update_eq; reflexivity.
   intros. apply SafeinHo1_4.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl. reflexivity.
   simpl. rewrite sS_update_eq;  reflexivity.
   intros. apply SafeinHo2_4.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_4).
   simpl. reflexivity.
   simpl. rewrite sS_update_eq;  reflexivity.
   intros. apply SafeinHo3_4.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl. 
   unfold Tractor_need.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple4 with (loc := oloc_5) (loc1 := rloc_13) (loc2 := rloc_14) (loc3 := rloc_15)(loc4 := rloc_16).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_13.
   apply sym_not_eq; apply Hr3_13.
   apply sym_not_eq; apply Hr2_13.
   apply sym_not_eq; apply Hr1_13.
   apply sym_not_eq; apply Hr7_13.
   apply sym_not_eq; apply Hr6_13.
   apply sym_not_eq; apply Hr5_13.
   apply sym_not_eq; apply Hr9_13.
   apply sym_not_eq; apply Hr8_13. 
   apply sym_not_eq; apply Hr12_13.
   apply sym_not_eq; apply Hr11_13.
   apply sym_not_eq; apply Hr10_13.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_14.
   apply sym_not_eq; apply Hr3_14.
   apply sym_not_eq; apply Hr2_14.
   apply sym_not_eq; apply Hr1_14.
   apply sym_not_eq; apply Hr7_14.
   apply sym_not_eq; apply Hr6_14.
   apply sym_not_eq; apply Hr5_14.
   apply sym_not_eq; apply Hr9_14.
   apply sym_not_eq; apply Hr8_14. 
   apply sym_not_eq; apply Hr12_14.
   apply sym_not_eq; apply Hr11_14.
   apply sym_not_eq; apply Hr10_14.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_15.
   apply sym_not_eq; apply Hr3_15.
   apply sym_not_eq; apply Hr2_15.
   apply sym_not_eq; apply Hr1_15.
   apply sym_not_eq; apply Hr7_15.
   apply sym_not_eq; apply Hr6_15.
   apply sym_not_eq; apply Hr5_15.
   apply sym_not_eq; apply Hr9_15.
   apply sym_not_eq; apply Hr8_15. 
   apply sym_not_eq; apply Hr12_15.
   apply sym_not_eq; apply Hr11_15.
   apply sym_not_eq; apply Hr10_15.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_16.
   apply sym_not_eq; apply Hr3_16.
   apply sym_not_eq; apply Hr2_16.
   apply sym_not_eq; apply Hr1_16.
   apply sym_not_eq; apply Hr7_16.
   apply sym_not_eq; apply Hr6_16.
   apply sym_not_eq; apply Hr5_16.
   apply sym_not_eq; apply Hr9_16.
   apply sym_not_eq; apply Hr8_16. 
   apply sym_not_eq; apply Hr12_16.
   apply sym_not_eq; apply Hr11_16.
   apply sym_not_eq; apply Hr10_16.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto.

   eapply E_IfFalse.
   simpl. 
   unfold unfoldWing.
   simpl. reflexivity.
   eapply E_Abt.
   Unshelve. auto. 
Qed.









