Require Import CSSsVerification8.
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

Definition Example_8 :=
  (o1_ZD ::=plan_ZD (Atuple4 (184;50;1;1)));;
  (o1_DJ ::=plan_DJ (Atuple3 (66;0;300)));;
  (o1_KC ::=plan_KC (Atuple3 (66;300;420)));;
  (o1_NC ::=plan_NC (Atuple3 (66;420;540)));;
  (B5 ::=asgn (OId o1_ZD));;
  (B5 ::=att (OId o1_DJ));;
  (B5 ::=att (OId o1_KC));;
  (B5 ::=att (OId o1_NC));;
  (B5 ::exe (ANum 1));;
  (B5 ::exe (ANum 1));;
  (J35_1_DJ add 1);;
  (B5 ::exe (ANum 1));;
  (J35_1_KC add 1);;
  (B5 ::exe (ANum 1));;
  (J35_1_NC add 1);;
  (free B5);;
  (o1_ZD ::=plan_ZD (Atuple4 (108;62;1;1)));;
  (o1_DY ::=plan_DY (Atuple3 (75;540;600)));;
  (o1_FKZJ ::=plan_FKZJ (Atuple3 (75;600;720)));;
  (K3 ::=asgn (OId o1_ZD));;
  (K3 ::=att (OId o1_DY));;
  (K3 ::=att (OId o1_FKZJ));;
  (K3 ::exe (ANum 1));;
  (K3 ::exe (ANum 1));;
  (J35_1_DY add 1);;
  (K3 ::exe (ANum 1));;
  (J35_1_FKZJ add 1);;
  (free K3);;
  (o1_ZD ::=plan_ZD (Atuple4 (128;62;1;1)));;
  (o1_DY ::=plan_DY (Atuple3 (67;720;780)));;
  (o1_QF ::=plan_QF (Atuple3 (67;780;798)));;
  (C3 ::=asgn (OId o1_ZD));;
  (C3 ::=att (OId o1_DY));;
  (C3 ::=att (OId o1_QF));;
  (IF (BEq (ANum (triple3_return_first_element QF1)) (ANum 67)) THEN SKIP ELSE CAbt FI);;
  (C3 ::exe (ANum 1));;
  (C3 ::exe (ANum 1));;
  (J35_1_DY add 1);;
  (C3 ::exe (ANum 1));;
  (J35_1_QF add 1);;
  (free C3);;
  (o2_ZD ::=plan_ZD (Atuple4 (175;48;0;1)));;
  (o2_DJ ::=plan_DJ (Atuple3 (66;0;300)));;
  (o2_KC ::=plan_KC (Atuple3 (66;300;420)));;
  (o2_NC ::=plan_NC (Atuple3 (66;420;540)));;
  (B6 ::=asgn (OId o2_ZD));;
  (B6 ::=att (OId o2_DJ));;
  (B6 ::=att (OId o2_KC));;
  (B6 ::=att (OId o2_NC));;
  (B6 ::exe (ANum 1));;
  (B6 ::exe (ANum 1));;
  (J35_2_DJ add 1);;
  (B6 ::exe (ANum 1));;
  (J35_2_KC add 1);;
  (B6 ::exe (ANum 1));;
  (J35_2_NC add 1);;
  (free B6);;
  (o2_ZD ::=plan_ZD (Atuple4 (108;62;1;1)));;
  (o2_DY ::=plan_DY (Atuple3 (75;660;720)));;
  (o2_FKZJ ::=plan_FKZJ (Atuple3 (75;720;840)));;
  (K3 ::reuse (OId o2_ZD));;
  (K3 ::=att (OId o2_DY));;
  (K3 ::=att (OId o2_FKZJ));;
  (K3 ::exe (ANum 1));;
  (K3 ::exe (ANum 1));;
  (J35_2_DY add 1);;
  (K3 ::exe (ANum 1));;
  (J35_2_FKZJ add 1);;
  (free K3);;
  (o2_ZD ::=plan_ZD (Atuple4 (128;62;1;1)));;
  (o2_DY ::=plan_DY (Atuple3 (67;840;900)));;
  (o2_QF ::=plan_QF (Atuple3 (67;900;918)));;
  (C3 ::reuse (OId o2_ZD));;
  (C3 ::=att (OId o2_DY));;
  (C3 ::=att (OId o2_QF));;
  (IF (BEq (ANum (triple3_return_first_element QF2)) (ANum 67)) THEN SKIP ELSE CAbt FI);;
  (C3 ::exe (ANum 1));;
  (C3 ::exe (ANum 1));;
  (J35_2_DY add 1);;
  (C3 ::exe (ANum 1));;
  (J35_2_QF add 1);;
  (free C3);;
  (SKIP).

Fact Example_8_Correct :

forall (oloc_1  oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 :nat)
       (rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
        rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 :nat),

neq0_7 oloc_1  oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 ->
neq0_24 rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
        rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 ->

neq_7  oloc_1  oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 ->
neq_24  rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
        rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 -> 

empty_st =[
  Example_8
]=> St (o2_QF !so-> 0;o2_DY !so-> 0;o2_ZD !so-> 0;o2_FKZJ !so-> 0;o2_NC !so-> 0;o2_KC !so-> 0;o2_DJ !so-> 0;o1_QF !so-> 0;
        o1_DY !so-> 0;o1_ZD !so-> 0; o1_FKZJ !so-> 0; o1_NC !so-> 0; o1_KC !so-> 0; o1_DJ !so-> 0; emp_sO,J35_2_QF !sv-> 1;
        J35_2_DY !sv-> 2;J35_2_FKZJ !sv-> 1;J35_2_NC !sv-> 1;J35_2_KC !sv-> 1;J35_2_DJ !sv-> 1;J35_1_QF !sv-> 1;J35_1_DY !sv-> 2;
        J35_1_FKZJ !sv-> 1; J35_1_NC !sv-> 1; J35_1_KC !sv-> 1; J35_1_DJ !sv-> 1; emp_sV,C3 !ss-> on; K3 !ss-> on; B6 !ss-> on; B5 !ss-> on; 
        emp_sS, emp_heapR, emp_heapO).

Proof.
  unfold neq0_7, neq0_24, neq_7, neq_24.
  intros oloc_1  oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 .
  intros rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
         rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 .
  intros H_neq0_oloc H_neq0_rloc H_neq_oloc H_neq_rloc.
  destruct H_neq0_oloc as (H1_o & H2_o & H3_o & H4_o & H5_o & H6_o & H7_o ).
  destruct H_neq0_rloc as (H1_r & H2_r & H3_r & H4_r & H5_r & H6_r & H7_r & H8_r & H9_r & H10_r & H11_r & H12_r & H13_r & 
                           H14_r & H15_r & H16_r & H17_r & H18_r & H19_r & H20_r & H21_r & H22_r & H23_r & H24_r ).
  destruct H_neq_oloc as (
  Ho1_2 & Ho1_3 & Ho1_4 & Ho1_5 & Ho1_6 & Ho1_7 &
  Ho2_3 & Ho2_4 & Ho2_5 & Ho2_6 & Ho2_7 & 
  Ho3_4 & Ho3_5 & Ho3_6 & Ho3_7 &
  Ho4_5 & Ho4_6 & Ho4_7 &
  Ho5_6 & Ho5_7 &
  Ho6_7 
  ).
  destruct H_neq_rloc as (
  Hr1_2 & Hr1_3 & Hr1_4 & Hr1_5 & Hr1_6 & Hr1_7 & Hr1_8 & Hr1_9 & Hr1_10 & Hr1_11 & Hr1_12 & Hr1_13 & Hr1_14 & Hr1_15 & Hr1_16 & Hr1_17 & Hr1_18 & Hr1_19 & Hr1_20 & Hr1_21 & Hr1_22 & Hr1_23 & Hr1_24 & 
  Hr2_3 & Hr2_4 & Hr2_5 & Hr2_6 & Hr2_7 & Hr2_8 & Hr2_9 & Hr2_10 & Hr2_11 & Hr2_12 & Hr2_13 & Hr2_14 & Hr2_15 & Hr2_16 & Hr2_17 & Hr2_18 & Hr2_19 & Hr2_20 & Hr2_21 & Hr2_22 & Hr2_23 & Hr2_24 &
  Hr3_4 & Hr3_5 & Hr3_6 & Hr3_7 & Hr3_8 & Hr3_9 & Hr3_10 & Hr3_11 & Hr3_12 & Hr3_13 & Hr3_14 & Hr3_15 & Hr3_16 & Hr3_17 & Hr3_18 & Hr3_19 & Hr3_20 & Hr3_21 & Hr3_22 & Hr3_23 & Hr3_24 & 
  Hr4_5 & Hr4_6 & Hr4_7 & Hr4_8 & Hr4_9 & Hr4_10 & Hr4_11 & Hr4_12 & Hr4_13 & Hr4_14 & Hr4_15 & Hr4_16 & Hr4_17 & Hr4_18 & Hr4_19 & Hr4_20 & Hr4_21 & Hr4_22 & Hr4_23 & Hr4_24 &  
  Hr5_6 & Hr5_7 & Hr5_8 & Hr5_9 & Hr5_10 & Hr5_11 & Hr5_12 & Hr5_13 & Hr5_14 & Hr5_15 & Hr5_16 & Hr5_17 & Hr5_18 & Hr5_19 & Hr5_20 & Hr5_21 & Hr5_22 & Hr5_23 & Hr5_24 & 
  Hr6_7 & Hr6_8 & Hr6_9 & Hr6_10 & Hr6_11 & Hr6_12 & Hr6_13 & Hr6_14 & Hr6_15 & Hr6_16 & Hr6_17 & Hr6_18 & Hr6_19 & Hr6_20 & Hr6_21 & Hr6_22 & Hr6_23 & Hr6_24 & 
  Hr7_8 & Hr7_9 & Hr7_10 & Hr7_11 & Hr7_12 & Hr7_13 & Hr7_14 & Hr7_15 & Hr7_16 & Hr7_17 & Hr7_18 & Hr7_19 & Hr7_20 & Hr7_21 & Hr7_22 & Hr7_23 & Hr7_24 & 
  Hr8_9 & Hr8_10 & Hr8_11 & Hr8_12 & Hr8_13 & Hr8_14 & Hr8_15 & Hr8_16 & Hr8_17 & Hr8_18 & Hr8_19 & Hr8_20 & Hr8_21 & Hr8_22 & Hr8_23 & Hr8_24 &
  Hr9_10 & Hr9_11 & Hr9_12 & Hr9_13 & Hr9_14 & Hr9_15 & Hr9_16 & Hr9_17 & Hr9_18 & Hr9_19 & Hr9_20 & Hr9_21 & Hr9_22 & Hr9_23 & Hr9_24 & 
  Hr10_11 & Hr10_12 & Hr10_13 & Hr10_14 & Hr10_15 & Hr10_16 & Hr10_17 & Hr10_18 & Hr10_19 & Hr10_20 & Hr10_21 & Hr10_22 & Hr10_23 & Hr10_24 &
  Hr11_12 & Hr11_13 & Hr11_14 & Hr11_15 & Hr11_16 & Hr11_17 & Hr11_18 & Hr11_19 & Hr11_20 & Hr11_21 & Hr11_22 & Hr11_23 & Hr11_24 & 
  Hr12_13 & Hr12_14 & Hr12_15 & Hr12_16 & Hr12_17 & Hr12_18 & Hr12_19 & Hr12_20 & Hr12_21 & Hr12_22 & Hr12_23 & Hr12_24 &  
  Hr13_14 & Hr13_15 & Hr13_16 & Hr13_17 & Hr13_18 & Hr13_19 & Hr13_20 & Hr13_21 & Hr13_22 & Hr13_23 & Hr13_24 &
  Hr14_15 & Hr14_16 & Hr14_17 & Hr14_18 & Hr14_19 & Hr14_20 & Hr14_21 & Hr14_22 & Hr14_23 & Hr14_24 & 
  Hr15_16 & Hr15_17 & Hr15_18 & Hr15_19 & Hr15_20 & Hr15_21 & Hr15_22 & Hr15_23 & Hr15_24 & 
  Hr16_17 & Hr16_18 & Hr16_19 & Hr16_20 & Hr16_21 & Hr16_22 & Hr16_23 & Hr16_24 & 
  Hr17_18 & Hr17_19 & Hr17_20 & Hr17_21 & Hr17_22 & Hr17_23 & Hr17_24 & 
  Hr18_19 & Hr18_20 & Hr18_21 & Hr18_22 & Hr18_23 & Hr18_24 &
  Hr19_20 & Hr19_21 & Hr19_22 & Hr19_23 & Hr19_24 & 
  Hr20_21 & Hr20_22 & Hr20_23 & Hr20_24 & 
  Hr21_22 & Hr21_23 & Hr21_24 & 
  Hr22_23 & Hr22_24 &
  Hr23_24 
  ).

   eapply E_Seq.
 - eapply E_Oplan_Tuple4 with (loc := oloc_1) (loc1 := rloc_1) (loc2 := rloc_2) (loc3 := rloc_3)(loc4 := rloc_4).
   reflexivity. reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.

 - eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_2) (loc1 := rloc_5) (loc2 := rloc_6) (loc3 := rloc_7).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_3) (loc1 := rloc_8) (loc2 := rloc_9) (loc3 := rloc_10).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_4) (loc1 := rloc_11) (loc2 := rloc_12) (loc3 := rloc_13).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Sasgn  with (loc := oloc_1).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_2).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo1_4; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo2_4; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_4).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo3_4; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_1)(e :=o1_ZD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr4_13; auto.
   simpl. 
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_2)(e :=o1_DJ).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_9; auto.
   simpl. 
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_3)(e :=o1_KC).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_6; auto.
   simpl. 
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_4)(e :=o1_NC).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_3; auto.
   simpl.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Oplan_Tuple4 with (loc := oloc_1) (loc1 := rloc_1) (loc2 := rloc_2) (loc3 := rloc_3)(loc4 := rloc_4).
   reflexivity. reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_2) (loc1 := rloc_5) (loc2 := rloc_6) (loc3 := rloc_7).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_3) (loc1 := rloc_8) (loc2 := rloc_9) (loc3 := rloc_10).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Sasgn  with (loc := oloc_1).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_2).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo1_3; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo2_3; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_1)(e :=o1_ZD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr4_10; auto.
   simpl. 
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_2)(e :=o1_DY).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_6; auto.
   simpl. 
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_3)(e :=o1_FKZJ).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_3; auto.
   simpl.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Oplan_Tuple4 with (loc := oloc_1) (loc1 := rloc_1) (loc2 := rloc_2) (loc3 := rloc_3)(loc4 := rloc_4).
   reflexivity. reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_2) (loc1 := rloc_5) (loc2 := rloc_6) (loc3 := rloc_7).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.
   rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_3) (loc1 := rloc_8) (loc2 := rloc_9) (loc3 := rloc_10).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Sasgn  with (loc := oloc_1).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_2).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo1_3; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo2_3; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_1)(e :=o1_ZD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr4_10; auto.
   simpl. 
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_2)(e :=o1_DY).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_6; auto.
   simpl. 
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   simpl.
   rewrite sV_update_shadow_3.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_3)(e :=o1_QF).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_3; auto.
   simpl.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Oplan_Tuple4 with (loc := oloc_1) (loc1 := rloc_1) (loc2 := rloc_2) (loc3 := rloc_3)(loc4 := rloc_4).
   reflexivity. reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_2) (loc1 := rloc_5) (loc2 := rloc_6) (loc3 := rloc_7).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_3) (loc1 := rloc_8) (loc2 := rloc_9) (loc3 := rloc_10).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_4) (loc1 := rloc_11) (loc2 := rloc_12) (loc3 := rloc_13).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Sasgn  with (loc := oloc_1).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_2).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo1_4; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo2_4; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_4).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo3_4; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_1)(e :=o2_ZD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr4_13; auto.
   simpl. 
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_2)(e :=o2_DJ).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_9; auto.
   simpl. 
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_3)(e :=o2_KC).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_6; auto.
   simpl. 
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_4)(e :=o2_NC).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_3; auto.
   simpl.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Oplan_Tuple4 with (loc := oloc_1) (loc1 := rloc_1) (loc2 := rloc_2) (loc3 := rloc_3)(loc4 := rloc_4).
   reflexivity. reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_2) (loc1 := rloc_5) (loc2 := rloc_6) (loc3 := rloc_7).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_3) (loc1 := rloc_8) (loc2 := rloc_9) (loc3 := rloc_10).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Sreuse  with (loc := oloc_1).
   rewrite sS_update_neq.
   rewrite sS_update_neq.
   rewrite sS_update_eq.
   reflexivity.
   discriminate. discriminate.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq.
   reflexivity.
   discriminate. discriminate.
   rewrite sS_update_shadow_4.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_2).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo1_3; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo2_3; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_1)(e :=o2_ZD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr4_10; auto.
   simpl. 
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_2)(e :=o2_DY).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_6; auto.
   simpl. 
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_3)(e :=o2_FKZJ).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_3; auto.
   simpl.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Oplan_Tuple4 with (loc := oloc_1) (loc1 := rloc_1) (loc2 := rloc_2) (loc3 := rloc_3)(loc4 := rloc_4).
   reflexivity. reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_2) (loc1 := rloc_5) (loc2 := rloc_6) (loc3 := rloc_7).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.
   rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_3) (loc1 := rloc_8) (loc2 := rloc_9) (loc3 := rloc_10).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Sreuse  with (loc := oloc_1).
   rewrite sS_update_neq.
   rewrite sS_update_neq.
   rewrite sS_update_eq.
   reflexivity.
   discriminate. discriminate.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq.
   reflexivity.
   discriminate. discriminate.
   rewrite sS_update_shadow_4.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_2).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo1_3; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo2_3; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_1)(e :=o2_ZD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr4_10; auto.
   simpl. 
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_2)(e :=o2_DY).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_6; auto.
   simpl. 
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   simpl.
   rewrite sV_update_shadow_3.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_3)(e :=o2_QF).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_3; auto.
   simpl.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Skip.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   Unshelve.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
Qed.












