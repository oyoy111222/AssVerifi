Require Import CSSsVerification7.
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

Definition Example_7 :=
  (o1_ZD ::=plan_ZD (Atuple4 (195;6;0;1)));;
  (o1_GRDZT ::=plan_GRDZT (Atuple3 (80;(large_to_nat 1608);(large_to_nat 1668))));;
  (o1_NMWQZZ ::=plan_NMWQZZ (Atuple3 (80;(large_to_nat 1608);(large_to_nat 1680))));;
  (o1_GD ::=plan_GD (Atuple3 (80;(large_to_nat 1680);(large_to_nat 1752))));;
  (o1_GDDZ ::=plan_GDDZ (Atuple3 (80;(large_to_nat 1680);(large_to_nat 1728))));;
  (o1_JWJC ::=plan_JWJC (Atuple3 (80;(large_to_nat 1680);(large_to_nat 1740))));;
  (o1_JY ::=plan_JY (Atuple3 (80;(large_to_nat 1680);(large_to_nat 1752))));;
  (P12 ::=asgn (OId o1_ZD));;
  (P12 ::=att (OId o1_GRDZT));;
  (IF (BEq ((ANum (triple4_return_third_element ZD1))) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (P12 ::=att (OId o1_NMWQZZ));;
  (P12 ::=att (OId o1_GD));;
  (d1 add 1);;
  (P12 ::=att (OId o1_GDDZ));;
  (IF (BEq (ANum D1) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (gdsb_4 sub 1);;
  (P12 ::=att (OId o1_JWJC));;
  (IF (BEq (ANum D1) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (P12 ::=att (OId o1_JY));;
  (IF (BEq (ANum D1) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (jyc_11 sub 1);;
  (P12 ::exe (ANum 1));;
  (P12 ::exe (ANum 1));;
  (J35_13_GRDZT add 1);;
  (P12 ::exe (ANum 1));;
  (J35_13_NMWQZZ add 1);;
  (P12 ::exe (ANum 1));;
  (d1 sub 1);;
  (P12 ::exe (ANum 1));;
  (J35_13_GDDZ add 1);;
  (gdsb_4 add 1);;
  (P12 ::exe (ANum 1));;
  (J35_13_JWJC add 1);;
  (P12 ::exe (ANum 1));;
  (J35_13_JY add 1);;
  (jyc_11 add 1);;
  (free P12);;
  (SKIP).

Fact Example_7_Correct :

forall (oloc_1  oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 :nat)
       (rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
        rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 :nat),

neq0_7 oloc_1  oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 ->
neq0_24 rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
        rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 ->

neq_7  oloc_1  oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 ->
neq_24  rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
        rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 -> 

(emp_sO, d1 !sv-> 0; gdsb_4 !sv-> 1; jyc_11 !sv-> 1; emp_sV, emp_sS, rloc_23 !hr-> 1; rloc_24 !hr-> 1;  emp_heapR, 
 emp_heapO) =[
 Example_7
]=> St (o1_JY !so-> 0; o1_JWJC !so-> 0; o1_GDDZ !so-> 0; o1_GD !so-> 0; o1_NMWQZZ !so-> 0; o1_GRDZT !so-> 0; o1_ZD !so-> 0; emp_sO,
        jyc_11 !sv-> 1; J35_13_JY !sv-> 1; J35_13_JWJC !sv-> 1; gdsb_4 !sv-> 1; J35_13_GDDZ !sv-> 1; d1 !sv-> 0; J35_13_NMWQZZ !sv-> 1;
        J35_13_GRDZT !sv-> 1; emp_sV, P12 !ss-> on; emp_sS, rloc_23 !hr-> 1; rloc_24 !hr-> 1; emp_heapR, emp_heapO).

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
   eapply E_Oplan_Tuple3 with (loc := oloc_5) (loc1 := rloc_14) (loc2 := rloc_15) (loc3 := rloc_16).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_6) (loc1 := rloc_17) (loc2 := rloc_18) (loc3 := rloc_19).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_7) (loc1 := rloc_20) (loc2 := rloc_21) (loc3 := rloc_22).
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
   simpl. reflexivity.
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo1_7; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.























