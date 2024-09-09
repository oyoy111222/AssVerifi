Require Import CSSsVerification_Three.
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

(* 三机运行流程案例 *)
Definition EX_JZ_Three :=
  (o1_ZD ::=plan_ZD (Atuple4 (128;128;0;1)));;
  (o1_GY ::=plan_GY (Atuple3 (0;0;10)));;
  (o1_QYC ::=plan_QYC (Atuple2 (1;10)));;
  (p1_M0 ::=asgn (OId o1_ZD));;
  (p1_M0 ::=att (OId o1_GY));;
  (p1_M0 ::=att (OId o1_QYC));;
  (c1 add 1);;
  (IF (BTr ZD1 C1) THEN SKIP ELSE CAbt FI);;
  (o2_ZD ::=plan_ZD (Atuple4 (113;128;1;1)));;
  (IF (BZd ZD1 ZD2) THEN SKIP ELSE CAbt FI);;
  (o2_GY ::=plan_GY (Atuple3 (2;10;10)));;
  (o2_QYC ::=plan_QYC (Atuple2 (1;20)));;
  (p2_M0 ::=asgn (OId o2_ZD));;
  (p2_M0 ::=att (OId o2_GY));;
  (p2_M0 ::=att (OId o2_QYC));;
  (c2 add 1);;
  (IF (BTr ZD2 C2) THEN SKIP ELSE CAbt FI);;
  (IF (BOr (BOr (BMod (triple3_return_first_element GY1) 0) (BMod (triple3_return_first_element GY1) 2) ) (BMod (triple3_return_first_element GY1) 3)) THEN SKIP ELSE CAbt FI);;
  (p1_M0 ::exe (ANum 1));;
  (p1_M0 ::exe (ANum 1));;
  (z1_GY add 1);;
  (p1_M0 ::exe (ANum 1));;
  (c1 sub 1);;
  (free p1_M0);;
  (o1_ZD ::=plan_ZD (Atuple4 (148;128;1;1)));;
  (p1_M4 ::=asgn (OId o1_ZD));;
  (IF (BZd ZD1_2 ZD2) THEN SKIP ELSE CAbt FI);;
  (o1_GD ::=plan_GD (Atuple3 (45;10;40)));;
  (d1 add 1);;
  (o1_JY ::=plan_JY (Atuple3 (41;10;20)));;
  (p1_M4 ::=att (OId o1_GD));;
  (p1_M4 ::=att (OId o1_JY));;
  (IF (BEq (ANum D1) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (o1_QYC ::=plan_QYC (Atuple2 (1;50)));;
  (p1_M4 ::=att (OId o1_QYC));;
  (c1 add 1);;
  (IF (BTr ZD1_2 C1) THEN SKIP ELSE CAbt FI);;
  (o3_ZD ::=plan_ZD (Atuple4 (130;128;0;1)));;
  (p1_M0::reuse (OId o3_ZD));;
  (IF (BZd ZD2 ZD3) THEN SKIP ELSE CAbt FI);;
  (IF (BZd ZD1_2 ZD3) THEN SKIP ELSE CAbt FI);;
  (o3_GY ::=plan_GY (Atuple3 (3;15;10)));;
  (p1_M0 ::=att (OId o3_GY));;
  (IF (BTr ZD3 C3) THEN SKIP ELSE CAbt FI);;
  (IF (BOr (BOr (BMod (triple3_return_first_element GY2) 0) (BMod (triple3_return_first_element GY2) 2) ) (BMod (triple3_return_first_element GY2) 3)) THEN SKIP ELSE CAbt FI);;
  (p2_M0 ::exe (ANum 1));;
  (p2_M0 ::exe (ANum 1));;
  (z2_GY add 1);;
  (p2_M0 ::exe (ANum 1));;
  (c2 sub 1);;
  (free p2_M0);;
  (o2_ZD ::=plan_ZD (Atuple4 (135;143;0;1)));;
  (p2_M5 ::=asgn (OId o2_ZD));;
  (IF (BZd ZD3 ZD2_2) THEN SKIP ELSE CAbt FI);;
  (IF (BZd ZD1_2 ZD2_2) THEN SKIP ELSE CAbt FI);;
  (o2_GD ::=plan_GD (Atuple3 (55;20;40)));;
  (p2_M5 ::=att (OId o2_GD));;
  (d2 add 1);;
  (o2_JY ::=plan_JY (Atuple3 (51;20;20)));;
  (p2_M5 ::=att (OId o2_JY));;
  (IF (BEq (ANum D2) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (o2_TF ::=plan_TF (Atuple3 (51;20;20)));;
  (p2_M5 ::=att (OId o2_TF));;
  (IF (BEq (ANum D2) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (o2_QYC ::=plan_QYC (Atuple2 (1;60)));;
  (p2_M5 ::=att (OId o2_QYC));;
  (c2 add 1);;
  (IF (BTr ZD2_2 C2) THEN SKIP ELSE CAbt FI);;
  (IF (BOr (BOr (BMod (triple3_return_first_element GY3) 0) (BMod (triple3_return_first_element GY3) 2) ) (BMod (triple3_return_first_element GY3) 3)) THEN SKIP ELSE CAbt FI);;
  (p1_M0 ::exe (ANum 1));;
  (p1_M0 ::exe (ANum 1));;
  (z3_GY add 1);;
  (free p1_M0);;          
  (o3_ZD ::=plan_ZD (Atuple4 (130;130;0;1)));;
  (p3_M5 ::=asgn (OId o3_ZD));;
  (IF (BZd ZD1_2 ZD3_2) THEN SKIP ELSE CAbt FI);;
  (IF (BZd ZD2_2 ZD3_2) THEN SKIP ELSE CAbt FI);;
  (o3_GD ::=plan_GD (Atuple3 (65;25;40)));;
  (p3_M5 ::=att (OId o3_GD));;
  (d3 add 1);;
  (o3_JY ::=plan_JY (Atuple3 (51;25;20)));;
  (p3_M5 ::=att (OId o3_JY));;
  (IF (BEq (ANum D3) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (o3_TF ::=plan_TF (Atuple3 (51;25;20)));;
  (p3_M5 ::=att (OId o3_TF));;
  (IF (BEq (ANum D3) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (IF (BTr ZD3_2 C3) THEN SKIP ELSE CAbt FI);;
  (IF (BAnd (BLe (ANum (triple3_return_first_element GY1)) (ANum (triple3_return_first_element JY1))) (BLe (ANum (triple3_return_first_element GY1)) (ANum (triple3_return_first_element TF1)))) THEN SKIP ELSE CAbt FI);;
  (IF (BOr (BMod (triple3_return_first_element GD1) 4) (BMod (triple3_return_first_element GD1) 5) ) THEN SKIP ELSE CAbt FI);;
  (p1_M4 ::exe (ANum 1));;
  (p1_M4 ::exe (ANum 1));;
  (z1_GD add 1);;
  (p1_M4 ::exe (ANum 1));;
  (d1 sub 1);;
  (z1_JY add 1);;
  (p1_M4 ::exe (ANum 1));;
  (c1 sub 1);;
  (free p1_M4);;
  (o1_ZD ::=plan_ZD (Atuple4 (120;145;1;1)));;
  (p1_M8 ::=asgn (OId o1_ZD));;
  (IF (BZd ZD2_2 ZD1_3) THEN SKIP ELSE CAbt FI);;
  (IF (BZd ZD3_2 ZD1_3) THEN SKIP ELSE CAbt FI);;
  (o1_GD ::=plan_GD (Atuple3 (88;50;40)));;
  (p1_M8 ::=att (OId o1_GD));;
  (d1 add 1);;
  (o1_TF ::=plan_TF (Atuple3 (81;50;20)));;
  (p1_M8 ::=att (OId o1_TF));;
  (IF (BEq (ANum D1) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (o1_QYC ::=plan_QYC (Atuple2 (1;90)));;
  (c1 add 1);;
  (IF (BTr ZD1_3 C1) THEN SKIP ELSE CAbt FI);;
  (p1_M8 ::=att (OId o1_QYC));;
  (IF (BAnd (BLe (ANum (triple3_return_first_element GY2)) (ANum (triple3_return_first_element JY2))) (BLe (ANum (triple3_return_first_element GY2)) (ANum (triple3_return_first_element TF2)))) THEN SKIP ELSE CAbt FI);;
  (IF (BMod (triple3_return_first_element GD2) 5) THEN SKIP ELSE CAbt FI);;
  (p2_M5 ::exe (ANum 1));;
  (p2_M5 ::exe (ANum 1));;
  (z2_GD add 1);;
  (p2_M5 ::exe (ANum 1));;
  (z2_JY add 1);;
  (p2_M5 ::exe (ANum 1));;
  (d2 sub 1);;
  (z2_TF add 1);;
  (p2_M5 ::exe (ANum 1));;
  (c2 sub 1);;
  (free p2_M5);;
  (IF (BAnd (BLe (ANum (triple3_return_first_element GY3)) (ANum (triple3_return_first_element JY3))) (BLe (ANum (triple3_return_first_element GY3)) (ANum (triple3_return_first_element TF3)))) THEN SKIP ELSE CAbt FI);;
  (IF (BMod (triple3_return_first_element GD3) 5) THEN SKIP ELSE CAbt FI);;
  (p3_M5 ::exe (ANum 1));;
  (p3_M5 ::exe (ANum 1));;
  (d3 sub 1);;
  (z3_GD add 1);;
  (p3_M5 ::exe (ANum 1));;
  (z3_JY add 1);;
  (p3_M5 ::exe (ANum 1));;
  (z3_TF add 1);;
  (free p3_M5);;
  (IF (BAnd (BLe (ANum (triple3_return_first_element GY1)) (ANum (triple3_return_first_element JY1))) (BLe (ANum (triple3_return_first_element GY1)) (ANum (triple3_return_first_element TF1)))) THEN SKIP ELSE CAbt FI);;
  (IF (BOr (BMod (triple3_return_first_element GD1_2) 8) (BMod (triple3_return_first_element GD1_2) 9) ) THEN SKIP ELSE CAbt FI);;
  (p1_M8 ::exe (ANum 1));;
  (p1_M8 ::exe (ANum 1));;
  (z1_GD add 1);;
  (d1 sub 1);;
  (p1_M8 ::exe (ANum 1));;
  (z1_TF add 1);;
  (p1_M8 ::exe (ANum 1));;
  (c1 sub 1);;
  (free p1_M8);;
  (SKIP).

Fact EX_JZ_Three_Correct :

forall (oloc_1 oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 oloc_8 oloc_9 oloc_10 oloc_11 oloc_12 oloc_13 :nat)
       (rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
        rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 rloc_25 
        rloc_26 rloc_27 rloc_28 rloc_29 rloc_30 rloc_31 rloc_32 rloc_33 rloc_34 rloc_35 rloc_36 rloc_37 
        rloc_38 rloc_39 rloc_40 :nat),

neq0_13 oloc_1 oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 oloc_8 oloc_9 oloc_10 oloc_11 oloc_12 oloc_13 ->
neq0_40 rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
        rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 rloc_25 
        rloc_26 rloc_27 rloc_28 rloc_29 rloc_30 rloc_31 rloc_32 rloc_33 rloc_34 rloc_35 rloc_36 rloc_37
        rloc_38 rloc_39 rloc_40 ->

neq_13 oloc_1 oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 oloc_8 oloc_9 oloc_10 oloc_11 oloc_12 oloc_13 ->
neq_40 rloc_1 rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
       rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 rloc_25 
       rloc_26 rloc_27 rloc_28 rloc_29 rloc_30 rloc_31 rloc_32 rloc_33 rloc_34 rloc_35 rloc_36 rloc_37
       rloc_38 rloc_39 rloc_40 -> 

empty_st =[
  EX_JZ_Three
]=> St (o1_QYC !so-> 0; o1_TF !so-> 0; o1_GD !so-> 0; o1_ZD !so-> 0; o3_TF !so-> 0; o3_JY !so-> 0; o3_GD !so-> 0;      
        o3_ZD !so-> 0; o2_QYC !so-> 0; o2_TF !so-> 0; o2_JY !so-> 0; o2_GD !so-> 0; o2_ZD !so-> 0; o1_JY !so-> 0;   
        o3_GY !so-> 0; o2_GY !so-> 0; o1_GY !so-> 0; emp_sO,
        c1 !sv-> 0; z1_TF !sv-> 1; d1 !sv-> 0; z1_GD !sv-> 2; z3_TF !sv-> 1; z3_JY !sv-> 1; z3_GD !sv->1; d3 !sv-> 0;
        c2 !sv-> 0; z2_TF !sv-> 1; d2 !sv-> 0; z2_JY !sv-> 1; z2_GD !sv-> 1; c1 !sv-> 0; z1_JY !sv-> 1; z3_GY !sv-> 1; 
        z2_GY !sv-> 1; z1_GY !sv-> 1; emp_sV,
        p1_M8 !ss-> on; p3_M5 !ss-> on; p2_M5 !ss-> on; p1_M4 !ss-> on; p1_M0 !ss-> on; p2_M0 !ss-> on; emp_sS,
        emp_heapR,emp_heapO).

Proof.
  unfold neq0_13, neq0_40, neq_13, neq_40.
  intros oloc_1 oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 oloc_8 oloc_9 oloc_10 oloc_11 oloc_12 oloc_13.
  intros rloc_1 rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
         rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 rloc_25 
         rloc_26 rloc_27 rloc_28 rloc_29 rloc_30 rloc_31 rloc_32 rloc_33 rloc_34 rloc_35 rloc_36 rloc_37
         rloc_38 rloc_39 rloc_40.
  intros H_neq0_oloc H_neq0_rloc H_neq_oloc H_neq_rloc.
  destruct H_neq0_oloc as (H1_o & H2_o & H3_o & H4_o & H5_o & H6_o & H7_o & H8_o & H9_o & H10_o & H11_o & H12_o & H13_o).
  destruct H_neq0_rloc as (H1_r & H2_r & H3_r & H4_r & H5_r & H6_r & H7_r & H8_r & H9_r & H10_r & H11_r & H12_r & H13_r & 
                           H14_r & H15_r & H16_r & H17_r & H18_r & H19_r & H20_r & H21_r & H22_r & H23_r & H24_r & H25_r & 
                           H26_r & H27_r & H28_r & H29_r & H30_r & H31_r & H32_r & H33_r & H34_r & H35_r & H36_r & H37_r & 
                           H38_r & H39_r & H40_r).
  destruct H_neq_oloc as (
  Ho1_2 & Ho1_3 & Ho1_4 & Ho1_5 & Ho1_6 & Ho1_7 & Ho1_8 & Ho1_9 & Ho1_10 & Ho1_11 & Ho1_12 & Ho1_13 &
  Ho2_3 & Ho2_4 & Ho2_5 & Ho2_6 & Ho2_7 & Ho2_8 & Ho2_9 & Ho2_10 & Ho2_11 & Ho2_12 & Ho2_13 &
  Ho3_4 & Ho3_5 & Ho3_6 & Ho3_7 & Ho3_8 & Ho3_9 & Ho3_10 & Ho3_11 & Ho3_12 & Ho3_13 &
  Ho4_5 & Ho4_6 & Ho4_7 & Ho4_8 & Ho4_9 & Ho4_10 & Ho4_11 & Ho4_12 & Ho4_13 &
  Ho5_6 & Ho5_7 & Ho5_8 & Ho5_9 & Ho5_10 & Ho5_11 & Ho5_12 & Ho5_13 &
  Ho6_7 & Ho6_8 & Ho6_9 & Ho6_10 & Ho6_11 & Ho6_12 & Ho6_13 &
  Ho7_8 & Ho7_9 & Ho7_10 & Ho7_11 & Ho7_12 & Ho7_13 &
  Ho8_9 & Ho8_10 & Ho8_11 & Ho8_12 & Ho8_13 &
  Ho9_10 & Ho9_11 & Ho9_12 & Ho9_13 &
  Ho10_11 & Ho10_12 & Ho10_13 &
  Ho11_12 & Ho11_13 &
  Ho12_13 
  ).
  destruct H_neq_rloc as (
  Hr1_2 & Hr1_3 & Hr1_4 & Hr1_5 & Hr1_6 & Hr1_7 & Hr1_8 & Hr1_9 & Hr1_10 & Hr1_11 & Hr1_12 & Hr1_13 & Hr1_14 & Hr1_15 & Hr1_16 & Hr1_17 & Hr1_18 & Hr1_19 & Hr1_20 & Hr1_21 & Hr1_22 & Hr1_23 & Hr1_24 & Hr1_25 & Hr1_26 & Hr1_27 & Hr1_28 & Hr1_29 & Hr1_30 & Hr1_31 & Hr1_32 & Hr1_33 & Hr1_34 & Hr1_35 & Hr1_36 & Hr1_37 & Hr1_38 & Hr1_39 & Hr1_40 &
  Hr2_3 & Hr2_4 & Hr2_5 & Hr2_6 & Hr2_7 & Hr2_8 & Hr2_9 & Hr2_10 & Hr2_11 & Hr2_12 & Hr2_13 & Hr2_14 & Hr2_15 & Hr2_16 & Hr2_17 & Hr2_18 & Hr2_19 & Hr2_20 & Hr2_21 & Hr2_22 & Hr2_23 & Hr2_24 & Hr2_25 & Hr2_26 & Hr2_27 & Hr2_28 & Hr2_29 & Hr2_30 & Hr2_31 & Hr2_32 & Hr2_33 & Hr2_34 & Hr2_35 & Hr2_36 & Hr2_37 & Hr2_38 & Hr2_39 & Hr2_40 &
  Hr3_4 & Hr3_5 & Hr3_6 & Hr3_7 & Hr3_8 & Hr3_9 & Hr3_10 & Hr3_11 & Hr3_12 & Hr3_13 & Hr3_14 & Hr3_15 & Hr3_16 & Hr3_17 & Hr3_18 & Hr3_19 & Hr3_20 & Hr3_21 & Hr3_22 & Hr3_23 & Hr3_24 & Hr3_25 & Hr3_26 & Hr3_27 & Hr3_28 & Hr3_29 & Hr3_30 & Hr3_31 & Hr3_32 & Hr3_33 & Hr3_34 & Hr3_35 & Hr3_36 & Hr3_37 & Hr3_38 & Hr3_39 & Hr3_40 &
  Hr4_5 & Hr4_6 & Hr4_7 & Hr4_8 & Hr4_9 & Hr4_10 & Hr4_11 & Hr4_12 & Hr4_13 & Hr4_14 & Hr4_15 & Hr4_16 & Hr4_17 & Hr4_18 & Hr4_19 & Hr4_20 & Hr4_21 & Hr4_22 & Hr4_23 & Hr4_24 & Hr4_25 & Hr4_26 & Hr4_27 & Hr4_28 & Hr4_29 & Hr4_30 & Hr4_31 & Hr4_32 & Hr4_33 & Hr4_34 & Hr4_35 & Hr4_36 & Hr4_37 & Hr4_38 & Hr4_39 & Hr4_40 &
  Hr5_6 & Hr5_7 & Hr5_8 & Hr5_9 & Hr5_10 & Hr5_11 & Hr5_12 & Hr5_13 & Hr5_14 & Hr5_15 & Hr5_16 & Hr5_17 & Hr5_18 & Hr5_19 & Hr5_20 & Hr5_21 & Hr5_22 & Hr5_23 & Hr5_24 & Hr5_25 & Hr5_26 & Hr5_27 & Hr5_28 & Hr5_29 & Hr5_30 & Hr5_31 & Hr5_32 & Hr5_33 & Hr5_34 & Hr5_35 & Hr5_36 & Hr5_37 & Hr5_38 & Hr5_39 & Hr5_40 &
  Hr6_7 & Hr6_8 & Hr6_9 & Hr6_10 & Hr6_11 & Hr6_12 & Hr6_13 & Hr6_14 & Hr6_15 & Hr6_16 & Hr6_17 & Hr6_18 & Hr6_19 & Hr6_20 & Hr6_21 & Hr6_22 & Hr6_23 & Hr6_24 & Hr6_25 & Hr6_26 & Hr6_27 & Hr6_28 & Hr6_29 & Hr6_30 & Hr6_31 & Hr6_32 & Hr6_33 & Hr6_34 & Hr6_35 & Hr6_36 & Hr6_37 & Hr6_38 & Hr6_39 & Hr6_40 &
  Hr7_8 & Hr7_9 & Hr7_10 & Hr7_11 & Hr7_12 & Hr7_13 & Hr7_14 & Hr7_15 & Hr7_16 & Hr7_17 & Hr7_18 & Hr7_19 & Hr7_20 & Hr7_21 & Hr7_22 & Hr7_23 & Hr7_24 & Hr7_25 & Hr7_26 & Hr7_27 & Hr7_28 & Hr7_29 & Hr7_30 & Hr7_31 & Hr7_32 & Hr7_33 & Hr7_34 & Hr7_35 & Hr7_36 & Hr7_37 & Hr7_38 & Hr7_39 & Hr7_40 &
  Hr8_9 & Hr8_10 & Hr8_11 & Hr8_12 & Hr8_13 & Hr8_14 & Hr8_15 & Hr8_16 & Hr8_17 & Hr8_18 & Hr8_19 & Hr8_20 & Hr8_21 & Hr8_22 & Hr8_23 & Hr8_24 & Hr8_25 & Hr8_26 & Hr8_27 & Hr8_28 & Hr8_29 & Hr8_30 & Hr8_31 & Hr8_32 & Hr8_33 & Hr8_34 & Hr8_35 & Hr8_36 & Hr8_37 & Hr8_38 & Hr8_39 & Hr8_40 &
  Hr9_10 & Hr9_11 & Hr9_12 & Hr9_13 & Hr9_14 & Hr9_15 & Hr9_16 & Hr9_17 & Hr9_18 & Hr9_19 & Hr9_20 & Hr9_21 & Hr9_22 & Hr9_23 & Hr9_24 & Hr9_25 & Hr9_26 & Hr9_27 & Hr9_28 & Hr9_29 & Hr9_30 & Hr9_31 & Hr9_32 & Hr9_33 & Hr9_34 & Hr9_35 & Hr9_36 & Hr9_37 & Hr9_38 & Hr9_39 & Hr9_40 &
  Hr10_11 & Hr10_12 & Hr10_13 & Hr10_14 & Hr10_15 & Hr10_16 & Hr10_17 & Hr10_18 & Hr10_19 & Hr10_20 & Hr10_21 & Hr10_22 & Hr10_23 & Hr10_24 & Hr10_25 & Hr10_26 & Hr10_27 & Hr10_28 & Hr10_29 & Hr10_30 & Hr10_31 & Hr10_32 & Hr10_33 & Hr10_34 & Hr10_35 & Hr10_36 & Hr10_37 & Hr10_38 & Hr10_39 & Hr10_40 &
  Hr11_12 & Hr11_13 & Hr11_14 & Hr11_15 & Hr11_16 & Hr11_17 & Hr11_18 & Hr11_19 & Hr11_20 & Hr11_21 & Hr11_22 & Hr11_23 & Hr11_24 & Hr11_25 & Hr11_26 & Hr11_27 & Hr11_28 & Hr11_29 & Hr11_30 & Hr11_31 & Hr11_32 & Hr11_33 & Hr11_34 & Hr11_35 & Hr11_36 & Hr11_37 & Hr11_38 & Hr11_39 & Hr11_40 &
  Hr12_13 & Hr12_14 & Hr12_15 & Hr12_16 & Hr12_17 & Hr12_18 & Hr12_19 & Hr12_20 & Hr12_21 & Hr12_22 & Hr12_23 & Hr12_24 & Hr12_25 & Hr12_26 & Hr12_27 & Hr12_28 & Hr12_29 & Hr12_30 & Hr12_31 & Hr12_32 & Hr12_33 & Hr12_34 & Hr12_35 & Hr12_36 & Hr12_37 & Hr12_38 & Hr12_39 & Hr12_40 &
  Hr13_14 & Hr13_15 & Hr13_16 & Hr13_17 & Hr13_18 & Hr13_19 & Hr13_20 & Hr13_21 & Hr13_22 & Hr13_23 & Hr13_24 & Hr13_25 & Hr13_26 & Hr13_27 & Hr13_28 & Hr13_29 & Hr13_30 & Hr13_31 & Hr13_32 & Hr13_33 & Hr13_34 & Hr13_35 & Hr13_36 & Hr13_37 & Hr13_38 & Hr13_39 & Hr13_40 &
  Hr14_15 & Hr14_16 & Hr14_17 & Hr14_18 & Hr14_19 & Hr14_20 & Hr14_21 & Hr14_22 & Hr14_23 & Hr14_24 & Hr14_25 & Hr14_26 & Hr14_27 & Hr14_28 & Hr14_29 & Hr14_30 & Hr14_31 & Hr14_32 & Hr14_33 & Hr14_34 & Hr14_35 & Hr14_36 & Hr14_37 & Hr14_38 & Hr14_39 & Hr14_40 &
  Hr15_16 & Hr15_17 & Hr15_18 & Hr15_19 & Hr15_20 & Hr15_21 & Hr15_22 & Hr15_23 & Hr15_24 & Hr15_25 & Hr15_26 & Hr15_27 & Hr15_28 & Hr15_29 & Hr15_30 & Hr15_31 & Hr15_32 & Hr15_33 & Hr15_34 & Hr15_35 & Hr15_36 & Hr15_37 & Hr15_38 & Hr15_39 & Hr15_40 &
  Hr16_17 & Hr16_18 & Hr16_19 & Hr16_20 & Hr16_21 & Hr16_22 & Hr16_23 & Hr16_24 & Hr16_25 & Hr16_26 & Hr16_27 & Hr16_28 & Hr16_29 & Hr16_30 & Hr16_31 & Hr16_32 & Hr16_33 & Hr16_34 & Hr16_35 & Hr16_36 & Hr16_37 & Hr16_38 & Hr16_39 & Hr16_40 &
  Hr17_18 & Hr17_19 & Hr17_20 & Hr17_21 & Hr17_22 & Hr17_23 & Hr17_24 & Hr17_25 & Hr17_26 & Hr17_27 & Hr17_28 & Hr17_29 & Hr17_30 & Hr17_31 & Hr17_32 & Hr17_33 & Hr17_34 & Hr17_35 & Hr17_36 & Hr17_37 & Hr17_38 & Hr17_39 & Hr17_40 &
  Hr18_19 & Hr18_20 & Hr18_21 & Hr18_22 & Hr18_23 & Hr18_24 & Hr18_25 & Hr18_26 & Hr18_27 & Hr18_28 & Hr18_29 & Hr18_30 & Hr18_31 & Hr18_32 & Hr18_33 & Hr18_34 & Hr18_35 & Hr18_36 & Hr18_37 & Hr18_38 & Hr18_39 & Hr18_40 &
  Hr19_20 & Hr19_21 & Hr19_22 & Hr19_23 & Hr19_24 & Hr19_25 & Hr19_26 & Hr19_27 & Hr19_28 & Hr19_29 & Hr19_30 & Hr19_31 & Hr19_32 & Hr19_33 & Hr19_34 & Hr19_35 & Hr19_36 & Hr19_37 & Hr19_38 & Hr19_39 & Hr19_40 &
  Hr20_21 & Hr20_22 & Hr20_23 & Hr20_24 & Hr20_25 & Hr20_26 & Hr20_27 & Hr20_28 & Hr20_29 & Hr20_30 & Hr20_31 & Hr20_32 & Hr20_33 & Hr20_34 & Hr20_35 & Hr20_36 & Hr20_37 & Hr20_38 & Hr20_39 & Hr20_40 &
  Hr21_22 & Hr21_23 & Hr21_24 & Hr21_25 & Hr21_26 & Hr21_27 & Hr21_28 & Hr21_29 & Hr21_30 & Hr21_31 & Hr21_32 & Hr21_33 & Hr21_34 & Hr21_35 & Hr21_36 & Hr21_37 & Hr21_38 & Hr21_39 & Hr21_40 &
  Hr22_23 & Hr22_24 & Hr22_25 & Hr22_26 & Hr22_27 & Hr22_28 & Hr22_29 & Hr22_30 & Hr22_31 & Hr22_32 & Hr22_33 & Hr22_34 & Hr22_35 & Hr22_36 & Hr22_37 & Hr22_38 & Hr22_39 & Hr22_40 &
  Hr23_24 & Hr23_25 & Hr23_26 & Hr23_27 & Hr23_28 & Hr23_29 & Hr23_30 & Hr23_31 & Hr23_32 & Hr23_33 & Hr23_34 & Hr23_35 & Hr23_36 & Hr23_37 & Hr23_38 & Hr23_39 & Hr23_40 &
  Hr24_25 & Hr24_26 & Hr24_27 & Hr24_28 & Hr24_29 & Hr24_30 & Hr24_31 & Hr24_32 & Hr24_33 & Hr24_34 & Hr24_35 & Hr24_36 & Hr24_37 & Hr24_38 & Hr24_39 & Hr24_40 &
  Hr25_26 & Hr25_27 & Hr25_28 & Hr25_29 & Hr25_30 & Hr25_31 & Hr25_32 & Hr25_33 & Hr25_34 & Hr25_35 & Hr25_36 & Hr25_37 & Hr25_38 & Hr25_39 & Hr25_40 &
  Hr26_27 & Hr26_28 & Hr26_29 & Hr26_30 & Hr26_31 & Hr26_32 & Hr26_33 & Hr26_34 & Hr26_35 & Hr26_36 & Hr26_37 & Hr26_38 & Hr26_39 & Hr26_40 &
  Hr27_28 & Hr27_29 & Hr27_30 & Hr27_31 & Hr27_32 & Hr27_33 & Hr27_34 & Hr27_35 & Hr27_36 & Hr27_37 & Hr27_38 & Hr27_39 & Hr27_40 &
  Hr28_29 & Hr28_30 & Hr28_31 & Hr28_32 & Hr28_33 & Hr28_34 & Hr28_35 & Hr28_36 & Hr28_37 & Hr28_38 & Hr28_39 & Hr28_40 &
  Hr29_30 & Hr29_31 & Hr29_32 & Hr29_33 & Hr29_34 & Hr29_35 & Hr29_36 & Hr29_37 & Hr29_38 & Hr29_39 & Hr29_40 &
  Hr30_31 & Hr30_32 & Hr30_33 & Hr30_34 & Hr30_35 & Hr30_36 & Hr30_37 & Hr30_38 & Hr30_39 & Hr30_40 &
  Hr31_32 & Hr31_33 & Hr31_34 & Hr31_35 & Hr31_36 & Hr31_37 & Hr31_38 & Hr31_39 & Hr31_40 &
  Hr32_33 & Hr32_34 & Hr32_35 & Hr32_36 & Hr32_37 & Hr32_38 & Hr32_39 & Hr32_40 &
  Hr33_34 & Hr33_35 & Hr33_36 & Hr33_37 & Hr33_38 & Hr33_39 & Hr33_40 &
  Hr34_35 & Hr34_36 & Hr34_37 & Hr34_38 & Hr34_39 & Hr34_40 &
  Hr35_36 & Hr35_37 & Hr35_38 & Hr35_39 & Hr35_40 &
  Hr36_37 & Hr36_38 & Hr36_39 & Hr36_40 &
  Hr37_38 & Hr37_39 & Hr37_40 &
  Hr38_39 & Hr38_40 &
  Hr39_40 
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
   eapply E_Sasgn  with (loc := oloc_1).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_2).
   simpl. reflexivity.
   rewrite sS_update_eq; reflexivity.
   intros. apply SafeinHo1_3.
   auto. auto. auto. auto. auto. auto. auto. 
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl. reflexivity.
   simpl. rewrite sS_update_eq;  reflexivity.
   intros. apply SafeinHo2_3.
   auto. auto. auto. auto. auto. auto. auto. 
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
   eapply E_Oplan_Tuple4 with (loc := oloc_4) (loc1 := rloc_10) (loc2 := rloc_11) (loc3 := rloc_12)(loc4 := rloc_13).
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
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. 

   eapply E_Seq.
   eapply E_IfTure.
   simpl. 
   unfold unfoldWing.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_5) (loc1 := rloc_14) (loc2 := rloc_15) (loc3 := rloc_16).      
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
   apply sym_not_eq; apply Hr13_14.
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
   apply sym_not_eq; apply Hr13_15.
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
   apply sym_not_eq; apply Hr13_16.
   apply sym_not_eq; apply Hr12_16.
   apply sym_not_eq; apply Hr11_16.
   apply sym_not_eq; apply Hr10_16. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. 

   eapply E_Seq.
   eapply E_Oplan_Tuple2 with (loc := oloc_6) (loc1 := rloc_17) (loc2 := rloc_18).
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
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity.
   apply sym_not_eq; apply Hr4_17.
   apply sym_not_eq; apply Hr3_17.
   apply sym_not_eq; apply Hr2_17.
   apply sym_not_eq; apply Hr1_17.
   apply sym_not_eq; apply Hr7_17.
   apply sym_not_eq; apply Hr6_17.
   apply sym_not_eq; apply Hr5_17.
   apply sym_not_eq; apply Hr9_17.
   apply sym_not_eq; apply Hr8_17. 
   apply sym_not_eq; apply Hr13_17.
   apply sym_not_eq; apply Hr12_17.
   apply sym_not_eq; apply Hr11_17.
   apply sym_not_eq; apply Hr10_17.
   apply sym_not_eq; apply Hr16_17. 
   apply sym_not_eq; apply Hr15_17.
   apply sym_not_eq; apply Hr14_17.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
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
   apply sym_not_eq; apply Hr4_18.
   apply sym_not_eq; apply Hr3_18.
   apply sym_not_eq; apply Hr2_18.
   apply sym_not_eq; apply Hr1_18.
   apply sym_not_eq; apply Hr7_18.
   apply sym_not_eq; apply Hr6_18.
   apply sym_not_eq; apply Hr5_18.
   apply sym_not_eq; apply Hr9_18.
   apply sym_not_eq; apply Hr8_18. 
   apply sym_not_eq; apply Hr13_18.
   apply sym_not_eq; apply Hr12_18.
   apply sym_not_eq; apply Hr11_18.
   apply sym_not_eq; apply Hr10_18.
   apply sym_not_eq; apply Hr16_18. 
   apply sym_not_eq; apply Hr15_18.
   apply sym_not_eq; apply Hr14_18.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto.

   eapply E_Seq.
   eapply E_Sasgn  with (loc := oloc_4).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_5).
   simpl. reflexivity.
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo1_3; auto.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_6).
   simpl. reflexivity.
   simpl; rewrite sS_update_eq;  reflexivity.
   intros. 
   apply SafeinHo2_3; auto.
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
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_1)(e :=o1_ZD).
   rewrite sS_update_neq. 
   rewrite sS_update_eq. reflexivity.
   simpl; discriminate.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq.
   auto.
   discriminate. discriminate. discriminate. discriminate. discriminate. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto.
   intros. 
   apply SafeinHr4_18; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow_3.  rewrite sO_update_shadow_7.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_2)(e :=o1_GY).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto.
   intros. 
   apply SafeinHr3_14; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_7.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_3)(e :=o1_QYC).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto.
   intros. 
   apply SafeinHr2_11; auto.
   simpl.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. 
   rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_7.

   eapply E_Seq.
   eapply E_Rsub_V. auto.
   simpl; rewrite sV_update_shadow_4.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Oplan_Tuple4 with (loc := oloc_1) (loc1 := rloc_1) (loc2 := rloc_2) (loc3 := rloc_3)(loc4 := rloc_4).
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
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto.
   rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Sasgn  with (loc := oloc_1).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_IfTure.
   simpl. 
   unfold unfoldWing.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_2) (loc1 := rloc_5) (loc2 := rloc_6) (loc3 := rloc_7).
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
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_3) (loc1 := rloc_19) (loc2 := rloc_20) (loc3 := rloc_21).
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
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_2).
   simpl. reflexivity.
   rewrite sS_update_eq;  reflexivity.
   intros. apply SafeinHo1_3.
   auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl. reflexivity.
   simpl; rewrite sS_update_eq;  reflexivity.
   intros. apply SafeinHo2_3.
   auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple2 with (loc := oloc_7) (loc1 := rloc_8) (loc2 := rloc_9).
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
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto.  
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto.
   rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_7).
   simpl. reflexivity.
   rewrite sS_update_eq;  reflexivity.
   intros. 
   apply SafeinHo3_4; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   rewrite sV_update_shadow_3.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl. 
   unfold Tractor_need.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple4 with (loc := oloc_8) (loc1 := rloc_25) (loc2 := rloc_26) (loc3 := rloc_27)(loc4 := rloc_28).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto.
 
   eapply E_Seq.
   eapply E_Sreuse with (e := o3_ZD).
   rewrite sS_update_neq.
   rewrite sS_update_eq;  reflexivity.
   simpl; discriminate.
   rewrite sO_update_eq.
   reflexivity.
   rewrite sS_update_shadow_3.

   eapply E_Seq.
   eapply E_IfTure.
   simpl. 
   unfold unfoldWing.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_IfTure.
   simpl. 
   unfold unfoldWing.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_9) (loc1 := rloc_22) (loc2 := rloc_23) (loc3 := rloc_24).      
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
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_9).
   simpl. reflexivity.
   rewrite sS_update_eq;  reflexivity.
   intros. 
   apply SafeinHo1_2; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl. 
   unfold Tractor_need.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_4)(e :=o2_ZD).
   rewrite sS_update_neq.
   rewrite sS_update_neq.
   rewrite sS_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto.
   intros. 
   apply SafeinHr4_28; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow_4.  rewrite sO_update_shadow_11.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_5)(e :=o2_GY).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto.
   intros. 
   apply SafeinHr3_24; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_11.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_6)(e :=o2_QYC).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. 
   intros. 
   apply SafeinHr2_21; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. 
   rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_11.

   eapply E_Seq.
   eapply E_Rsub_V. auto.
   simpl; rewrite sV_update_shadow_6.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Oplan_Tuple4 with (loc := oloc_4) (loc1 := rloc_13) (loc2 := rloc_14) (loc3 := rloc_15)(loc4 := rloc_16).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto.
   rewrite sO_update_shadow_3.

   eapply E_Seq.
   eapply E_Sasgn  with (loc := oloc_4).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_IfTure.
   simpl. 
   unfold unfoldWing.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_IfTure.
   simpl. 
   unfold unfoldWing.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_5) (loc1 := rloc_10) (loc2 := rloc_11) (loc3 := rloc_12).
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
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_5).
   simpl. reflexivity.
   rewrite sS_update_eq;  reflexivity.
   intros. apply SafeinHo1_2.
   auto. auto. auto. auto. auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_6) (loc1 := rloc_29) (loc2 := rloc_30) (loc3 := rloc_31).
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
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq.
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq.
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
    rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   rewrite hR_update_neq.
   rewrite hR_update_neq.
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
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_6).
   simpl. reflexivity.
   rewrite sS_update_eq;  reflexivity.
   intros. apply SafeinHo2_3.
   auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_10) (loc1 := rloc_32) (loc2 := rloc_33)(loc3 := rloc_34).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.   
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.   
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.   
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_10).
   simpl. reflexivity.
   rewrite sS_update_eq;  reflexivity.
   intros. 
   apply SafeinHo3_4; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple2 with (loc := oloc_11) (loc1 := rloc_17) (loc2 := rloc_18).
   simpl; reflexivity.
   simpl; reflexivity.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.   
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.   
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite sO_update_shadow_5.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_11).
   simpl. reflexivity.
   rewrite sS_update_eq;  reflexivity.
   intros. 
   apply SafeinHo4_5; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   rewrite sV_update_shadow_3.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl. 
   unfold Tractor_need.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_8)(e :=o3_ZD).
   rewrite sS_update_neq.
   rewrite sS_update_neq.
   rewrite sS_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto.
   intros. 
   apply SafeinHr4_22; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow_4.  rewrite sO_update_shadow_9.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_9)(e :=o3_GY).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto.
   intros. 
   apply SafeinHr3_18; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow. rewrite sO_update_shadow_9.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Oplan_Tuple4 with (loc := oloc_8) (loc1 := rloc_25) (loc2 := rloc_26) (loc3 := rloc_27)(loc4 := rloc_28).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.  
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite sO_update_shadow_2.

   eapply E_Seq.
   eapply E_Sasgn  with (loc := oloc_8).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_IfTure.
   simpl. 
   unfold unfoldWing.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_IfTure.
   simpl. 
   unfold unfoldWing.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_9) (loc1 := rloc_22) (loc2 := rloc_23) (loc3 := rloc_24).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
     
   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_9).
   simpl. reflexivity.
   rewrite sS_update_eq; reflexivity.
   intros. apply SafeinHo1_2.
   auto. auto. auto. auto. auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_12) (loc1 := rloc_35) (loc2 := rloc_36) (loc3 := rloc_37).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity.  
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_12).
   simpl. reflexivity.
   rewrite sS_update_eq; reflexivity.
   intros. apply SafeinHo2_3.
   auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_13) (loc1 := rloc_38) (loc2 := rloc_39)(loc3 := rloc_40).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_13).
   simpl. reflexivity.
   rewrite sS_update_eq; reflexivity.
   intros. apply SafeinHo3_4.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl. 
   unfold Tractor_need.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_1)(e :=o1_ZD).
   rewrite sS_update_neq.
   rewrite sS_update_neq.
   rewrite sS_update_neq.
   rewrite sS_update_neq.
   rewrite sS_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   intros. 
   apply SafeinHr4_40; auto.
   simpl.
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.   
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow_6.  rewrite sO_update_shadow_16.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_2)(e :=o1_GD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. 
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   intros. 
   apply SafeinHr3_36; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_16.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_3)(e :=o1_JY).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   intros. 
   apply SafeinHr3_33; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_16.

   eapply E_Seq.
   eapply E_Rsub_V. auto.
   simpl; rewrite sV_update_shadow_9.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_7)(e :=o1_QYC).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. 
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   intros. 
   apply SafeinHr2_30; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_16.

   eapply E_Seq.
   eapply E_Rsub_V. auto.
   simpl; rewrite sV_update_shadow_10.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Oplan_Tuple4 with (loc := oloc_1) (loc1 := rloc_1) (loc2 := rloc_2) (loc3 := rloc_3)(loc4 := rloc_4).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Sasgn  with (loc := oloc_1).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_IfTure.
   simpl. 
   unfold unfoldWing.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_IfTure.
   simpl. 
   unfold unfoldWing.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_2) (loc1 := rloc_5) (loc2 := rloc_6) (loc3 := rloc_7).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_2).
   simpl. reflexivity.
   rewrite sS_update_eq; reflexivity.
   intros. apply SafeinHo1_2.
   auto. auto. auto. auto. auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   rewrite sV_update_shadow_4.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_3) (loc1 := rloc_19) (loc2 := rloc_20) (loc3 := rloc_21).
   simpl; reflexivity. 
   simpl; reflexivity. 
   simpl; reflexivity. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. 
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.   
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl. reflexivity.
   rewrite sS_update_eq; reflexivity.
   intros. apply SafeinHo2_3.
   auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple2 with (loc := oloc_7) (loc1 := rloc_8) (loc2 := rloc_9).
   simpl; reflexivity.
   simpl; reflexivity.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.    
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.  
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite sO_update_shadow_4.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl. 
   unfold Tractor_need.
   simpl. reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_7).
   simpl. reflexivity.
   rewrite sS_update_eq; reflexivity.
   intros. apply SafeinHo3_4.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_4)(e :=o2_ZD).
   rewrite sS_update_neq.
   rewrite sS_update_neq.
   rewrite sS_update_neq.
   rewrite sS_update_neq.
   rewrite sS_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq. 
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_eq. reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   intros. 
   apply SafeinHr4_40; auto.
   simpl.
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.   
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow_6.  rewrite sO_update_shadow_16.
   
   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_5)(e :=o2_GD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. 
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   intros. 
   apply SafeinHr3_36; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_16.
   
   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_6)(e :=o2_JY).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   intros. 
   apply SafeinHr3_33; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_16.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_10)(e :=o2_TF).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. 
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   intros. 
   apply SafeinHr3_30; auto.
   simpl. 
   rewrite hO_remove_neq.   
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_16.

   eapply E_Seq.
   eapply E_Rsub_V. auto.
   simpl; rewrite sV_update_shadow_12.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_11)(e :=o2_QYC).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto. auto. 
   intros. 
   apply SafeinHr2_27; auto.
   simpl. 
   rewrite hO_remove_neq. rewrite hO_remove_neq.   
   rewrite hO_remove_neq. rewrite hO_remove_neq.
   rewrite hO_remove_neq. rewrite hO_remove_neq.
   rewrite hO_remove_neq. rewrite hO_remove_neq. 
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. 
   rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_16.

   eapply E_Seq.
   eapply E_Rsub_V. auto.
   simpl; rewrite sV_update_shadow_13.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_8)(e :=o3_ZD).
   rewrite sS_update_neq. 
   rewrite sS_update_neq. 
   rewrite sS_update_neq. 
   rewrite sS_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. 
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. 
   rewrite hO_update_eq.
   reflexivity.
   auto. auto. auto. auto. auto. auto. auto.
   intros. 
   apply SafeinHr4_25; auto.
   simpl.  
   rewrite hO_remove_neq. rewrite hO_remove_neq.
   rewrite hO_remove_neq. rewrite hO_remove_neq.
   rewrite hO_remove_neq. rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow_5.  rewrite sO_update_shadow_15.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_9)(e :=o3_GD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. 
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity. 
   auto. auto. auto. auto. auto. auto.
   intros. 
   apply SafeinHr3_21; auto.
   simpl. 
   rewrite hO_remove_neq. rewrite hO_remove_neq.   
   rewrite hO_remove_neq. rewrite hO_remove_neq.
   rewrite hO_remove_neq. rewrite hO_remove_neq.
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_15.

   eapply E_Seq.
   eapply E_Rsub_V. auto.
   simpl; rewrite sV_update_shadow_12.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_12)(e :=o3_JY).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. 
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. 
   rewrite hO_update_eq.
   reflexivity. 
   auto. auto. auto. auto. auto. 
   intros. 
   apply SafeinHr3_18; auto.
   simpl. 
   rewrite hO_remove_neq. rewrite hO_remove_neq.   
   rewrite hO_remove_neq. rewrite hO_remove_neq.
   rewrite hO_remove_neq. 
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_15.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_13)(e :=o3_TF).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. 
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity. 
   auto. auto. auto. auto. 
   intros. 
   apply SafeinHr3_15; auto.
   simpl. 
   rewrite hO_remove_neq. rewrite hO_remove_neq.   
   rewrite hO_remove_neq. rewrite hO_remove_neq. 
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_15.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_1)(e :=o1_ZD).
   rewrite sS_update_neq.
   rewrite sS_update_neq.
   rewrite sS_update_eq. reflexivity.
   simpl; discriminate.
   simpl; discriminate.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq. 
   rewrite hO_update_eq.
   reflexivity. 
   auto. auto. auto.  
   intros. 
   apply SafeinHr4_12; auto.
   simpl. 
   rewrite hO_remove_neq. rewrite hO_remove_neq.   
   rewrite hO_remove_neq.  
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow_4.  rewrite sO_update_shadow_14.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_2)(e :=o1_GD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_eq.
   reflexivity. 
   auto. auto.
   intros. 
   apply SafeinHr3_8; auto.
   simpl. 
   rewrite hO_remove_neq. rewrite hO_remove_neq.   
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_14.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   simpl; rewrite sV_update_shadow_15.

   eapply E_Seq.
   eapply E_Rsub_V. auto.
   simpl; rewrite sV_update_shadow_13.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_3)(e :=o1_TF).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq. 
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_neq. 
   rewrite hO_update_eq.
   reflexivity. 
   auto. 
   intros. 
   apply SafeinHr3_5; auto.
   simpl. 
   rewrite hO_remove_neq. 
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_neq. rewrite hR_remove_neq.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_14.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_7)(e :=o1_QYC).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq. reflexivity.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   simpl; discriminate. simpl; discriminate.
   rewrite hO_update_eq.
   reflexivity. 
   intros. apply SafeinHr2_2.
   auto. auto. auto. auto.
   simpl. 
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_work. rewrite hR_remove_work.
   rewrite sS_update_shadow.  rewrite sO_update_shadow_14.

   eapply E_Seq.
   eapply E_Rsub_V. auto.
   simpl; rewrite sV_update_shadow_14.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Skip.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. 
   unfold not_in_domO. auto.
   auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. 
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. 
   rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq.
   auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. 
   rewrite hO_update_neq. rewrite hO_update_neq. rewrite hO_update_neq.
   rewrite hO_update_neq.
   auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domO. auto.
   auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. 
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto.
   unfold not_in_domR. auto.
   unfold not_in_domR. rewrite hR_update_neq. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   auto. auto. auto. auto.
   unfold not_in_domO. auto.
   auto. auto. auto. auto. auto.
   Unshelve.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
Qed.

  



























