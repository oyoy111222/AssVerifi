Require Import CSSsVerification9.
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

(* 样式_2运行流程案例 *)
Definition Example_9 :=
  (o1_ZD ::=plan_ZD (Atuple4 (274;536;1;1)));;
  (P1 ::=asgn (OId o1_ZD));;
  (o2_ZD ::=plan_ZD (Atuple4 (291;546;1;1)));;
  (P2 ::=asgn (OId o2_ZD));;
  (o2_GRDZT ::=plan_GRDZT (Atuple3 (80;(large_to_nat 8220);(large_to_nat 8820))));;
  (P2 ::=att (OId o2_GRDZT));;
  (IF (BEq ((ANum (triple4_return_third_element ZD2))) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (o2_NMWQZZ ::=plan_NMWQZZ (Atuple3 (80;(large_to_nat 8220);(large_to_nat 8940))));;
  (P2 ::=att (OId o2_NMWQZZ));;
  (o1_GRDZT ::=plan_GRDZT (Atuple3 (80;(large_to_nat 8340);(large_to_nat 8940))));;
  (P1 ::=att (OId o1_GRDZT));;
  (IF (BEq ((ANum (triple4_return_third_element ZD1))) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (o1_NMWQZZ ::=plan_NMWQZZ (Atuple3 (80;(large_to_nat 8340);(large_to_nat 9060))));;
  (P1 ::=att (OId o1_NMWQZZ));;
  (o2_GD ::=plan_GD (Atuple3 (80;(large_to_nat 8940);(large_to_nat 9660))));;
  (P2 ::=att (OId o2_GD));;
  (d2 add 1);;
  (o2_GDDZ ::=plan_GDDZ (Atuple3 (80;(large_to_nat 8940);(large_to_nat 9420))));;
  (P2 ::=att (OId o2_GDDZ));;
  (IF (BEq (ANum D2) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (gdsb_10 sub 1);;
  (o2_JWJC ::=plan_JWJC (Atuple3 (80;(large_to_nat 8940);(large_to_nat 9540))));;
  (P2 ::=att (OId o2_JWJC));;
  (IF (BEq (ANum D2) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (o2_JY ::=plan_JY (Atuple3 (80;(large_to_nat 8940);(large_to_nat 9660))));;
  (P2 ::=att (OId o2_JY));;
  (IF (BEq (ANum D2) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (jyc_2 sub 1);;
  (P2 ::exe (ANum 1));;
  (P2 ::exe (ANum 1));;
  (J35_12_GRDZT add 1);;
  (P2 ::exe (ANum 1));;
  (J35_12_NMWQZZ add 1);;
  (P2 ::exe (ANum 1));;
  (d2 sub 1);;
  (P2 ::exe (ANum 1));;
  (J35_12_GDDZ add 1);;
  (gdsb_10 add 1);;
  (P2 ::exe (ANum 1));;
  (J35_12_JWJC add 1);;
  (P2 ::exe (ANum 1));;
  (J35_12_JY add 1);;
  (jyc_2 add 1);;
  (free P2);;
  (o1_GD ::=plan_GD (Atuple3 (80;(large_to_nat 9060);(large_to_nat 9780))));;
  (P1 ::=att (OId o1_GD));;
  (d1 add 1);;
  (o1_GDDZ ::=plan_GDDZ (Atuple3 (80;(large_to_nat 9060);(large_to_nat 9540))));;
  (P1 ::=att (OId o1_GDDZ));;
  (IF (BEq (ANum D1) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (gdsb_6 sub 1);;
  (o1_JWJC ::=plan_JWJC (Atuple3 (80;(large_to_nat 9060);(large_to_nat 9660))));;
  (P1 ::=att (OId o1_JWJC));;
  (IF (BEq (ANum D1) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (o1_JY ::=plan_JY (Atuple3 (80;(large_to_nat 9060);(large_to_nat 9780))));;
  (P1 ::=att (OId o1_JY));;
  (IF (BEq (ANum D1) (ANum 1)) THEN SKIP ELSE CAbt FI);;
  (jyc_1 sub 1);;
  (P1 ::exe (ANum 1));;
  (P1 ::exe (ANum 1));;
  (J35_11_GRDZT add 1);;
  (P1 ::exe (ANum 1));;
  (J35_11_NMWQZZ add 1);;
  (P1 ::exe (ANum 1));;
  (d1 sub 1);;
  (P1 ::exe (ANum 1));;
  (J35_11_GDDZ add 1);;
  (gdsb_6 add 1);;
  (P1 ::exe (ANum 1));;
  (J35_11_JWJC add 1);;
  (P1 ::exe (ANum 1));;
  (J35_11_JY add 1);;
  (jyc_1 add 1);;
  (free P1);;
  (SKIP).

Fact Example_9_Correct :

forall (oloc_1 oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 oloc_8 oloc_9 oloc_10  :nat)
       (rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
        rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 rloc_25 
        rloc_26 rloc_27 rloc_28 rloc_29 rloc_30 rloc_31 rloc_32 rloc_33 rloc_34 rloc_35 rloc_36 :nat),

neq0_10 oloc_1 oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 oloc_8 oloc_9 oloc_10 ->
neq0_36 rloc_1  rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
        rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 rloc_25 
        rloc_26 rloc_27 rloc_28 rloc_29 rloc_30 rloc_31 rloc_32 rloc_33 rloc_34 rloc_35 rloc_36 ->

neq_10 oloc_1 oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 oloc_8 oloc_9 oloc_10 ->
neq_36 rloc_1 rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
       rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 rloc_25 
       rloc_26 rloc_27 rloc_28 rloc_29 rloc_30 rloc_31 rloc_32 rloc_33 rloc_34 rloc_35 rloc_36 -> 

(emp_sO, d1 !sv-> 0; d2 !sv-> 0; gdsb_6 !sv-> 1; gdsb_10 !sv-> 1; jyc_1 !sv-> 1; jyc_2 !sv-> 1; emp_sV, 
 emp_sS, rloc_33 !hr-> 1; rloc_34 !hr-> 1; rloc_35 !hr-> 1; rloc_36 !hr-> 1;  emp_heapR, 
 emp_heapO) =[
   Example_9
]=> St (o1_JY !so-> 0;o1_JWJC !so-> 0;o1_GDDZ !so-> 0;o1_GD !so-> 0;o1_NMWQZZ !so-> 0;o1_GRDZT !so-> 0;o1_ZD !so-> 0;
        o2_JY !so-> 0;o2_JWJC !so-> 0;o2_GDDZ !so-> 0;o2_GD !so-> 0; o2_NMWQZZ !so-> 0; o2_GRDZT !so-> 0; o2_ZD !so-> 0; emp_sO,
        jyc_1 !sv-> 1;J35_11_JY !sv-> 1;J35_11_JWJC !sv-> 1;gdsb_6 !sv-> 1;J35_11_GDDZ !sv-> 1;d1 !sv-> 0;
        J35_11_NMWQZZ !sv-> 1;J35_11_GRDZT !sv-> 1;jyc_2 !sv-> 1;J35_12_JY !sv-> 1;J35_12_JWJC !sv-> 1;gdsb_10 !sv-> 1;
        J35_12_GDDZ !sv-> 1; d2 !sv-> 0; J35_12_NMWQZZ !sv-> 1; J35_12_GRDZT !sv-> 1; emp_sV,P1 !ss-> on; P2 !ss-> on; emp_sS,
        rloc_35 !hr-> 1; rloc_33 !hr-> 1; rloc_36 !hr-> 1; rloc_34 !hr-> 1; emp_heapR, emp_heapO).

Proof.
  unfold neq0_10, neq0_36, neq_10, neq_36.
  intros oloc_1 oloc_2 oloc_3 oloc_4 oloc_5 oloc_6 oloc_7 oloc_8 oloc_9 oloc_10.
  intros rloc_1 rloc_2 rloc_3 rloc_4 rloc_5 rloc_6 rloc_7 rloc_8 rloc_9 rloc_10 rloc_11 rloc_12 rloc_13 
         rloc_14 rloc_15 rloc_16 rloc_17 rloc_18 rloc_19 rloc_20 rloc_21 rloc_22 rloc_23 rloc_24 rloc_25 
         rloc_26 rloc_27 rloc_28 rloc_29 rloc_30 rloc_31 rloc_32 rloc_33 rloc_34 rloc_35 rloc_36.
  intros H_neq0_oloc H_neq0_rloc H_neq_oloc H_neq_rloc.
  destruct H_neq0_oloc as (H1_o & H2_o & H3_o & H4_o & H5_o & H6_o & H7_o & H8_o & H9_o & H10_o).
  destruct H_neq0_rloc as (H1_r & H2_r & H3_r & H4_r & H5_r & H6_r & H7_r & H8_r & H9_r & H10_r & H11_r & H12_r & H13_r & 
                           H14_r & H15_r & H16_r & H17_r & H18_r & H19_r & H20_r & H21_r & H22_r & H23_r & H24_r & H25_r & 
                           H26_r & H27_r & H28_r & H29_r & H30_r & H31_r & H32_r & H33_r & H34_r & H35_r & H36_r).
  destruct H_neq_oloc as (
  Ho1_2 & Ho1_3 & Ho1_4 & Ho1_5 & Ho1_6 & Ho1_7 & Ho1_8 & Ho1_9 & Ho1_10 & 
  Ho2_3 & Ho2_4 & Ho2_5 & Ho2_6 & Ho2_7 & Ho2_8 & Ho2_9 & Ho2_10 & 
  Ho3_4 & Ho3_5 & Ho3_6 & Ho3_7 & Ho3_8 & Ho3_9 & Ho3_10 &
  Ho4_5 & Ho4_6 & Ho4_7 & Ho4_8 & Ho4_9 & Ho4_10 & 
  Ho5_6 & Ho5_7 & Ho5_8 & Ho5_9 & Ho5_10 &
  Ho6_7 & Ho6_8 & Ho6_9 & Ho6_10 & 
  Ho7_8 & Ho7_9 & Ho7_10 & 
  Ho8_9 & Ho8_10 &
  Ho9_10
  ).
  destruct H_neq_rloc as (
  Hr1_2 & Hr1_3 & Hr1_4 & Hr1_5 & Hr1_6 & Hr1_7 & Hr1_8 & Hr1_9 & Hr1_10 & Hr1_11 & Hr1_12 & Hr1_13 & Hr1_14 & Hr1_15 & Hr1_16 & Hr1_17 & Hr1_18 & Hr1_19 & Hr1_20 & Hr1_21 & Hr1_22 & Hr1_23 & Hr1_24 & Hr1_25 & Hr1_26 & Hr1_27 & Hr1_28 & Hr1_29 & Hr1_30 & Hr1_31 & Hr1_32 & Hr1_33 & Hr1_34 & Hr1_35 & Hr1_36 &
  Hr2_3 & Hr2_4 & Hr2_5 & Hr2_6 & Hr2_7 & Hr2_8 & Hr2_9 & Hr2_10 & Hr2_11 & Hr2_12 & Hr2_13 & Hr2_14 & Hr2_15 & Hr2_16 & Hr2_17 & Hr2_18 & Hr2_19 & Hr2_20 & Hr2_21 & Hr2_22 & Hr2_23 & Hr2_24 & Hr2_25 & Hr2_26 & Hr2_27 & Hr2_28 & Hr2_29 & Hr2_30 & Hr2_31 & Hr2_32 & Hr2_33 & Hr2_34 & Hr2_35 & Hr2_36 &
  Hr3_4 & Hr3_5 & Hr3_6 & Hr3_7 & Hr3_8 & Hr3_9 & Hr3_10 & Hr3_11 & Hr3_12 & Hr3_13 & Hr3_14 & Hr3_15 & Hr3_16 & Hr3_17 & Hr3_18 & Hr3_19 & Hr3_20 & Hr3_21 & Hr3_22 & Hr3_23 & Hr3_24 & Hr3_25 & Hr3_26 & Hr3_27 & Hr3_28 & Hr3_29 & Hr3_30 & Hr3_31 & Hr3_32 & Hr3_33 & Hr3_34 & Hr3_35 & Hr3_36 & 
  Hr4_5 & Hr4_6 & Hr4_7 & Hr4_8 & Hr4_9 & Hr4_10 & Hr4_11 & Hr4_12 & Hr4_13 & Hr4_14 & Hr4_15 & Hr4_16 & Hr4_17 & Hr4_18 & Hr4_19 & Hr4_20 & Hr4_21 & Hr4_22 & Hr4_23 & Hr4_24 & Hr4_25 & Hr4_26 & Hr4_27 & Hr4_28 & Hr4_29 & Hr4_30 & Hr4_31 & Hr4_32 & Hr4_33 & Hr4_34 & Hr4_35 & Hr4_36 & 
  Hr5_6 & Hr5_7 & Hr5_8 & Hr5_9 & Hr5_10 & Hr5_11 & Hr5_12 & Hr5_13 & Hr5_14 & Hr5_15 & Hr5_16 & Hr5_17 & Hr5_18 & Hr5_19 & Hr5_20 & Hr5_21 & Hr5_22 & Hr5_23 & Hr5_24 & Hr5_25 & Hr5_26 & Hr5_27 & Hr5_28 & Hr5_29 & Hr5_30 & Hr5_31 & Hr5_32 & Hr5_33 & Hr5_34 & Hr5_35 & Hr5_36 &
  Hr6_7 & Hr6_8 & Hr6_9 & Hr6_10 & Hr6_11 & Hr6_12 & Hr6_13 & Hr6_14 & Hr6_15 & Hr6_16 & Hr6_17 & Hr6_18 & Hr6_19 & Hr6_20 & Hr6_21 & Hr6_22 & Hr6_23 & Hr6_24 & Hr6_25 & Hr6_26 & Hr6_27 & Hr6_28 & Hr6_29 & Hr6_30 & Hr6_31 & Hr6_32 & Hr6_33 & Hr6_34 & Hr6_35 & Hr6_36 &
  Hr7_8 & Hr7_9 & Hr7_10 & Hr7_11 & Hr7_12 & Hr7_13 & Hr7_14 & Hr7_15 & Hr7_16 & Hr7_17 & Hr7_18 & Hr7_19 & Hr7_20 & Hr7_21 & Hr7_22 & Hr7_23 & Hr7_24 & Hr7_25 & Hr7_26 & Hr7_27 & Hr7_28 & Hr7_29 & Hr7_30 & Hr7_31 & Hr7_32 & Hr7_33 & Hr7_34 & Hr7_35 & Hr7_36 & 
  Hr8_9 & Hr8_10 & Hr8_11 & Hr8_12 & Hr8_13 & Hr8_14 & Hr8_15 & Hr8_16 & Hr8_17 & Hr8_18 & Hr8_19 & Hr8_20 & Hr8_21 & Hr8_22 & Hr8_23 & Hr8_24 & Hr8_25 & Hr8_26 & Hr8_27 & Hr8_28 & Hr8_29 & Hr8_30 & Hr8_31 & Hr8_32 & Hr8_33 & Hr8_34 & Hr8_35 & Hr8_36 &
  Hr9_10 & Hr9_11 & Hr9_12 & Hr9_13 & Hr9_14 & Hr9_15 & Hr9_16 & Hr9_17 & Hr9_18 & Hr9_19 & Hr9_20 & Hr9_21 & Hr9_22 & Hr9_23 & Hr9_24 & Hr9_25 & Hr9_26 & Hr9_27 & Hr9_28 & Hr9_29 & Hr9_30 & Hr9_31 & Hr9_32 & Hr9_33 & Hr9_34 & Hr9_35 & Hr9_36 & 
  Hr10_11 & Hr10_12 & Hr10_13 & Hr10_14 & Hr10_15 & Hr10_16 & Hr10_17 & Hr10_18 & Hr10_19 & Hr10_20 & Hr10_21 & Hr10_22 & Hr10_23 & Hr10_24 & Hr10_25 & Hr10_26 & Hr10_27 & Hr10_28 & Hr10_29 & Hr10_30 & Hr10_31 & Hr10_32 & Hr10_33 & Hr10_34 & Hr10_35 & Hr10_36 & 
  Hr11_12 & Hr11_13 & Hr11_14 & Hr11_15 & Hr11_16 & Hr11_17 & Hr11_18 & Hr11_19 & Hr11_20 & Hr11_21 & Hr11_22 & Hr11_23 & Hr11_24 & Hr11_25 & Hr11_26 & Hr11_27 & Hr11_28 & Hr11_29 & Hr11_30 & Hr11_31 & Hr11_32 & Hr11_33 & Hr11_34 & Hr11_35 & Hr11_36 & 
  Hr12_13 & Hr12_14 & Hr12_15 & Hr12_16 & Hr12_17 & Hr12_18 & Hr12_19 & Hr12_20 & Hr12_21 & Hr12_22 & Hr12_23 & Hr12_24 & Hr12_25 & Hr12_26 & Hr12_27 & Hr12_28 & Hr12_29 & Hr12_30 & Hr12_31 & Hr12_32 & Hr12_33 & Hr12_34 & Hr12_35 & Hr12_36 & 
  Hr13_14 & Hr13_15 & Hr13_16 & Hr13_17 & Hr13_18 & Hr13_19 & Hr13_20 & Hr13_21 & Hr13_22 & Hr13_23 & Hr13_24 & Hr13_25 & Hr13_26 & Hr13_27 & Hr13_28 & Hr13_29 & Hr13_30 & Hr13_31 & Hr13_32 & Hr13_33 & Hr13_34 & Hr13_35 & Hr13_36 & 
  Hr14_15 & Hr14_16 & Hr14_17 & Hr14_18 & Hr14_19 & Hr14_20 & Hr14_21 & Hr14_22 & Hr14_23 & Hr14_24 & Hr14_25 & Hr14_26 & Hr14_27 & Hr14_28 & Hr14_29 & Hr14_30 & Hr14_31 & Hr14_32 & Hr14_33 & Hr14_34 & Hr14_35 & Hr14_36 & 
  Hr15_16 & Hr15_17 & Hr15_18 & Hr15_19 & Hr15_20 & Hr15_21 & Hr15_22 & Hr15_23 & Hr15_24 & Hr15_25 & Hr15_26 & Hr15_27 & Hr15_28 & Hr15_29 & Hr15_30 & Hr15_31 & Hr15_32 & Hr15_33 & Hr15_34 & Hr15_35 & Hr15_36 & 
  Hr16_17 & Hr16_18 & Hr16_19 & Hr16_20 & Hr16_21 & Hr16_22 & Hr16_23 & Hr16_24 & Hr16_25 & Hr16_26 & Hr16_27 & Hr16_28 & Hr16_29 & Hr16_30 & Hr16_31 & Hr16_32 & Hr16_33 & Hr16_34 & Hr16_35 & Hr16_36 &
  Hr17_18 & Hr17_19 & Hr17_20 & Hr17_21 & Hr17_22 & Hr17_23 & Hr17_24 & Hr17_25 & Hr17_26 & Hr17_27 & Hr17_28 & Hr17_29 & Hr17_30 & Hr17_31 & Hr17_32 & Hr17_33 & Hr17_34 & Hr17_35 & Hr17_36 &
  Hr18_19 & Hr18_20 & Hr18_21 & Hr18_22 & Hr18_23 & Hr18_24 & Hr18_25 & Hr18_26 & Hr18_27 & Hr18_28 & Hr18_29 & Hr18_30 & Hr18_31 & Hr18_32 & Hr18_33 & Hr18_34 & Hr18_35 & Hr18_36 & 
  Hr19_20 & Hr19_21 & Hr19_22 & Hr19_23 & Hr19_24 & Hr19_25 & Hr19_26 & Hr19_27 & Hr19_28 & Hr19_29 & Hr19_30 & Hr19_31 & Hr19_32 & Hr19_33 & Hr19_34 & Hr19_35 & Hr19_36 & 
  Hr20_21 & Hr20_22 & Hr20_23 & Hr20_24 & Hr20_25 & Hr20_26 & Hr20_27 & Hr20_28 & Hr20_29 & Hr20_30 & Hr20_31 & Hr20_32 & Hr20_33 & Hr20_34 & Hr20_35 & Hr20_36 & 
  Hr21_22 & Hr21_23 & Hr21_24 & Hr21_25 & Hr21_26 & Hr21_27 & Hr21_28 & Hr21_29 & Hr21_30 & Hr21_31 & Hr21_32 & Hr21_33 & Hr21_34 & Hr21_35 & Hr21_36 & 
  Hr22_23 & Hr22_24 & Hr22_25 & Hr22_26 & Hr22_27 & Hr22_28 & Hr22_29 & Hr22_30 & Hr22_31 & Hr22_32 & Hr22_33 & Hr22_34 & Hr22_35 & Hr22_36 & 
  Hr23_24 & Hr23_25 & Hr23_26 & Hr23_27 & Hr23_28 & Hr23_29 & Hr23_30 & Hr23_31 & Hr23_32 & Hr23_33 & Hr23_34 & Hr23_35 & Hr23_36 & 
  Hr24_25 & Hr24_26 & Hr24_27 & Hr24_28 & Hr24_29 & Hr24_30 & Hr24_31 & Hr24_32 & Hr24_33 & Hr24_34 & Hr24_35 & Hr24_36 & 
  Hr25_26 & Hr25_27 & Hr25_28 & Hr25_29 & Hr25_30 & Hr25_31 & Hr25_32 & Hr25_33 & Hr25_34 & Hr25_35 & Hr25_36 &
  Hr26_27 & Hr26_28 & Hr26_29 & Hr26_30 & Hr26_31 & Hr26_32 & Hr26_33 & Hr26_34 & Hr26_35 & Hr26_36 & 
  Hr27_28 & Hr27_29 & Hr27_30 & Hr27_31 & Hr27_32 & Hr27_33 & Hr27_34 & Hr27_35 & Hr27_36 & 
  Hr28_29 & Hr28_30 & Hr28_31 & Hr28_32 & Hr28_33 & Hr28_34 & Hr28_35 & Hr28_36 &
  Hr29_30 & Hr29_31 & Hr29_32 & Hr29_33 & Hr29_34 & Hr29_35 & Hr29_36 &
  Hr30_31 & Hr30_32 & Hr30_33 & Hr30_34 & Hr30_35 & Hr30_36 & 
  Hr31_32 & Hr31_33 & Hr31_34 & Hr31_35 & Hr31_36 &
  Hr32_33 & Hr32_34 & Hr32_35 & Hr32_36 &
  Hr33_34 & Hr33_35 & Hr33_36 &
  Hr34_35 & Hr34_36 &
  Hr35_36
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
   eapply E_Sasgn  with (loc := oloc_1).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_Oplan_Tuple4 with (loc := oloc_2) (loc1 := rloc_5) (loc2 := rloc_6) (loc3 := rloc_7)(loc4 := rloc_8).
   reflexivity. reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.

   eapply E_Seq.
   eapply E_Sasgn  with (loc := oloc_2).
   simpl. reflexivity.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_3) (loc1 := rloc_9) (loc2 := rloc_10) (loc3 := rloc_11).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo1in3; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_4) (loc1 := rloc_12) (loc2 := rloc_13) (loc3 := rloc_14).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_4).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo2in4; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_5) (loc1 := rloc_15) (loc2 := rloc_16) (loc3 := rloc_17).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_5).
   simpl; reflexivity. 
   rewrite sS_update_neq.
   rewrite sS_update_eq; reflexivity.
   discriminate.
   intros. 
   apply SafeinHo1_5; auto.
   rewrite sS_update_shadow_3.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_6) (loc1 := rloc_18) (loc2 := rloc_19) (loc3 := rloc_20).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_6).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo2in6; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_7) (loc1 := rloc_21) (loc2 := rloc_22) (loc3 := rloc_23).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_7).
   simpl; reflexivity. 
   rewrite sS_update_neq.
   rewrite sS_update_eq; reflexivity.
   discriminate.
   intros. 
   apply SafeinHo3_6; auto.
   rewrite sS_update_shadow_3.
   simpl.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   rewrite sV_update_shadow_3.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_8) (loc1 := rloc_24) (loc2 := rloc_25) (loc3 := rloc_26).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_8).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo4in8; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Rsub with (loc := rloc_34). 
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_eq.
   reflexivity.
   simpl; discriminate. 
   simpl; discriminate.
   simpl; discriminate.
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
   rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. 
   rewrite hR_update_eq.
   reflexivity.
   simpl; rewrite sV_update_shadow_5.
   rewrite hR_update_shadow_29.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_9) (loc1 := rloc_27) (loc2 := rloc_28) (loc3 := rloc_29).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_9).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo5in9; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_10) (loc1 := rloc_30) (loc2 := rloc_31) (loc3 := rloc_32).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_10).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo6in10; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Rsub with (loc := rloc_36). 
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_eq.
   reflexivity.
   simpl; discriminate. 
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
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
   rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. 
   rewrite hR_update_eq.
   reflexivity.
   simpl; rewrite sV_update_shadow_7.
   rewrite hR_update_shadow_37.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_2)(e :=o2_ZD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate.
   discriminate. discriminate. 
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr4_30; auto.
   simpl. 
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_neq; auto.   
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
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
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
   rewrite sS_update_shadow.  rewrite sO_update_shadow_10.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_3)(e :=o2_GRDZT).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate.
   discriminate. discriminate. 
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_26; auto.
   simpl. 
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_neq; auto.
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
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_10.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_4)(e :=o2_NMWQZZ).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate.
   discriminate. discriminate. 
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_23; auto.
   simpl. 
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_neq; auto.
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
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_10.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_7)(e :=o2_GD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_14; auto.
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
   rewrite hR_remove_neq; auto.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_8.

   eapply E_Seq.
   eapply E_Rsub_V. auto.
   simpl.
   rewrite sV_update_shadow_6.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_8)(e :=o2_GDDZ).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_11; auto.
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
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_8.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Radd with (loc := rloc_34). 
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_eq.
   reflexivity.
   simpl; discriminate. 
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto.
   rewrite hR_update_eq.
   reflexivity.
   simpl; rewrite sV_update_shadow_7.
   rewrite hR_update_shadow_9.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_9)(e :=o2_JWJC).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_8; auto.
   simpl. 
   rewrite hO_remove_neq; auto.  
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_8.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_10)(e :=o2_JY).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_5; auto.
   simpl.  
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_8.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Radd with (loc := rloc_36). 
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_eq.
   reflexivity.
   simpl; discriminate. 
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hR_update_neq; auto. 
   rewrite hR_update_eq.
   reflexivity.
   simpl; rewrite sV_update_shadow_9.
   rewrite hR_update_shadow_3.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_2) (loc1 := rloc_5) (loc2 := rloc_6) (loc3 := rloc_7).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_2).
   simpl; reflexivity. 
   rewrite sS_update_neq.
   rewrite sS_update_eq; reflexivity.
   discriminate.
   intros. 
   apply SafeinHo3_4; auto.
   rewrite sS_update_shadow_3.
   simpl.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   rewrite sV_update_shadow_10.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_3) (loc1 := rloc_8) (loc2 := rloc_9) (loc3 := rloc_10).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_3).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo4_5; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Rsub with (loc := rloc_33). 
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_eq.
   reflexivity.
   simpl; discriminate. 
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_eq.
   reflexivity.
   simpl; rewrite sV_update_shadow_11.
   rewrite hR_update_shadow_20.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_4) (loc1 := rloc_11) (loc2 := rloc_12) (loc3 := rloc_13).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_4).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo5_6; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Oplan_Tuple3 with (loc := oloc_7) (loc1 := rloc_21) (loc2 := rloc_22) (loc3 := rloc_23).
   reflexivity. reflexivity. reflexivity.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hR_update_neq; auto.
   repeat rewrite hO_update_neq; auto.
   simpl.

   eapply E_Seq.
   eapply E_Satt  with (loc := oloc_7).
   simpl; reflexivity. 
   rewrite sS_update_eq; reflexivity.
   intros. 
   apply SafeinHo6_7; auto.
   rewrite sS_update_shadow.
   simpl.

   eapply E_Seq.
   eapply E_IfTure. 
   simpl.
   reflexivity.
   eapply E_Skip.

   eapply E_Seq.
   eapply E_Rsub with (loc := rloc_35). 
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_eq.
   reflexivity.
   simpl; discriminate. 
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. 
   rewrite hR_update_eq.
   reflexivity.
   simpl; rewrite sV_update_shadow_12.
   rewrite hR_update_shadow_27.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_1)(e :=o1_ZD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate. discriminate.
   discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr4_26; auto.
   simpl. 
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_neq; auto.   
   rewrite hO_remove_neq; auto.
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
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
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
   rewrite sS_update_shadow.  rewrite sO_update_shadow_15.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_5)(e :=o1_GRDZT).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate. discriminate.
   discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_22; auto.
   simpl. 
   rewrite hO_remove_neq; auto.
   rewrite hO_remove_neq; auto.   
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
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_15.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_6)(e :=o1_NMWQZZ).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_neq. 
   rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate. discriminate.
   discriminate. discriminate. discriminate. discriminate.
   discriminate.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_19; auto.
   simpl. 
   rewrite hO_remove_neq; auto.
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
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_15.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_2)(e :=o1_GD).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate. 
   discriminate. discriminate. discriminate. 
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_14; auto.
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
   rewrite hR_remove_neq; auto.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_8.

   eapply E_Seq.
   eapply E_Rsub_V. auto.
   simpl.
   rewrite sV_update_shadow_6.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_3)(e :=o1_GDDZ).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate. 
   discriminate. discriminate. discriminate. 
   rewrite hO_update_neq; auto.
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_11; auto.
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
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_8.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Radd with (loc := rloc_33). 
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_eq.
   reflexivity.
   simpl; discriminate. 
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. rewrite hR_update_neq; auto. 
   rewrite hR_update_neq; auto. 
   rewrite hR_update_eq.
   reflexivity.
   simpl; rewrite sV_update_shadow_7.
   rewrite hR_update_shadow_9.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_4)(e :=o1_JWJC).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate. 
   discriminate. discriminate. discriminate. 
   rewrite hO_update_neq; auto.
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_8; auto.
   simpl.  
   rewrite hO_remove_neq; auto.    
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. 
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_8.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Sexe with (loc := oloc_7)(e :=o1_JY).
   rewrite sS_update_eq. reflexivity.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_neq. rewrite sO_update_neq.
   rewrite sO_update_eq; auto.
   discriminate. discriminate. discriminate. 
   discriminate. discriminate. discriminate. 
   rewrite hO_update_eq; reflexivity.
   intros. 
   apply SafeinHr3_5; auto.
   simpl.    
   rewrite hO_remove_work.
   unfold hR_removes.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_neq; auto. rewrite hR_remove_neq; auto.
   rewrite hR_remove_work. rewrite hR_remove_work. rewrite hR_remove_work. 
   rewrite sS_update_shadow.  rewrite sO_update_shadow_8.

   eapply E_Seq.
   eapply E_Radd_V. auto.
   rewrite sV_add.
   simpl.

   eapply E_Seq.
   eapply E_Radd with (loc := rloc_35). 
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_neq.
   rewrite sV_update_eq.
   reflexivity.
   simpl; discriminate. 
   simpl; discriminate.
   simpl; discriminate. 
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   simpl; discriminate.
   rewrite hR_update_neq; auto. 
   rewrite hR_update_eq.
   reflexivity.
   simpl; rewrite sV_update_shadow_9.
   rewrite hR_update_shadow_3.

   eapply E_Seq.
   eapply E_Sfree.
   rewrite sS_update_eq; reflexivity.
   rewrite sS_update_shadow.

   eapply E_Skip.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto.
   unfold not_in_domO. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. auto. auto. auto. auto.
   unfold not_in_domR. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto.
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
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domO. 
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   rewrite hO_update_neq.
   auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domO. 
   rewrite hO_update_neq.
   auto. auto. 
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domO. 
   rewrite hO_update_neq.
   auto. auto. 
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq.
   auto. auto. auto. auto. auto. auto. auto. auto.
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domR. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. rewrite hR_update_neq. 
   rewrite hR_update_neq. 
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. 
   unfold not_in_domO. 
   rewrite hO_update_neq.
   auto. auto. 
   Unshelve.
   auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto. auto.
Qed.



