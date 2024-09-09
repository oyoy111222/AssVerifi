Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Export util.
Require Export language.
Require Export semantic.
Require Export state.
Require Export function.
Require Export Logic.

(*Some variables*)

(* 歼35_3 *)
Definition i  : id := Id "i".
Definition J35_3_ZD : id := Id "J35_3_ZD". (* 折叠 *)
Definition J35_3_GD : id := Id "J35_3_GD". (* 供电 *)
Definition J35_3_JY : id := Id "J35_3_JY". (* 加油 *)
Definition J35_3_GRDZT : id := Id "J35_3_GRDZT". (* 干扰弹装填 *)
Definition J35_3_NMWQZZ : id := Id "J35_3_NMWQZZ". (* 内埋武器装载 *)
Definition J35_3_GDDZ : id := Id "J35_3_GDDZ". (* 惯导对准 *)
Definition J35_3_JWJC : id := Id "J35_3_RWJZ". (* 机务检查 *)

(* 歼35_4 *)
Definition J35_4_ZD : id := Id "J35_4_ZD". (* 折叠 *)
Definition J35_4_GD : id := Id "J35_4_GD". (* 供电 *)
Definition J35_4_JY : id := Id "J35_4_JY". (* 加油 *)
Definition J35_4_GRDZT : id := Id "J35_4_GRDZT". (* 干扰弹装填 *)
Definition J35_4_NMWQZZ : id := Id "J35_4_NMWQZZ". (* 内埋武器装载 *)
Definition J35_4_GDDZ : id := Id "J15_4_GDDZ". (* 惯导对准 *)
Definition J35_4_JWJC : id := Id "J15_4_RWJZ". (* 机务检查 *)

(* 全局变量 *)
Definition d1 : id := Id "d1".
Definition d2 : id := Id "d2".
Definition jyc_6 : id := Id "jyz_6".
Definition jyc_12 : id := Id "jyz_12".
Definition gdsb_4 : id := Id "gdsb_4".
Definition gdsb_5 : id := Id "gdsb_5".


(* 作业变量 *)

(* 具体作业 *)
Definition o1_JY : id := Id "o1_JY".
Definition o1_GRDZT : id := Id "o1_GRDZT".
Definition o1_NMWQZZ : id := Id "o1_NMWQZZ".
Definition o1_GDDZ : id := Id "o1_GDDZ".
Definition o1_JWJC : id := Id "o1_JWJC".

Definition o2_JY : id := Id "o2_JY".
Definition o2_GRDZT : id := Id "o2_GRDZT".
Definition o2_NMWQZZ : id := Id "o2_NMWQZZ".
Definition o2_GDDZ : id := Id "o2_GDDZ".
Definition o2_JWJC : id := Id "o2_JWJC".

(* 抽象作业 *)
Definition o1_ZD : id := Id "o1_ZD".
Definition o1_GD : id := Id "o1_GD".

Definition o2_ZD : id := Id "o2_ZD".
Definition o2_GD : id := Id "o2_GD".


(* 阵位变量 *)
Definition P7 : id := Id "P7".
Definition P12 : id := Id "P12".

(* 用于比较和判断的具体数值 *)
Definition ZD1 : tuple4 := Triple4 195 6 0 1.
Definition GD1 : tuple3 := Triple3 80 (large_to_nat 8542) (large_to_nat 9262).
Definition JY1 : tuple3 := Triple3 80 (large_to_nat 8542) (large_to_nat 9262).  
Definition JWJC1 : tuple3 := Triple3 80 (large_to_nat 8542) (large_to_nat 9142).     
Definition GDDZ1 : tuple3 := Triple3 80 (large_to_nat 8542) (large_to_nat 9022). 
Definition GRDZT1 : tuple3 := Triple3 80 (large_to_nat 7822) (large_to_nat 8422). 
Definition NMWQZZ1 : tuple3 := Triple3 80 (large_to_nat 7822) (large_to_nat 8542).

Definition ZD2 : tuple4 := Triple4 262 26 1 1.
Definition GD2 : tuple3 := Triple3 80 (large_to_nat 8662) (large_to_nat 9382).
Definition JY2 : tuple3 := Triple3 80 (large_to_nat 8662) (large_to_nat 9382).  
Definition JWJC2 : tuple3 := Triple3 80 (large_to_nat 8662) (large_to_nat 9262).     
Definition GDDZ2 : tuple3 := Triple3 80 (large_to_nat 8662) (large_to_nat 9142). 
Definition GRDZT2 : tuple3 := Triple3 80 (large_to_nat 7942) (large_to_nat 8542). 
Definition NMWQZZ2 : tuple3 := Triple3 80 (large_to_nat 7942) (large_to_nat 8662). 

Definition D1  : nat := 1. (* 歼35_3 供电 *)
Definition D2  : nat := 1. (* 歼35_4 供电 *)
Definition R_JYC_6  : nat := 1. (* 6号加油车 *)
Definition R_JYC_12  : nat := 1. (* 12号加油车 *)
Definition R_GDSB_4  : nat := 1. (* 4号惯导设备 *)
Definition R_GDSB_5  : nat := 1. (* 5号惯导设备 *)

(*The definition of empty state*)
Definition emp_sO : storeO :=
  fun (n : id) => 0.

Definition emp_sV : storeV :=
  fun (n : id) => 0.

Definition emp_sS : storeS :=
  fun (n : id) => [].

Definition empty_st : state := 
  (emp_sO, emp_sV, emp_sS, emp_heapR, emp_heapO).

