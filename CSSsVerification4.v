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

(* 歼35_5 *)
Definition i  : id := Id "i".
Definition J35_5_ZD : id := Id "J35_5_ZD". (* 折叠 *)
Definition J35_5_GD : id := Id "J35_5_GD". (* 供电 *)
Definition J35_5_JY : id := Id "J35_5_JY". (* 加油 *)
Definition J35_5_GRDZT : id := Id "J35_5_GRDZT". (* 干扰弹装填 *)
Definition J35_5_NMWQZZ : id := Id "J35_5_NMWQZZ". (* 内埋武器装载 *)
Definition J35_5_GDDZ : id := Id "J35_5_GDDZ". (* 惯导对准 *)
Definition J35_5_JWJC : id := Id "J35_5_RWJZ". (* 机务检查 *)

(* 歼35_6 *)
Definition J35_6_ZD : id := Id "J35_6_ZD". (* 折叠 *)
Definition J35_6_GD : id := Id "J35_6_GD". (* 供电 *)
Definition J35_6_GN : id := Id "J35_6_GN". (* 供氮 *)
Definition J35_6_JY : id := Id "J35_6_JY". (* 加油 *)
Definition J35_6_GDDZ : id := Id "J35_4_GDDZ". (* 惯导对准 *)
Definition J35_6_JWJC : id := Id "J35_4_RWJZ". (* 机务检查 *)

(* 全局变量 *)
Definition d1 : id := Id "d1".
Definition d2 : id := Id "d2".
Definition gnc_1 : id := Id "gnc_1".
Definition jyc_2 : id := Id "jyz_2".
Definition jyc_21 : id := Id "jyz_21".
Definition gdsb_2 : id := Id "gdsb_2".
Definition gdsb_6 : id := Id "gdsb_6".


(* 作业变量 *)

(* 具体作业 *)
Definition o1_JY : id := Id "o1_JY".
Definition o1_GRDZT : id := Id "o1_GRDZT".
Definition o1_NMWQZZ : id := Id "o1_NMWQZZ".
Definition o1_GDDZ : id := Id "o1_GDDZ".
Definition o1_JWJC : id := Id "o1_JWJC".

Definition o2_JY : id := Id "o2_JY".
Definition o2_GN : id := Id "o2_GN".
Definition o2_GDDZ : id := Id "o2_GDDZ".
Definition o2_JWJC : id := Id "o2_JWJC".

(* 抽象作业 *)
Definition o1_ZD : id := Id "o1_ZD".
Definition o1_GD : id := Id "o1_GD".

Definition o2_ZD : id := Id "o2_ZD".
Definition o2_GD : id := Id "o2_GD".


(* 阵位变量 *)
Definition P1  : id := Id "P1".
Definition A6  : id := Id "A6".


(* 用于比较和判断的具体数值 *)
Definition ZD1 : tuple4 := Triple4 274 536 1 1.
Definition GD1 : tuple3 := Triple3 80 (large_to_nat 8912) (large_to_nat 9632).
Definition JY1 : tuple3 := Triple3 80 (large_to_nat 8912) (large_to_nat 9632).  
Definition JWJC1 : tuple3 := Triple3 80 (large_to_nat 8912) (large_to_nat 9512).     
Definition GDDZ1 : tuple3 := Triple3 80 (large_to_nat 8912) (large_to_nat 9392). 
Definition GRDZT1 : tuple3 := Triple3 80 (large_to_nat 8192) (large_to_nat 8792). 
Definition NMWQZZ1 : tuple3 := Triple3 80 (large_to_nat 8192) (large_to_nat 8912).

Definition ZD2 : tuple4 := Triple4 30 70 1 1.
Definition GD2 : tuple3 := Triple3 65 (large_to_nat 8220) (large_to_nat 8940).
Definition GN2 : tuple3 := Triple3 65 (large_to_nat 8220) (large_to_nat 8400).
Definition JY2 : tuple3 := Triple3 65 (large_to_nat 8220) (large_to_nat 8940).  
Definition JWJC2 : tuple3 := Triple3 65 (large_to_nat 8220) (large_to_nat 8820).     
Definition GDDZ2 : tuple3 := Triple3 65 (large_to_nat 8220) (large_to_nat 8700). 

Definition D1  : nat := 1. (* 歼35_5 供电 *)
Definition D2  : nat := 1. (* 歼35_6 供电 *)
Definition R_GNC_1   : nat := 1. (* 1号供氮车 *)
Definition R_JYC_2   : nat := 1. (* 2号加油车 *)
Definition R_JYC_21  : nat := 1. (* 21号加油车 *)
Definition R_GDSB_12 : nat := 1. (* 2号惯导设备 *)
Definition R_GDSB_13 : nat := 1. (* 6号惯导设备 *)

(*The definition of empty state*)
Definition emp_sO : storeO :=
  fun (n : id) => 0.

Definition emp_sV : storeV :=
  fun (n : id) => 0.

Definition emp_sS : storeS :=
  fun (n : id) => [].

Definition empty_st : state := 
  (emp_sO, emp_sV, emp_sS, emp_heapR, emp_heapO).

