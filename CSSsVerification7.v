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

(* 歼35_13 *)
Definition i  : id := Id "i".
Definition J35_13_ZD : id := Id "J35_13_ZD". (* 折叠 *)
Definition J35_13_GD : id := Id "J35_13_GD". (* 供电 *)
Definition J35_13_JY : id := Id "J35_13_JY". (* 加油 *)
Definition J35_13_NC : id := Id "J35_13_NC". (* 暖车 *)
Definition J35_13_GRDZT : id := Id "J35_13_GRDZT". (* 干扰弹装填 *)
Definition J35_13_NMWQZZ : id := Id "J35_13_NMWQZZ". (* 内埋武器装载 *)
Definition J35_13_GDDZ : id := Id "J35_13_GDDZ". (* 惯导对准 *)
Definition J35_13_JWJC : id := Id "J35_13_RWJZ". (* 机务检查 *)

(* 全局变量 *)
Definition d1 : id := Id "d1".
Definition jyc_11 : id := Id "jyz_11".
Definition gdsb_4 : id := Id "gdsb_4".


(* 作业变量 *)

(* 具体作业 *)
Definition o1_JY : id := Id "o1_JY".
Definition o1_NC : id := Id "o1_NC".
Definition o1_GRDZT : id := Id "o1_GRDZT".
Definition o1_NMWQZZ : id := Id "o1_NMWQZZ".
Definition o1_GDDZ : id := Id "o1_GDDZ".
Definition o1_JWJC : id := Id "o1_JWJC".

(* 抽象作业 *)
Definition o1_ZD : id := Id "o1_ZD".
Definition o1_GD : id := Id "o1_GD".

(* 阵位变量 *)
Definition P12  : id := Id "P12".

(* 用于比较和判断的具体数值 *)
(* 开始时间和结束时间都是_ _ _ _ 0,而直接使用 _ _ _ _ 0作为 nat 类型的值，Coq 会将其解释为一个非常大的递归结构，
导致验证性能下降或者耗尽系统资源，而不是简单地表示一个整数，故统一采用保留高位，去除低位0的方法，即不影响方案验证的正确性，也提高了验证效率 *)
Definition ZD1 : tuple4 := Triple4 195 6 0 1.
Definition GD1 : tuple3 := Triple3 80 (large_to_nat 1680) (large_to_nat 1752).
Definition JY1 : tuple3 := Triple3 80 (large_to_nat 1680) (large_to_nat 1752).  
Definition JWJC1 : tuple3 := Triple3 80 (large_to_nat 1680) (large_to_nat 1740).     
Definition GDDZ1 : tuple3 := Triple3 80 (large_to_nat 1680) (large_to_nat 1728). 
Definition GRDZT1 : tuple3 := Triple3 80 (large_to_nat 1608) (large_to_nat 1668). 
Definition NMWQZZ1 : tuple3 := Triple3 80 (large_to_nat 1608) (large_to_nat 1680).

Definition D1  : nat := 1. (* 歼35_13 供电 *)
Definition R_JYC_11  : nat := 1. (* 11号加油车 *)
Definition R_GDSB_4 : nat := 1. (* 4号惯导设备 *)

(*The definition of empty state*)
Definition emp_sO : storeO :=
  fun (n : id) => 0.

Definition emp_sV : storeV :=
  fun (n : id) => 0.

Definition emp_sS : storeS :=
  fun (n : id) => [].

Definition empty_st : state := 
  (emp_sO, emp_sV, emp_sS, emp_heapR, emp_heapO).

