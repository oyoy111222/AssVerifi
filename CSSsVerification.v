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

(* 歼15_2 *)
Definition i  : id := Id "i".
Definition J15_2_ZD : id := Id "J15_2_ZD". (* 折叠 *)
Definition J15_2_GY : id := Id "J15_2_GY". (* 供氧 *)
Definition J15_2_GN : id := Id "J15_2_GN". (* 供氮 *)
Definition J15_2_GD : id := Id "J15_2_GD". (* 供电 *)
Definition J15_2_JY : id := Id "J15_2_JY". (* 加油 *)
Definition J15_2_TF : id := Id "J15_2_TF". (* 通风 *)
Definition J15_2_QYC : id := Id "J15_2_QYC". (* 牵引车 *)
Definition J15_2_JYGD : id := Id "J15_2_JYGD". (* 机翼挂弹 *)
Definition J15_2_GDDZ : id := Id "J15_2_GDDZ". (* 惯导对准 *)
Definition J15_2_RWJZ : id := Id "J15_2_RWJZ". (* 任务加载 *)

(* 全局变量 *)
Definition d1 : id := Id "d1".
Definition gyc_3 : id := Id "gyc_3".
Definition ktc_1 : id := Id "ktc_1".
Definition jyc_3 : id := Id "jyc_3".
Definition gnc_2 : id := Id "gnc_2".
Definition gdsb_2 : id := Id "gdsb_2".


(* 作业变量 *)

(* 具体作业 *)
Definition o1_GY : id := Id "o1_GY".
Definition o1_GN : id := Id "o1_GN".
Definition o1_JY : id := Id "o1_JY".
Definition o1_TF : id := Id "o1_TF".
Definition o1_QYC : id := Id "o1_QYC".
Definition o1_JYGD : id := Id "o1_JYGD".
Definition o1_GDDZ : id := Id "o1_GDDZ".
Definition o1_RWJZ : id := Id "o1_RWJZ".

(* 抽象作业 *)
Definition o1_ZD : id := Id "o1_ZD".
Definition o1_GD : id := Id "o1_GD".


(* 阵位变量 *)
Definition P4 : id := Id "P4".

(* 用于比较和判断的具体数值 *)
(* 开始时间和结束时间都是2_ _ _ _,而直接使用 2_ _ _ _ 作为 nat 类型的值，Coq 会将其解释为一个非常大的递归结构，
导致验证性能下降或者耗尽系统资源，而不是简单地表示一个整数，故统一采用保留后四位的方法，即不影响方案验证的正确性，也提高了验证效率 *)
Definition ZD : tuple4 := Triple4 315 300 1 1.
Definition GY : tuple3 := Triple3 80 (large_to_nat 4534) (large_to_nat 4534).
Definition GN : tuple3 := Triple3 80 (large_to_nat 5614) (large_to_nat 5794).
Definition GD : tuple3 := Triple3 80 (large_to_nat 4534) (large_to_nat 6034).
Definition JY : tuple3 := Triple3 80 (large_to_nat 5134) (large_to_nat 6034).  
Definition TF : tuple3 := Triple3 80 (large_to_nat 5134) (large_to_nat 5614).    
Definition JYGD : tuple3 := Triple3 80 (large_to_nat 4534) (large_to_nat 5134). 
Definition GDDZ : tuple3 := Triple3 80 (large_to_nat 5134) (large_to_nat 5734). 
Definition RWJZ : tuple3 := Triple3 80 (large_to_nat 5734) (large_to_nat 5814). 

Definition D1  : nat := 1. (* 供电 *)
Definition R_GYC_3  : nat := 1. (* 3号供氧车 *)
Definition R_KTC_1  : nat := 1. (* 1号空调车 *)
Definition R_JYC_3  : nat := 1. (* 3号加油车 *)
Definition R_GNC_2  : nat := 1. (* 2号供氮车 *)
Definition R_GDSB_2  : nat := 1. (* 2号惯导设备 *)

(*The definition of empty state*)
Definition emp_sO : storeO :=
  fun (n : id) => 0.

Definition emp_sV : storeV :=
  fun (n : id) => 0.

Definition emp_sS : storeS :=
  fun (n : id) => [].

Definition empty_st : state := 
  (emp_sO, emp_sV, emp_sS, emp_heapR, emp_heapO).

