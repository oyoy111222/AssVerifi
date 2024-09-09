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

(* 歼35_1 *)
Definition J35_1_ZD : id := Id "J35_1_ZD". (* 折叠 *)
Definition J35_1_DJ : id := Id "J35_1_DJ". (* 飞行员登机及准备 *)
Definition J35_1_KC : id := Id "J35_1_KC". (* 开车及检查 *)
Definition J35_1_NC : id := Id "J35_1_NC". (* 暖车 *)
Definition J35_1_DY : id := Id "J35_1_DY". (* 调运 *)
Definition J35_1_FKZJ : id := Id "J35_1_FKZJ". (* 飞控自检 *)
Definition J35_1_QF : id := Id "J35_1_QF". (* 进入起飞位并弹射 *)

(* 歼35_2 *)
Definition J35_2_ZD : id := Id "J35_2_ZD". (* 折叠 *)
Definition J35_2_DJ : id := Id "J35_2_DJ". (* 飞行员登机及准备 *)
Definition J35_2_KC : id := Id "J35_2_KC". (* 开车及检查 *)
Definition J35_2_NC : id := Id "J35_2_NC". (* 暖车 *)
Definition J35_2_DY : id := Id "J35_2_DY". (* 调运 *)
Definition J35_2_FKZJ : id := Id "J35_2_FKZJ". (* 飞控自检 *)
Definition J35_2_QF : id := Id "J35_2_QF". (* 进入起飞位并弹射 *)

(* 全局变量 *)
Definition d1 : id := Id "d1".
Definition d2 : id := Id "d2".

(* 作业变量 *)

(* 具体作业 *)
Definition o1_DJ : id := Id "o1_DJ".
Definition o1_KC : id := Id "o1_KC".
Definition o1_NC : id := Id "o1_NC".
Definition o1_DY : id := Id "o1_DY".
Definition o1_FKZJ : id := Id "o1_FKZJ".
Definition o1_QF : id := Id "o1_QF".

Definition o2_DJ : id := Id "o2_DJ".
Definition o2_KC : id := Id "o2_KC".
Definition o2_NC : id := Id "o2_NC".
Definition o2_DY : id := Id "o2_DY".
Definition o2_FKZJ : id := Id "o2_FKZJ".
Definition o2_QF : id := Id "o2_QF".

(* 抽象作业 *)
Definition o1_ZD : id := Id "o1_ZD".

Definition o2_ZD : id := Id "o2_ZD".

(* 阵位变量 *)
Definition B5 : id := Id "B5".
Definition B6 : id := Id "B6".
Definition K3 : id := Id "K3".
Definition C3 : id := Id "C3".

(* 用于比较和判断的具体数值 *)
Definition ZD1 : tuple4 := Triple4 184 50 1 1.
Definition ZD1_2 : tuple4 := Triple4 108 62 1 1.
Definition ZD1_3 : tuple4 := Triple4 128 62 1 1.
Definition DJ1 : tuple3 := Triple3 66 0 300.
Definition KC1 : tuple3 := Triple3 66 300 420.
Definition NC1 : tuple3 := Triple3 66 420 540.
Definition DY1 : tuple3 := Triple3 75 540 600.
Definition DY1_2 : tuple3 := Triple3 67 720 780.
Definition FKZJ1 : tuple3 := Triple3 75 600 720.
Definition QF1 : tuple3 := Triple3 67 780 798.

Definition ZD2 : tuple4 := Triple4 175 48 0 1.
Definition ZD2_2 : tuple4 := Triple4 108 62 1 1.
Definition ZD2_3 : tuple4 := Triple4 128 62 1 1.
Definition DJ2 : tuple3 := Triple3 66 0 300.
Definition KC2 : tuple3 := Triple3 66 300 420.
Definition NC2 : tuple3 := Triple3 66 420 540.
Definition DY2 : tuple3 := Triple3 75 660 720.
Definition DY2_2 : tuple3 := Triple3 67 840 900.
Definition FKZJ2 : tuple3 := Triple3 75 720 840.
Definition QF2 : tuple3 := Triple3 67 900 918.

(*The definition of empty state*)
Definition emp_sO : storeO :=
  fun (n : id) => 0.

Definition emp_sV : storeV :=
  fun (n : id) => 0.

Definition emp_sS : storeS :=
  fun (n : id) => [].

Definition empty_st : state := 
  (emp_sO, emp_sV, emp_sS, emp_heapR, emp_heapO).















