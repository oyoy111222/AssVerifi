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

(* 舰载机1 *)
Definition i  : id := Id "i".
Definition z1_GY : id := Id "z1_GY". (* 供氧 *)
Definition z1_GD : id := Id "z1_GD". (* 供电 *)
Definition z1_JY : id := Id "z1_JY". (* 加油 *)
Definition z1_TF : id := Id "z1_TF". (* 通风 *)
Definition z1_ZD  : id := Id "z1_ZD". (* 折叠 *)

(* 舰载机2 *)
Definition z2_GY : id := Id "z2_GY".
Definition z2_GD : id := Id "z2_GD".
Definition z2_JY : id := Id "z2_JY".
Definition z2_TF : id := Id "z2_TF".
Definition z2_ZD  : id := Id "z2_ZD".

(* 舰载机3 *)
Definition z3_GY : id := Id "z3_GY".
Definition z3_GD : id := Id "z3_GD".
Definition z3_JY : id := Id "z3_JY".
Definition z3_TF : id := Id "z3_TF".
Definition z3_ZD  : id := Id "z3_ZD".

(* 全局变量 *)
Definition c1 : id := Id "c1".
Definition c2 : id := Id "c2".
Definition c3 : id := Id "c3".
Definition d1 : id := Id "d1".
Definition d2 : id := Id "d2".
Definition d3 : id := Id "d3".

(* 作业变量 *)

(* 舰载机1 *)
Definition o1_ZD : id := Id "o1_ZD".
Definition o1_GY : id := Id "o1_GY".
Definition o1_GD : id := Id "o1_GD".
Definition o1_JY : id := Id "o1_JY".
Definition o1_TF : id := Id "o1_TF".
Definition o1_QYC : id := Id "o1_QYC".

(* 舰载机2 *)
Definition o2_ZD : id := Id "o2_ZD".
Definition o2_GY : id := Id "o2_GY".
Definition o2_GD : id := Id "o2_GD".
Definition o2_JY : id := Id "o2_JY".
Definition o2_TF : id := Id "o2_TF".
Definition o2_QYC : id := Id "o2_QYC".

(* 舰载机3 *)
Definition o3_ZD : id := Id "o3_ZD".
Definition o3_GY : id := Id "o3_GY".
Definition o3_GD : id := Id "o3_GD".
Definition o3_JY : id := Id "o3_JY".
Definition o3_TF : id := Id "o3_TF".
Definition o3_QYC : id := Id "o3_QYC".

(* 阵位变量 *)
Definition p1_M0 : id := Id "p1_M0".
Definition p2_M0 : id := Id "p2_M0".
Definition p3_M0 : id := Id "p3_M0".
Definition p1_M4 : id := Id "p1_M4".
Definition p2_M5 : id := Id "p2_M5".
Definition p3_M5 : id := Id "p3_M5".
Definition p1_M8 : id := Id "p1_M8".

(* 用于比较和判断的具体数值 *)
Definition ZD1 : tuple4 := Triple4 128 128 0 1.
Definition ZD1_2 : tuple4 := Triple4 148 128 1 1.
Definition ZD1_3 : tuple4 := Triple4 120 145 1 1.
Definition GY1 : tuple3 := Triple3 0 0 10.
Definition JY1 : tuple3 := Triple3 41 10 20.
Definition TF1 : tuple3 := Triple3 51 10 20.    
Definition GD1 : tuple3 := Triple3 45 10 40. 
Definition GD1_2 : tuple3 := Triple3 88 50 40. 

Definition ZD2 : tuple4 := Triple4 113 128 1 1.
Definition ZD2_2 : tuple4 := Triple4 135 143 0 1.
Definition GY2 : tuple3 := Triple3 2 10 10.
Definition JY2 : tuple3 := Triple3 51 20 20.
Definition TF2 : tuple3 := Triple3 51 20 20.
Definition GD2 : tuple3 := Triple3 55 20 40. 

Definition ZD3 : tuple4 := Triple4 130 128 0 1.
Definition ZD3_2 : tuple4 := Triple4 130 130 0 1.
Definition GY3 : tuple3 := Triple3 3 15 10.
Definition JY3 : tuple3 := Triple3 51 25 20.
Definition TF3 : tuple3 := Triple3 51 25 20.
Definition GD3 : tuple3 := Triple3 65 20 40.

Definition C1  : nat := 1. 
Definition C2  : nat := 1. 
Definition C3  : nat := 1. 
Definition D1  : nat := 1. 
Definition D2  : nat := 1. 
Definition D3  : nat := 1. 

(*The definition of empty state*)
Definition emp_sO : storeO :=
  fun (n : id) => 0.

Definition emp_sV : storeV :=
  fun (n : id) => 0.

Definition emp_sS : storeS :=
  fun (n : id) => [].

Definition empty_st : state := 
  (emp_sO, emp_sV, emp_sS, emp_heapR, emp_heapO).


