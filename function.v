Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import GlobalCounter.
Require Export Coq.omega.OmegaLemmas.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Import Coq.Strings.String.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Logic.
Require Import util.
Require Import Aid.
Require Import language.

(* 计算欧式距离的函数 *)
Definition euclidean_distance (p1 p2 : tuple4) : nat :=
  match p1, p2 with
  | Triple4 x1 y1 _ _, Triple4 x2 y2 _ _ =>
    if x1 <=? x2 then
      let dx := x2 - x1 in
      let dy := if y1 <=? y2 then y2 - y1 else y1 - y2 in
      dx * dx + dy * dy
    else (* x1 > x2 *)
      let dx := x1 - x2 in
      let dy := if y1 <=? y2 then y2 - y1 else y1 - y2 in
      dx * dx + dy * dy
  end.

(* 机翼折叠约束的判断函数 *)
Definition unfoldWing (p1 p2 : tuple4) : bool :=
  if (225 <=? euclidean_distance p1 p2) && (euclidean_distance p1 p2 <=? 400) then
     if (triple4_return_third_element p1 =? 0) || (triple4_return_third_element p2 =? 0) then
        true (* 间距在15米到20米之间，一架飞机机翼折叠 *)
     else false
  else if (euclidean_distance p1 p2 <? 225) then
     if (triple4_return_third_element p1 =? 0) && (triple4_return_third_element p2 =? 0) then
          true (* 间距在15米之内，两架飞机机翼都折叠 *)
     else false
  else (* 间距大于20米，两架飞机机翼都展开 *)
     if (triple4_return_third_element p1 =? 1) && (triple4_return_third_element p2 =? 1) then
          true 
     else false.

(* 判断是否需要牵引车函数 *)
(* 如果舰载机引擎关闭，未分配牵引车，则需要分配牵引车 *)
Definition Tractor_need (p1 : tuple4) (c : nat) : bool :=
  match (triple4_return_fourth_element p1 =? 0, c) with
  | (true, 0) => true
  | (false, 1) => true
  | _ => false
  end.

Definition check_mod (a : nat)(b : nat) : bool :=
  match a mod 10 with
  | x => if Nat.eqb x b then true else false
  end.

(* 使用 <=? 操作符的 Notation *)
Notation "x <=? y" := (Nat.leb x y) (at level 70) : nat_scope.
