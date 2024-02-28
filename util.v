Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Aid.
Import ListNotations.

Definition null : list nat := nil.
Definition on : list nat := [0].

Inductive id : Type :=
| Id      : string -> id.

(* 定义二元组类型 *)
Inductive tuple2 : Type :=
  | Pair2 : nat -> nat -> tuple2.

(* 返回二元组中第一个值的函数 *)
Definition tuple2_return_first_element (p : tuple2) : nat :=
  match p with
  | Pair2 x _ => x
  end.

(* 修改二元组中第一个值的函数 *)
Definition tuple2_modify_first_element (p : tuple2) (new_value : nat) : tuple2 :=
  match p with
  | Pair2 _ y => Pair2 new_value y
  end.

(* 返回二元组中第二个值的函数 *)
Definition tuple2_return_second_element (p : tuple2) : nat :=
  match p with
  | Pair2 _ y => y
  end.

(* 修改二元组中第二个值的函数 *)
Definition tuple2_modify_second_element (p : tuple2) (new_value : nat) : tuple2 :=
  match p with
  | Pair2 x _ => Pair2 x new_value
  end.

(* 定义三元组类型 *)
Inductive tuple3 : Type :=
  | Triple3 : nat -> nat -> nat -> tuple3.

(* 返回三元组中第一个值的函数 *)
Definition triple3_return_first_element (t : tuple3) : nat :=
  match t with
  | Triple3 x _ _ => x
  end.

(* 修改三元组中第一个值的函数 *)
Definition triple3_modify_first_element (t : tuple3) (new_value : nat) : tuple3 :=
  match t with
  | Triple3 _ y z => Triple3 new_value y z
  end.

(* 返回三元组中第二个值的函数 *)
Definition triple3_return_second_element (t : tuple3) : nat :=
  match t with
  | Triple3 _ y _ => y
  end.

(* 修改三元组中第二个值的函数 *)
Definition triple3_modify_second_element (t : tuple3) (new_value : nat) : tuple3 :=
  match t with
  | Triple3 x _ z => Triple3 x new_value z
  end.

(* 返回三元组中第三个值的函数 *)
Definition triple3_return_third_element (t : tuple3) : nat :=
  match t with
  | Triple3 _ _ z => z
  end.

(* 修改三元组中第三个值的函数 *)
Definition triple3_modify_third_element (t : tuple3) (new_value : nat) : tuple3 :=
  match t with
  | Triple3 x y _ => Triple3 x y new_value
  end.

(* 定义四元组类型 *)
Inductive tuple4 : Type :=
  | Triple4 : nat -> nat -> nat -> nat -> tuple4.

(* 返回四元组中第一个值的函数 *)
Definition triple4_return_first_element (z : tuple4) : nat :=
  match z with
  |  Triple4 x _ _ _ => x
  end.

(* 修改四元组中第一个值的函数 *)
Definition triple4_modify_first_element (t : tuple4) (new_value : nat) : tuple4 :=
  match t with
  | Triple4 _ y z w => Triple4 new_value y z w
  end.

(* 返回四元组中第二个值的函数 *)
Definition triple4_return_second_element (z : tuple4) : nat :=
  match z with
  |  Triple4 _ y _ _ => y
  end.

(* 修改四元组中第二个值的函数 *)
Definition triple4_modify_second_element (t : tuple4) (new_value : nat) : tuple4 :=
  match t with
  | Triple4 x _ z w => Triple4 x new_value z w
  end.

(* 返回四元组中第三个值的函数*)
Definition triple4_return_third_element (z : tuple4) : nat :=
  match z with
  |  Triple4 x y z' w => z'
  end.

(* 修改四元组中第三个值的函数 *)
Definition triple4_modify_third_element (t : tuple4) (new_value : nat) : tuple4 :=
  match t with
  | Triple4 x y _ z => Triple4 x y new_value z
  end. 

(* 返回四元组中第四个值的函数 *)
Definition triple4_return_fourth_element (z : tuple4) : nat :=
  match z with
  |  Triple4 _ _ _ w => w
  end.

(* 修改四元组中第四个值的函数 *)
Definition triple4_modify_fourth_element (t : tuple4) (new_value : nat) : tuple4 :=
  match t with
  | Triple4 x y z _ => Triple4 x y z new_value
  end.

Definition beq_id id1 id2 :=
  match id1,id2 with
  (* string_dec 函数用于比较两个字符串 n1 和 n2 是否相等 *)
  | Id n1, Id n2 => if string_dec n1 n2 then true else false
  end.

Theorem beq_eq_id :
  forall x y : id,
  beq_id x y = true <-> x = y.
Proof.
  intros. split.
  - intros. unfold beq_id in *. destruct x. destruct y.
   destruct (string_dec s s0). +subst. auto. +inversion H.
  - intros. unfold beq_id. destruct x. destruct y.
   destruct (string_dec s s0). +auto. +inversion H. subst.
   destruct n. auto.
Qed.

Theorem beq_neq_id : forall x y ,
  beq_id x y = false <-> x <> y.
Proof.
 split.
  - rewrite <- beq_eq_id.
    unfold not.
    intros.
    rewrite H in H0.
    discriminate.
  - unfold not.
    intros.
    rewrite <- (not_true_is_false (beq_id x y)).
    reflexivity.
    unfold not.
    rewrite beq_eq_id.
    apply H.
Qed.

Theorem beq_id_refl : forall s : id, 
  beq_id s s = true.
Proof.
  intros s.
  unfold beq_id.
  destruct s.
  destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Lemma beq_comm_id : forall m n,
  (beq_id m n) = (beq_id n m).
Proof.
  intros.
  destruct (beq_id m n) eqn : H.
  apply beq_eq_id in H.
  rewrite H.
  rewrite beq_id_refl. trivial.
  apply beq_neq_id in H.
  symmetry. apply beq_neq_id.
  intro. subst.
  apply H. trivial.
Qed.

Definition option_elim (d : nat) (o : option nat) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.






