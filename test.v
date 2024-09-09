Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import List.
Import ListNotations.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import NeqDefinition.


Fixpoint all_pairs {A : Type} (lst : list A) : list (A * A) :=
  match lst with
  | [] => []
  | x :: xs => (map (fun y => (x, y)) xs) ++ all_pairs xs
  end.

(* Function to check if all pairs in a list are distinct *)
(* 实现了判断列表中元素互不相等的谓词，但是引入了大量证明过程 *)
Definition all_distinct_pairs {A : Type} (pairs : list (A * A)) : Prop :=
  NoDup (map (fun '(x, y) => (x, y)) pairs).

Definition example_neq_3 (lst : list nat) : Prop :=
  length lst = 3 /\ all_distinct_pairs (all_pairs lst).

Lemma neq3 : forall n1 n2 n3,
  example_neq_3 [n1;n2;n3] -> 
  n1<>n2 /\ n1<>n3 /\n2<>n3.

Proof.
  intros n1 n2 n3 H.
  unfold example_neq_3 in H.
  destruct H as [Hlen Hpairs].
  inversion Hlen; subst.
  unfold all_distinct_pairs in Hpairs.
  simpl in Hpairs.
  apply NoDup_cons_iff in Hpairs as [Hn12 Hrest].
  apply NoDup_cons_iff in Hrest as [Hn13 Hn23].
  split; auto.
Qed.

(* Example usage *)
Definition example_neq_46 (lst : list nat) : Prop :=
  length lst = 46 /\ all_distinct_pairs (all_pairs lst).

(* Now, we can use example_neq_46_hypothesis in further proofs *)


(* 辅助函数：将大整数转换为 nat 类型的自然数 *)
Fixpoint pos_to_nat (p : positive) : nat :=
  match p with
  | xI p' => S (2 * pos_to_nat p')  (* 正数情况下，每次乘以2再加1 *)
  | xO p' => 2 * pos_to_nat p'       (* 偶数情况下，每次乘以2 *)
  | xH => 1                          (* 最小的正整数是 1 *)
  end.

(* 主函数：将大整数转换为 nat 类型 *)
Definition large_int_to_nat (z : Z) : nat :=
  match z with
  | Z0 => 0                (* 对于零，返回 0 *)
  | Zpos p => pos_to_nat p (* 对于正数，调用辅助函数处理 *)
  | Zneg _ => 0            (* 对于负数，返回 0，因为不能转换为 nat 类型 *)
  end.

Definition my_large_int : Z := 24534.

Definition my_nat_number : nat := large_int_to_nat my_large_int.

Compute large_int_to_nat 24534.

Fixpoint all_diff {A : Type} (ls : list A) : Prop :=
  match ls with
  | [] => True (* 空列表中的元素互不相等 *)
  | x :: xs => ~ In x xs /\ all_diff xs (* 头元素不在尾列表中，且尾列表中元素互不相等 *)
  end.

(* 定义一个函数检查给定的 40 个自然数是否互不相等 *)
Definition neq_40_ (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23 n24 n25 n26 n27 n28 n29 n30 n31 n32 n33 n34 n35 n36 n37 n38 n39 n40 : nat) : Prop :=
  all_diff [n1; n2; n3; n4; n5; n6; n7; n8; n9; n10; n11; n12; n13; n14; n15; n16; n17; n18; n19; n20; n21; n22; n23; n24; n25; n26; n27; n28; n29; n30; n31; n32; n33; n34; n35; n36; n37; n38; n39; n40].



(* all_diff 是一个函数，它接受一个类型为 A 的列表 ls，并定义了一个命题 NoDup ls，
表示列表 ls 中的元素两两不相等 *)

(* 在 Coq 中，NoDup 不是一个函数，而是一个命题谓词（predicate），用于描述列表中元素的不重复性。
具体来说，NoDup ls 是一个命题，表示列表 ls 中的元素没有重复。 *)

(* 这样可以高级一点，避免大量重复、冗余代码，但是要引入大量证明策略（我还未深入实现），来证明由NoDup可以推出
各个元素互不相等*)





