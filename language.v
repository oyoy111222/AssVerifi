Require Import util.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.omega.OmegaLemmas.
From Coq Require Import Strings.String.
Import ListNotations.

(* 算术表达式 *)
Inductive aexp: Type :=
| ANum : nat -> aexp
| Atuple2 : tuple2 -> aexp
| Atuple3 : tuple3 -> aexp
| Atuple4 : tuple4 -> aexp
| Atuple2_First  : tuple2 -> aexp
| Atuple2_Second : tuple2 -> aexp
| Atuple3_First  : tuple3 -> aexp
| Atuple3_Second : tuple3 -> aexp
| Atuple3_Third  : tuple3 -> aexp
| Atuple4_First  : tuple4 -> aexp
| Atuple4_Second : tuple4 -> aexp
| Atuple4_Third  : tuple4 -> aexp
| Atuple4_Fourth : tuple4 -> aexp
| AId : id -> aexp    (* Var *)
| APlus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp.

(* 资源表达式 *)
Inductive rexp : Type :=
| RNum : nat -> rexp
| RId  : id -> rexp     (* RVar *)
| RAddr: nat -> aexp -> rexp.

(* 作业表达式 *)
Inductive oexp : Type :=
| ONull : oexp
| ONum : nat -> oexp
| OId  : id -> oexp     (* OVar *)
| OAddr: id -> aexp -> oexp.

(* 站位表达式 *)
Inductive sexp : Type :=
| SNull : sexp
| SFin  : sexp
| SId  : id -> sexp     (* SVar *)
| SOattach : sexp -> oexp -> sexp
| SSattach : sexp -> sexp -> sexp.

(*布尔表达式*)
Inductive bexp: Type :=
| BTrue : bexp
| BFalse: bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
| BZd : tuple4 -> tuple4 -> bexp
| BTr : tuple4 -> nat -> bexp
| BMod : nat -> nat -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp
| BOr  : bexp -> bexp -> bexp.


Inductive command: Type :=
| CSkip    : command
| CAbt    : command
| CAss     : id -> aexp -> command
| CSeq     : command -> command -> command
| CIf      : bexp  -> command -> command -> command
| CWhile   : bexp -> command -> command
| CCons    : id -> aexp -> command  
| CLookup  : id -> aexp -> command
| CMutate  : aexp -> aexp -> command
| CDispose : aexp -> command

(*站位*)
| CSass : id -> oexp -> command  
| CSattach  : id -> oexp -> command 
| CSdelete  : id -> command  
| CSrestart : id -> command 
| CSlength  : id -> id -> command
| CSexe     : id -> aexp -> command
| CSfree  : id -> command  
| CSasgn  : id -> oexp -> command  
| CSatt  : id -> oexp -> command 
| CSreuse  : id -> oexp -> command 

(*作业*)
| COcreate : id -> rexp -> command 
| COattach : id -> rexp -> command 
| COlookup : id -> oexp -> aexp -> command 
| COstart  : id -> oexp -> command 
| COalloc  : id -> aexp -> command
| COdelete : nat -> command
| COlength : nat -> id -> command
| COplan_ZD : id -> aexp -> command
| COplan_GY : id -> aexp -> command
| COplan_GD : id -> aexp -> command
| COplan_JY : id -> aexp -> command 
| COplan_TF : id -> aexp -> command 
| COplan_QYC : id -> aexp -> command
 
(*资源*)
| CRalloc  : id -> aexp -> command
| CRnew    : id -> command
| CRappend : oexp -> aexp -> command
| CRlookup : id -> rexp -> aexp -> command
| CRlength : id -> rexp -> command
| CRreplace : oexp -> aexp -> rexp -> command
| CRtruncate : rexp -> command
| CRdelete : rexp -> command
| CRadd : id -> command
| CRsub : id -> command.

Notation "( a ; b )" := (Pair2 a b) (at level 0, format "( a ; b )").
Notation "( a ; b ; c )" := (Triple3 a b c) (at level 0, format "( a ; b ; c )").
Notation "( a ; b ; c ; d )" := (Triple4 a b c d) (at level 0, format "( a ; b ; c ; d )").
Notation " 'SKIP' " := CSkip.
Notation "x '::=' a" := (CAss x a) (at level 60).
Notation "c1 ;; c2"  := (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IF' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "x '::=plan_ZD' y" := (COplan_ZD x y : command) (at level 80, right associativity).
Notation "x '::=plan_GY' y" := (COplan_GY x y : command) (at level 80, right associativity).
Notation "x '::=plan_QYC' y" := (COplan_QYC x y : command) (at level 80, right associativity).
Notation "x '::=plan_GD' y" := (COplan_GD x y : command) (at level 80, right associativity).
Notation "x '::=plan_JY' y" := (COplan_JY x y : command) (at level 80, right associativity).
Notation "x '::=plan_TF' y" := (COplan_TF x y : command) (at level 80, right associativity).
Notation "x '::=asgn' y" := (CSasgn x y : command) (at level 80, right associativity).
Notation "x '::=att' y" := (CSatt x y : command) (at level 80, right associativity).
Notation "x '::exe' n" := (CSexe x n : command) (at level 80).
Notation "x '::reuse' y" := (CSreuse x y : command) (at level 80, right associativity).
Notation "'free' x" := (CSfree x : command) (at level 80, right associativity).
Notation " x 'add' '1'" := (CRadd x : command) (at level 80, right associativity).
Notation " x 'sub' '1'" := (CRsub x : command) (at level 80, right associativity).
Notation " 'tractor' t1 c" := (BTr t1 c : bexp ) (at level 80, right associativity).







