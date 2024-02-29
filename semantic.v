Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.Lists.List.
Require Import state.
Require Import util. 
Require Import Aid. 
Require Import language.
Require Import function.  
Import ListNotations.

(*算术表达式*)
Fixpoint aeval (stoV: storeV) (a: aexp) : nat :=
  match a with
  | ANum n =>  n
  | Atuple2 tuple2 => 1 (* 代表合法的二元组，用于match匹配而已 *)
  | Atuple3 tuple3 => 1 (* 代表合法的三元组，用于match匹配而已 *)
  | Atuple4 tuple4 => 1 (* 代表合法的四元组，用于match匹配而已 *)
  | Atuple2_First  tuple2 => tuple2_return_first_element tuple2
  | Atuple2_Second tuple2 => tuple2_return_second_element tuple2
  | Atuple3_First  tuple3 => triple3_return_first_element tuple3
  | Atuple3_Second tuple3 => triple3_return_second_element tuple3
  | Atuple3_Third  tuple3 => triple3_return_third_element tuple3
  | Atuple4_First  tuple4 => triple4_return_first_element tuple4
  | Atuple4_Second tuple4 => triple4_return_second_element tuple4
  | Atuple4_Third  tuple4 => triple4_return_third_element tuple4
  | Atuple4_Fourth tuple4 => triple4_return_fourth_element tuple4
  | AId x =>  stoV x
  | APlus a1 a2 => (aeval stoV  a1) + (aeval stoV  a2)
  | AMult a1 a2 => (aeval stoV  a1) * (aeval stoV  a2)
  | AMinus a1 a2 =>(aeval stoV  a1) - (aeval stoV  a2)
  end. 

(* 给定的作业列表 li 中查找特定位置 loc 的元素 *)
Fixpoint findoe (li:list nat) (loc:nat): option nat :=
match li with
| [] => None
| x::xli => if (beq_nat loc 1) then Some x else (findoe xli (loc-1))
end.

(* 给定的资源列表 li 中查找特定位置 loc 的元素 *)
Fixpoint findre_helper (xli : list (option nat)) (loc : nat) {struct xli} : option nat :=
  match xli with
  | [] => None
  | x :: xl => if beq_nat loc 1 then  x else findre_helper (xl) (loc - 1)
  end.

Fixpoint list_length {A : Type} (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: t => S (list_length t)
  end.

Fixpoint findre (li : option (list (option nat))) (loc : nat) {struct li} : option nat :=
  match li with
  | None => None
  | Some xli => findre_helper xli loc
  end.

(* 资源表达式 *)
Fixpoint reval (stoO:storeO) (stoV:storeV) 
                (heaO:heapO) (re:rexp) : option nat :=
match re with
| RNum n => Some n
| RId name => Some (stoV name)
| RAddr n a =>  findre ( heaO n ) (aeval stoV a )
end.

(* 作业表达式 *)
Fixpoint oeval (stoO:storeO) (stoV:storeV) 
                (stoS:storeS) (oe:oexp) : option nat :=
match oe with
| ONull => None
| ONum n => Some n
| OId name => Some (stoO name)
| OAddr sname a => findoe (stoS sname) (aeval stoV a)
end.

(* 列表拼接 *)
Fixpoint append {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: xs => x :: append xs l2
  end.
(* option nat 转化为nat *)
Definition option_nat_to_nat (o : option nat) : nat :=
  match o with
  | Some n => n
  | None => 0 
  end.

(* option (list (option nat)) 转化为 list (option nat)*)
Definition option_list_to_list {A : Type} (o : option (list A)) : list A :=
  match o with
  | Some l => l
  | None => []
  end.

(* option (list (option nat)) 转化为 list nat*)
Fixpoint flatten_option_list {A : Type} (optList : option (list (option A))) : list A :=
  match optList with
  | Some lst => concat (map (fun optA => match optA with Some a => [a] | None => [] end) lst)
  | None => []
  end.

(* list nat转化为list (option nat) *)
Fixpoint wrap_with_option {A : Type} (lst : list A) : list (option A) :=
  match lst with
  | [] => []
  | x :: rest => Some x :: wrap_with_option rest
  end.

(* 站位表达式 *)
Fixpoint seval (stoO:storeO) (stoV:storeV) 
                (stoS:storeS) (se:sexp) : list nat :=
match se with
| SNull => []
| SFin =>  [0] (* 使用[0]代表某个特定的值，表示完成*)
| SId name => stoS name
  | SOattach se1 oe2 => 
    match (seval stoO stoV stoS se1, option_nat_to_nat(oeval stoO stoV stoS oe2)) with
    | (li, n2) =>  append li [n2]
    end
  | SSattach se1 se2 =>
    match (seval stoO stoV stoS se1, seval stoO stoV stoS se2) with
    | (l1, l2) => append l1 l2
    end 
  end.

(*布尔表达式*)
Fixpoint beval stoV (b:bexp) : option bool :=
match b with
| BTrue   => Some true
| BFalse  => Some false
| BEq a1 a2 => Some (beq_nat (aeval stoV a1) (aeval stoV a2))
| BLe a1 a2 => Some (leb (aeval stoV a1) (aeval stoV a2))
| BZd t1 t2 => Some (unfoldWing t1 t2)
| BTr t1 c  => Some (Tractor_need t1 c)
| BMod a b  => Some (check_mod a b) 

| BNot b1   =>(match (beval stoV b1) with
               | None => None
               | Some x => Some (negb x)
               end)
| BAnd b1 b2  =>(match (beval stoV b1), (beval stoV b2) with
                 | None,_ => None
                 | _,None => None
                 | Some x1,Some x2 => Some (andb x1 x2)
                 end)
| BOr  b1 b2  =>(match (beval stoV b1), (beval stoV b2) with
                 | None,_ => None
                 | _,None => None
                 | Some x1, Some x2 => Some (orb x1 x2)
                 end)
end.


(* auxiliary function *)
(*可选类型的nat比较*)
Definition beq_op_nat (x y: option nat) : bool :=
match x,y with
| None,None => true
| Some n1,Some n2 => beq_nat n1 n2
| _,_ => false
end.

Fixpoint nth_list (n:nat) (l:list nat) :option nat :=
match n,l with
| _, [] => None
| O,(h::t) => Some h
| S n,(h::t) => nth_list n t
end.

Fixpoint nth_list_o (n:nat) (l:list (option nat)) :option nat :=
match n,l with
| _, (None::t) => None
| _, [] => None
| S O,(Some h::t) => Some h
| O, _ => None
| S n,(Some h::t) => nth_list_o n t
end.

Fixpoint nth_update (i m:nat) (l:list nat) :list nat :=
match i,l with
| _, [] => []
| O, (h::t) => [m] ++ t
| S n,(h::t) => nth_update n m t
end.

Definition nth_list_update (i m:nat) (l:list nat) :list nat :=
let rest := firstn i l in 
 rest ++ nth_update i m l.

Definition value_change (n:nat) :=
  fun m => if beq_nat m n then m else n.

Fixpoint list_update (li:list nat) (n : nat) : list nat :=
  map (value_change n) li.

Fixpoint in_list (li:list (option nat)) (x:option nat) : bool :=
match li with
| [] => false
| t::xli => if beq_op_nat t x then true else in_list xli x
end.

(* 去除列表 li 的最后一个元素 *)
Fixpoint cuttail (li:list nat) : list nat :=
match li with
| [] => []
| [h] => []
| h :: t => h :: cuttail t
end.

(* 去除列表li的第一个元素 *)
Fixpoint remove_first_element (li : list nat) : list nat :=
  match li with
  | [] => []  
  | _ :: tail => tail 
  end.

Fixpoint cuttail_o (li:list (option nat)) : list (option nat) :=
match li with
| [] => []
| [_] => []
| None :: t => []
| Some h :: t => Some h :: cuttail_o t
end.

(* 将一个包含 option nat 类型元素的列表（nli）转换为一个只包含 nat 类型元素的列表。 *)
Definition get_content (nli:list (option nat)) : list nat :=
let f := fun t => match t with
                 | Some n => n
                 | None => 0
                 end
in (map f nli).

Fixpoint all_none (opli:list (option nat)) : bool :=
match opli with
| [] => true
| x::li => if beq_op_nat x None then all_none li
           else false
end.

Fixpoint h_unionO_many (hO:heapO) (locli :list (option nat)) (nli : list (list (option nat))) : heapO :=
match locli,nli with
| bloc::blocs,l::ls => h_unionO_many (hO_update hO (o2v bloc) l) blocs ls
| [],[] => hO
| _,_ => hO
end.


Definition OeSafe stoO stoV stoS (hr:heapR) (hO:heapO) oe ol olist: Prop :=  
    (oeval stoO stoV stoS oe) = Some ol ->
    hO ol = Some olist ->
    forall l, in_list olist l = true ->
              exists k, hr (o2v l) = Some k.

(* 指令集 *)
Inductive ceval: command -> state -> ext_state -> Prop :=
(**旧指令集**)
| E_Skip  : forall stat,
              ceval CSkip stat (St stat)

| E_Abt   : forall stat,
              ceval CAbt stat Abt

| E_Ass   : forall stoO stoV stoS hR hO x a n, (aeval stoV a) = n ->
              ceval (CAss x a) (stoO,stoV,stoS,hR,hO)
                       (St(stoO,(x !sv-> n; stoV),stoS,hR,hO))

| E_Seq   : forall c1 c2 st0 st1 opst,
              ceval c1 st0 (St st1) ->
              ceval c2 st1 opst ->
              ceval (CSeq c1 c2) st0 opst

| E_Seq_Ab: forall c1 c2 st0,
              ceval c1 st0 Abt ->
              ceval (CSeq c1 c2) st0 Abt

| E_IfTure: forall stoO stoV stoS hR hO opst b c1 c2,
              beval stoV b = Some true ->
              ceval c1 (stoO,stoV,stoS,hR,hO) opst ->
              ceval (CIf b c1 c2) (stoO,stoV,stoS,hR,hO) opst

| E_IfFalse: forall stoO stoV stoS hR hO opst b c1 c2,
              beval stoV b = Some false ->
              ceval c2 (stoO,stoV,stoS,hR,hO) opst ->
              ceval (CIf b c1 c2) (stoO,stoV,stoS,hR,hO) opst

| E_If_Ab : forall stoO stoV stoS hR hO b c1 c2,
              beval stoV b = None ->
              ceval (CIf b c1 c2) (stoO,stoV,stoS,hR,hO) Abt


| E_WhileEnd : forall b stoO stoV stoS hR hO c,
                 beval stoV b = Some false ->
                 ceval (CWhile b c) (stoO,stoV,stoS,hR,hO) (St (stoO,stoV,stoS,hR,hO))

| E_WhileLoop : forall stoO stoV stoS hR hO opst b c st,
                  beval stoV b = Some true ->
                  ceval c (stoO,stoV,stoS,hR,hO) (St st) ->
                  ceval (CWhile b c) st opst ->
                  ceval (CWhile b c) (stoO,stoV,stoS,hR,hO) opst

| E_WhileLoop_Ab : forall stoO stoV stoS hR hO b c,
                  beval stoV b = Some true ->
                  ceval c (stoO,stoV,stoS,hR,hO) Abt ->
                  ceval (CWhile b c) (stoO,stoV,stoS,hR,hO) Abt

| E_While_Ab :  forall stoO stoV stoS hR hO b c,
                  beval stoV b = None ->
                  ceval (CWhile b c) (stoO,stoV,stoS,hR,hO) Abt

(**分离逻辑的指令集**)
| E_Cons : forall stoO stoV stoS hR hO a n x l,
              aeval stoV a = n ->
              hR l = None ->
              ceval  (CCons x a) (stoO,stoV,stoS,hR,hO)
                       (St (stoO,(x !sv-> l; stoV),stoS,
                            (l !hr-> n; hR), hO))

| E_Lookup : forall stoO stoV stoS hR hO x a1 l n,
                aeval stoV a1 = l ->
                hR l = Some n ->
                ceval (CLookup x a1) (stoO,stoV,stoS,hR,hO) 
                          (St (stoO,(x !sv-> l; stoV),stoS,
                             hR, hO))

| E_Lookup_Ab : forall stoO stoV stoS hR hO x a1 l,
                   aeval stoV  a1 = l ->
                   hR l = None ->
                   ceval (CLookup x a1) (stoO,stoV,stoS,hR,hO) Abt

| E_Mutate : forall stoO stoV stoS hR hO a1 a2 n1 n2,
                  aeval stoV  a1 = n1 ->
                  aeval stoV  a2 = n2 ->
                  in_domR n1 hR ->
                  ceval (CMutate a1 a2) (stoO,stoV,stoS,hR,hO) 
                           (St (stoO,stoV,stoS,(n1 !hr-> n2; hR),hO))

| E_Mutate_Ab : forall stoO stoV stoS hR hO a1 a2 n1,
                     aeval stoV a1 = n1 ->
                     hR n1 = None ->
                     ceval (CMutate a1 a2) (stoO,stoV,stoS,hR,hO) Abt

| E_Dispose : forall stoO stoV stoS hR hO a1 n1,
                 aeval stoV a1 = n1 ->
                 in_domR n1 hR ->
                 ceval
                   (CDispose a1) (stoO,stoV,stoS,hR,hO)
                   (St (stoO,stoV,stoS,(hR_remove hR n1),hO))

| E_Dispose_Ab : forall stoO stoV stoS hR hO a1 n1,
                    aeval stoV a1 = n1 ->
                    hR n1 = None ->
                    ceval (CDispose a1) (stoO,stoV,stoS,hR,hO) Abt

(**新指令集**)
(*站位指令 *)
| E_Sass : forall stoO stoV stoS hR hO se oe bloc,
                oeval stoO stoV stoS oe = Some bloc ->
                 ceval (CSass se oe ) (stoO,stoV,stoS,hR,hO)
                          (St (stoO,stoV,(se !ss-> [bloc]; stoS),hR,hO))

| E_Sass_Abt : forall stoO stoV stoS hR hO se oe,
                 oeval stoO stoV stoS oe = None ->
                 ceval (CSass se oe) (stoO,stoV,stoS,hR,hO) Abt

| E_Sattach : forall stoO stoV stoS hR hO se oe ss bloc,
                        oeval stoO stoV stoS oe = Some bloc ->
                        stoS se = ss ->
                        ceval (CSattach se oe) (stoO,stoV,stoS,hR,hO)
                                 (St (stoO,stoV,(se !ss-> (ss ++ [bloc]); stoS),hR,hO))

| E_Sattach_Abt : forall stoO stoV stoS hR hO se oe,
                          oeval stoO stoV stoS oe = None ->
                          ceval (CSattach se oe) (stoO,stoV,stoS,hR,hO) Abt

| E_Sdelete : forall stoO stoV stoS hR hO se,
                ceval (CSdelete se) (stoO,stoV,stoS,hR,hO)
                         (St (stoO,stoV,(se !ss-> nil;stoS),hR,hO))


| E_Srestart : forall stoO stoV stoS hR hO se,
                ceval (CSrestart se) (stoO,stoV,stoS,hR,hO)
                         (St (stoO,stoV,(se !ss-> nil;stoS),hR,hO))


| E_Slength : forall stoO stoV stoS hR hO se ss m x,
              stoS se = ss ->
              length ss = m ->
              ceval (CSlength x se) (stoO,stoV,stoS,hR,hO)
                    (St (stoO,(x !sv-> m;stoV),stoS,hR,hO))

| E_Sasgn : forall stoO stoV stoS hR hO se oe loc,
                oeval stoO stoV stoS oe = Some loc ->
                 ceval (CSasgn se oe ) (stoO,stoV,stoS,hR,hO)
                          (St (stoO,stoV,(se !ss-> [loc]; stoS),hR,hO))

| E_Satt : forall stoO stoV stoS hR hO se oe ss loc,
                 oeval stoO stoV stoS oe = Some loc ->
                                 stoS se = ss ->
                        ceval (CSatt se oe) (stoO,stoV,stoS,hR,hO)
                                 (St (stoO,stoV,(se !ss-> (ss ++ [loc]); stoS),hR,hO))

| E_Sexe : forall stoO stoV stoS hR hO n se e loc ss llist, 
            stoS se = ss ->
                 stoO e = loc ->
                   hO loc = Some llist ->
                    (forall l, in_list llist l = true -> exists k, hR (o2v l) = k) ->
                   ceval (CSexe se (ANum n))(stoO,stoV,stoS,hR,hO)
                                 (St ((e !so->0;stoO),stoV,(se !ss-> (remove_at n ss); stoS),(hR_removes hR (map o2v llist)),(hO_remove hO loc)))

| E_Sfree : forall stoO stoV stoS hR hO se,
              stoS se = null ->
                ceval (CSfree se) (stoO,stoV,stoS,hR,hO)
                         (St (stoO,stoV,(se !ss-> on;stoS),hR,hO))

| E_Sreuse : forall stoO stoV stoS hR hO e oe se loc,
              stoS se = on ->
                 stoO e = loc -> 
                   ceval (CSreuse se oe) (stoO,stoV,stoS,hR,hO)
                         (St (stoO,stoV,(se !ss-> [loc];stoS),hR,hO))

(*作业指令 *)
| E_Ocreate : forall stoO stoV stoS hR hO oe re loc bloc,
                reval stoO stoV hO re = Some bloc ->
                 ceval (COcreate oe re) (stoO,stoV,stoS,hR,hO)
                          (St (stoO,stoV,stoS,hR,(loc !ho-> [Some bloc] ; hO)))

| E_Ocreate_Abt : forall stoO stoV stoS hR hO oe re,
                 reval stoO stoV hO re = None ->
                 ceval (COcreate oe re) (stoO,stoV,stoS,hR,hO) Abt

| E_Oalloc :  forall stoO stoV stoS hR hO oe oe1 n bloc,
                aeval  stoV oe1 =  n ->
                 ceval (COalloc oe oe1) (stoO,stoV,stoS,hR,hO)
                          (St ((oe !so-> bloc; stoO),stoV,stoS,hR,hO))

| E_Oattach : forall stoO stoV stoS hR hO oe re rr loc,
                        reval stoO stoV hO re = Some loc ->
                        rr = hO loc ->
                        ceval (COattach oe re ) (stoO,stoV,stoS,hR,hO)
                                 (St (stoO,stoV,stoS,hR,(loc !ho-> (option_list_to_list rr ++ [Some loc]) ; hO)))

| E_Oattach_Abt : forall stoO stoV stoS hR hO oe re,
                          reval stoO stoV hO re = None ->
                          ceval (COattach oe re) (stoO,stoV,stoS,hR,hO) Abt

| E_OLookup : forall stoO stoV stoS hR hO x a1 l n,
                aeval stoV a1 = l ->
                hR l = Some n ->
                ceval (CLookup x a1) (stoO,stoV,stoS,hR,hO) 
                          (St (stoO,(x !sv-> l; stoV),stoS,
                             hR, hO))

| E_Odelete : forall stoO stoV stoS hR hO loc ,
                ceval (COdelete loc) (stoO,stoV,stoS,hR,hO)
                         (St (stoO,stoV,stoS,hR,(loc !ho->  [None] ; hO)))

| E_Olength : forall stoO stoV stoS hR hO loc rr m x,
              hO loc = rr ->
              length (option_list_to_list rr) = m ->
              ceval (COlength loc x) (stoO,stoV,stoS,hR,hO)
                    (St (stoO,(x !sv-> m;stoV),stoS,hR,hO))

| E_Oplan_ZD : forall stoO stoV stoS hR hO oe tuple4 loc n1 n2 n3 n4 loc1 loc2 loc3 loc4,
                aeval stoV (Atuple4_First tuple4) = n1 ->
                  aeval stoV (Atuple4_Second tuple4) = n2 ->
                   aeval stoV (Atuple4_Third tuple4) = n3 ->
                    aeval stoV (Atuple4_Fourth tuple4) = n4 ->
                      hR loc1 = None -> hR loc2 = None ->
                      hR loc3 = None -> hR loc4 = None ->
                        stoO oe = 0 ->
                 ceval (COplan_ZD oe (Atuple4 tuple4)) (stoO,stoV,stoS,hR,hO)
                          (St ((oe !so-> loc;stoO),stoV,stoS,(loc1 !hr-> n1;loc2 !hr-> n2;loc3 !hr-> n3;loc4 !hr-> n4;hR),(loc !ho->  [(Some loc1);(Some loc2);(Some loc3);(Some loc4)] ; hO)))

| E_Oplan_QYC : forall stoO stoV stoS hR hO oe tuple2 loc  n1 n2 loc1 loc2,
                aeval stoV (Atuple2_First tuple2) = n1 ->
                 aeval stoV (Atuple2_Second tuple2) = n2 ->
                      hR loc1 = None -> hR loc2 = None ->
                         stoO oe = 0 ->
                 ceval (COplan_QYC oe (Atuple2 tuple2)) (stoO,stoV,stoS,hR,hO)
                          (St ((oe !so-> loc;stoO),stoV,stoS,(loc1 !hr-> n1;loc2 !hr-> n2;hR),(loc !ho->  [(Some loc1);(Some loc2)] ; hO)))

| E_Oplan_GY : forall stoO stoV stoS hR hO oe tuple3 loc n1 n2 n3 loc1 loc2 loc3,
                aeval stoV  (Atuple3_First tuple3) = n1 ->
                  aeval stoV  (Atuple3_Second tuple3) = n2 ->
                   aeval stoV  (Atuple3_Third tuple3) = n3 ->
                      hR loc1 = None -> hR loc2 = None -> hR loc3 = None ->
                        stoO oe = 0 ->
                 ceval (COplan_GY oe (Atuple3 tuple3)) (stoO,stoV,stoS,hR,hO)
                          (St ((oe !so-> loc;stoO),stoV,stoS,(loc1 !hr-> n1;loc2 !hr-> n2;loc3 !hr-> n3;hR),(loc !ho->  [(Some loc1);(Some loc2);(Some loc3)] ; hO)))

| E_Oplan_GD : forall stoO stoV stoS hR hO oe tuple3 loc n1 n2 n3 loc1 loc2 loc3,
                aeval stoV  (Atuple3_First tuple3) = n1 ->
                  aeval stoV (Atuple3_Second tuple3) = n2 ->
                   aeval stoV (Atuple3_Third tuple3) = n3 ->
                      hR loc1 = None -> hR loc2 = None -> hR loc3 = None ->
                           stoO oe = 0 ->
                 ceval (COplan_GD oe (Atuple3 tuple3)) (stoO,stoV,stoS,hR,hO)
                          (St ((oe !so-> loc;stoO),stoV,stoS,(loc1 !hr-> n1;loc2 !hr-> n2;loc3 !hr-> n3;hR),(loc !ho->  [(Some loc1);(Some loc2);(Some loc3)] ; hO)))

| E_Oplan_JY : forall stoO stoV stoS hR hO oe tuple3 loc n1 n2 n3 loc1 loc2 loc3,
                aeval stoV (Atuple3_First tuple3) = n1 ->
                  aeval stoV (Atuple3_Second tuple3) = n2 ->
                   aeval stoV (Atuple3_Third tuple3) = n3 ->
                      hR loc1 = None -> hR loc2 = None -> hR loc3 = None ->
                        stoO oe = 0 ->
                 ceval (COplan_JY oe (Atuple3 tuple3)) (stoO,stoV,stoS,hR,hO)
                          (St ((oe !so-> loc;stoO),stoV,stoS,(loc1 !hr-> n1;loc2 !hr-> n2;loc3 !hr-> n3;hR),(loc !ho->  [(Some loc1);(Some loc2);(Some loc3)] ; hO)))

| E_Oplan_TF : forall stoO stoV stoS hR hO oe tuple3 loc n1 n2 n3 loc1 loc2 loc3 ,
                aeval stoV (Atuple3_First tuple3) = n1 ->
                  aeval stoV (Atuple3_Second tuple3) = n2 ->
                   aeval stoV (Atuple3_Third tuple3) = n3 ->
                      hR loc1 = None -> hR loc2 = None -> hR loc3 = None ->
                        stoO oe = 0 ->
                 ceval (COplan_TF oe (Atuple3 tuple3)) (stoO,stoV,stoS,hR,hO)
                          (St ((oe !so-> loc;stoO),stoV,stoS,(loc1 !hr-> n1;loc2 !hr-> n2;loc3 !hr-> n3;hR),(loc !ho->  [(Some loc1);(Some loc2);(Some loc3)] ; hO)))


(*资源指令*)
| E_Rnew : forall stoO stoV stoS hR hO b loc bloc,
              hO loc = None ->
              ceval (CRnew b) (stoO, stoV, stoS, hR, hO)
                    (St (stoO, (b !sv-> bloc; stoV), stoS, 
                          hR, (loc !ho-> [v2o bloc];hO)))

| E_Rsize : forall stoO stoV stoS hR hO bk x bloc llist m,
              (reval stoO stoV hO bk) = Some bloc ->
              hO bloc = Some llist ->
              (forall l, in_list llist l = true -> exists k, hR (o2v l) = k) ->
              length llist = m ->
              ceval (CRlength x bk) (stoO,stoV,stoS,hR,hO)
                    (St (stoO,(x !sv-> m; stoV),stoS,hR,hO))

| E_Rreplace : forall stoO stoV stoS hR hO bk bloc llist f ff loc e i,
              (reval stoO stoV hO bk) = Some bloc ->
              hO bloc = Some llist ->
              (forall l, in_list llist l = true -> exists k, hR (o2v l) = k) ->
              ff = hO loc ->
              (aeval stoV e) = i ->
              ceval (CRreplace (OId f) e bk) (stoO,stoV,stoS,hR,hO)
                         (St (stoO,stoV,stoS,hR,(loc !ho-> wrap_with_option (nth_list_update i bloc (flatten_option_list ff)) ;hO)))

| E_Rlookup : forall stoO stoV stoS hR hO bk bloc loc llist e x m j,
              (reval stoO stoV hO bk) = Some bloc ->
              hO bloc = Some llist ->
              (forall l, in_list llist l = true -> exists k, hR (o2v l) = k) ->
              aeval stoV  e = j ->
              nth_list_o j llist = Some loc ->
              hR loc = Some m ->
                ceval (CRlookup x bk e) (stoO,stoV,stoS,hR,hO)
                         (St (stoO,(x !sv-> m;stoV),stoS,hR,hO))

| E_Rtruncate : forall stoO stoV stoS hR hO bk bloc llist,
              (reval stoO stoV hO bk) = Some bloc ->
              hO bloc = Some llist ->
              (forall l, in_list llist l = true -> exists k, hR (o2v l) = k) ->
              ceval (CRtruncate bk) (stoO,stoV,stoS,hR,hO)
                    (St (stoO,stoV,stoS,hR,(bloc !ho-> cuttail_o llist; hO)))

| E_Radd : forall stoO stoV stoS hR hO b n,
              stoV b  = n ->
              ceval (CRadd b) (stoO, stoV, stoS, hR, hO)
                    (St (stoO, (b !sv-> (n+1);stoV), stoS, hR, hO))

| E_Rsub : forall stoO stoV stoS hR hO b n ,
              stoV b  = n ->
              ceval (CRsub b) (stoO, stoV, stoS, hR, hO)
                    (St (stoO, (b !sv-> (n-1);stoV), stoS, hR, hO)).

Notation "st '=[' c ']=>' st'" := (ceval c st st') (at level 40).

