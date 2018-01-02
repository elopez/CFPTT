(* Ejercicio 6.3 *)
Section ej63.

Definition Value := bool.
Inductive BoolExpr : Set :=
  | bbool : bool -> BoolExpr
  | band : BoolExpr -> BoolExpr -> BoolExpr
  | bnot : BoolExpr -> BoolExpr.
Inductive BEval : BoolExpr -> Value -> Prop :=
  | ebool : forall b : bool, BEval (bbool b) (b:Value)
  | eandl : forall e1 e2 : BoolExpr, BEval e1 false -> BEval (band e1 e2) false
  | eandr : forall e1 e2 : BoolExpr, BEval e2 false -> BEval (band e1 e2) false
  | eandrl : forall e1 e2 : BoolExpr, BEval e1 true -> BEval e2 true -> BEval (band e1 e2) true
  | enott : forall e : BoolExpr, BEval e true -> BEval (bnot e) false
  | enotf : forall e : BoolExpr, BEval e false -> BEval (bnot e) true.

Fixpoint beval1 (e : BoolExpr) : Value :=
  match e with
  | bbool b => b
  | band e1 e2 =>
    match beval1 e1, beval1 e2 with
    | true, true => true
    | _, _ => false
    end
  | bnot e1 => if beval1 e1 then false else true
end.
 
Fixpoint beval2 (e : BoolExpr) : Value :=
  match e with
  | bbool b => b
  | band e1 e2 =>
    match beval2 e1 with
    | false => false
    | _ => beval2 e2
    end
  | bnot e1 => if beval2 e1 then false else true
  end.

(* Ejercicio 6.3.1 - sin hints *)

Lemma beval1C : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
intros.
exists (beval1 e).
induction e; simpl.
  - constructor.
  - destruct (beval1 e1); try constructor; auto.
    destruct (beval1 e2); try apply eandr; try constructor; auto.
  - destruct (beval1 e); constructor; auto.
Qed.

Lemma beval2C : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
intros.
exists (beval2 e).
induction e; simpl.
  - constructor.
  - destruct (beval2 e1); try constructor; auto.
    destruct (beval2 e2); try apply eandr; try constructor; auto.
  - destruct (beval2 e); constructor; auto.
Qed.

(* Ejercicio 6.3.2 - con hints *)

Hint Constructors BEval.

Lemma beval1CH : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
intros.
exists (beval1 e).
induction e; simpl; auto.
  - destruct (beval1 e1), (beval1 e2); auto.
  - destruct (beval1 e); auto.
Qed.

Lemma beval2CH : forall e:BoolExpr, {b:Value |(BEval e b)}.
Proof.
intros.
exists (beval2 e).
induction e; simpl; auto.
  - destruct (beval2 e1), (beval2 e2); auto.
  - destruct (beval2 e); auto.
Qed.

End ej63.

(* Ejercicio 6.3.3/4 - extracción *)
Require Extraction.
Extraction Language Haskell.
(* Ejercicio 6.3.4 - usar tipo bool de Haskell *)
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].

Extraction "beval1C.hs" beval1C.
Extraction "beval2C.hs" beval2C.
Extraction "beval1CH.hs" beval1CH.
Extraction "beval2CH.hs" beval2CH.


(* Ejercicio 6.5 *)
Section ej65.

(* Ejercicio 6.5.1 *)
Inductive Le : nat -> nat -> Prop :=
  | Le_0  : forall n: nat, Le 0 n
  | Le_Sn : forall n m: nat, Le n m -> Le (S n) (S m).

Inductive Gt : nat -> nat -> Prop :=
  | Gt_n  : forall n: nat, Gt (S n) 0
  | Gt_Sn : forall n m: nat, Gt n m -> Gt (S n) (S m).

(* Ejercicio 6.5.2 *)
Fixpoint leBool (n m: nat) :=
  match n, m with
    | 0, _           => true
    | _, 0           => false
    | (S ni), (S mi) => leBool ni mi
  end.

Require Import FunInd.
Functional Scheme leBool_ind := Induction for leBool Sort Set.

Hint Constructors Le.
Hint Constructors Gt.

Lemma Le_Gt_dec: forall n m:nat, {(Le n m)}+{(Gt n m)}.
Proof.
intros.
functional induction (leBool n m) using leBool_ind; simpl; auto.
destruct IHb; [ left | right ]; auto.
Qed.

(* Ejercicio 6.5.3 *)
Require Import Omega.

Lemma le_gt_dec: forall n m:nat, {(le n m)}+{(gt n m)}.
Proof.
intros.
functional induction (leBool n m) using leBool_ind; simpl; auto with arith.
destruct IHb; [ left | right ]; omega. (* sirve auto with arith *)
Qed.

End ej65.


(* Ejercicio 6.6 *)
Section ej66.

Require Import Omega.
Require Import DecBool.
Require Import Compare_dec.
Require Import Plus.
Require Import Mult.

Definition spec_res_nat_div_mod (a b:nat) (qr:nat*nat) :=
  match qr with
    (q,r) => (a = b*q + r) /\ r < b
  end.

Definition nat_div_mod : forall a b:nat, not(b=0) -> {qr:nat*nat | spec_res_nat_div_mod a b qr}.
Proof.
intros.
induction a.
  * exists (0,0); simpl; omega.
  * destruct IHa.
    destruct x.
    induction s.
    case_eq (le_lt_eq_dec (S n0) b); auto.
      + exists (n, (S n0)).
        simpl.
        split; auto with arith; omega.
      + exists ((S n), 0).
        simpl.
        rewrite -> H0.
        rewrite <- e.
        simpl.
        replace (n0 * S n) with (n0 * n + n0); auto with arith.
        split; omega.
Qed.

End ej66.


(* Ejercicio 6.7 *)
Section ej67.

Inductive tree (A:Set) : Set :=
  | leaf : tree A
  | node : A -> tree A -> tree A -> tree A.

Inductive tree_sub (A:Set) (t:tree A) : tree A -> Prop :=
  | tree_sub1 : forall (t':tree A) (x:A), tree_sub A t (node A x t t')
  | tree_sub2 : forall (t':tree A) (x:A), tree_sub A t (node A x t' t).

Theorem well_founded_tree_sub : forall A:Set, well_founded (tree_sub A).
Proof.
unfold well_founded.
intros.
induction a;
constructor;
intros;
inversion H;
auto.
Qed.

End ej67.


(* Ejercicio 6.8 *)
Section ej68.

(* Ejercicio 6.8.1 *)
Fixpoint size (x: BoolExpr) :=
  match x with
  | bbool _  => 1
  | band x y => size x + size y + 1
  | bnot x   => size x + 1
  end.

Definition elt (e1 e2 : BoolExpr) := size e1 < size e2. 

(* Ejercicio 6.8.2 *)
Require Import Wf_nat.
Require Import Inverse_Image.

Theorem well_founded_elt : well_founded (elt).
Proof.
apply (wf_inverse_image BoolExpr nat).
exact lt_wf.
Qed.

End ej68.