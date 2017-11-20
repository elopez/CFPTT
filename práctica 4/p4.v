(* Ejercicios a entregar: 9, 12, 14, 17 y 20. *)

Section ej41.

(* Ej 4.1.1 *)
Inductive list (A: Set) : Set :=
      empty_l : list A
    | cons    : A -> list A -> list A.

Inductive bintree (A: Set) : Set :=
      empty_t : bintree A 
    | merge   : A -> bintree A -> bintree A -> bintree A.

(* Ej 4.1.2 *)
Inductive Array {A: Set} : nat -> Set :=
      empty_a : Array 0
    | append {n: nat} : A -> Array n -> Array (n + 1).
 
Inductive Matrix {A: Set} : nat -> nat -> Set :=
      empty_m (n: nat)   : Matrix n 0
    | add_row {n m: nat} : Array n (A:=A) -> Matrix n m -> Matrix n (m+1).
(*  | add_col {n m: nat} : Array m (A:=A) -> Matrix n m -> Matrix (n+1) m. *)

(* Ej 4.1.3 *)
Inductive leq : nat -> nat -> Prop :=
      leq0 (m: nat)   : leq 0 m
    | leqS (n m: nat) : leq n m -> leq (S n) (S m).

(* Ej 4.1.4 *)
Inductive eq_list {A: Set} {R: A -> A -> Prop}: list A -> list A -> Prop :=
      eq_empty_l                       : eq_list (empty_l A) (empty_l A)
    | eq_list_l (m n: list A) (x y: A) : eq_list n m -> R x y -> eq_list (cons A x n) (cons A y m).
 
(* Ej 4.1.5 *)
Inductive sorted_list {A: Set} {lt: A -> A -> Prop}: list A -> Prop :=
      sorted_empty_l                      : sorted_list (empty_l A)
    | sorted_one_l (x: A)                 : sorted_list (cons A x (empty_l A))
    | sorted_list_l (m: list A) (x y : A) : sorted_list (cons A y m) -> lt x y -> sorted_list (cons A x (cons A y m)).

(* Ej 4.1.6 *)
Inductive mirror_bintree {A: Set}: bintree A -> bintree A -> Prop :=
      mirror_empty_t                                 : mirror_bintree (empty_t A) (empty_t A)
    | mirror_merge (s1 s1m s2 s2m: bintree A) (x: A) : mirror_bintree s1 s1m -> mirror_bintree s2 s2m ->
                                                       mirror_bintree (merge A x s1 s2) (merge A x s2m s1m).

(* Ej 4.1.7 *)
Inductive isomorfo_bintree {A: Set}: bintree A -> bintree A -> Prop :=
      isomorfo_empty_t                                 : isomorfo_bintree (empty_t A) (empty_t A)
    | isomorfo_merge (s1 s1i s2 s2i: bintree A) (x: A) : isomorfo_bintree s1 s1i -> isomorfo_bintree s2 s2i ->
                                                         isomorfo_bintree (merge A x s1 s2) (merge A x s1i s2i).

(* Ej 4.1.8 *)
Inductive gtree {A B : Set} : Set :=
      node : A -> gforest -> gtree

with gforest {A B : Set} : Set :=
      empty_f  : B -> gforest
    | add_tree : gtree -> gforest -> gforest.

End ej41.


Section ej43.

(* Ej 4.3.1 *)
Fixpoint sum (n m:nat) {struct n} : nat :=
    match n with
        0    => m
      | S k  => S (sum k m)
    end.

(* Ej 4.3.2 *)
Fixpoint prod (n m:nat) {struct n} : nat :=
    match n with
        0    => 0
      | 1    => m
      | S k  => (sum m (prod k m))
    end.

(* Ej 4.3.3 *)
Fixpoint pot (n m:nat) {struct m} : nat :=
    match m with
        0    => 1
      | 1    => n
      | S k  => (prod n (pot n k))
    end.

(* Ej 4.3.4 *)
Fixpoint leBool (n m:nat) {struct n} : bool :=
    match n, m with
        0, 0 => true
      | 0, _ => true
      | _, 0 => false
      | S k, S r => leBool k r
    end.

End ej43.


Section ej44.

(* Ej 4.4.1 *)
Fixpoint length {A : Set} (l: list A) {struct l} : nat :=
    match l with
         empty_l _  => 0
       | cons _ _ x   => (length x) + 1
    end.

(* Eval compute in length (cons nat 1 (cons nat 1 (empty_l nat))).*)

(* Ej 4.4.2 *)
Fixpoint append_l {A : Set} (l1: list A) (l2: list A) {struct l1} : list A :=
    match l1 with
          empty_l _  => l2
        | cons _ a x => cons A a (append_l x l2)
    end.

(*Eval compute in append_l (cons nat 1 (empty_l nat)) (cons nat 2 (empty_l nat)).*)

(* Ej 4.4.3 *)
Fixpoint reverse {A: Set} (l: list A) : list A :=
    match l with
          empty_l _  => empty_l A
        | cons _ a x => append_l (reverse x) (cons A a (empty_l A))
    end.

(* Eval compute in reverse (cons nat 1 (cons nat 2 (empty_l nat))). *)

(* Ej 4.4.4 *)
Fixpoint filter {A: Set} (f: A -> bool) (l: list A) : list A :=
    match l with
          empty_l _  => empty_l A
        | cons _ a x => if f a then cons A a (filter f x) else filter f x
    end.

(* Eval compute in filter (fun x => leBool x 2) (cons nat 1 (cons nat 2 (empty_l nat))). *)

(* Ej 4.4.5 *)
Fixpoint map {A B: Set} (f: A -> B) (l: list A) {struct l} : list B :=
    match l with
          empty_l _  => empty_l B
        | cons _ a x => cons B (f a) (map f x)
    end.

(* Eval compute in map (fun x => leBool x 1) (cons nat 1 (cons nat 2 (empty_l nat))).*)

(* Ej 4.4.6 *)
Fixpoint exists_ {A: Set} (f: A -> bool) (l: list A) : bool :=
    match l with
          empty_l _  => false
        | cons _ a x => if f a then true else exists_ f x
    end.

(* Eval compute in exists_ (fun x => leBool x 0) (cons nat 1 (cons nat 2 (empty_l nat))). *)

End ej44.


Section ej45.

(* Ej 4.5.1 *)
Fixpoint inverse {A: Set} (t: bintree A) : bintree A :=
    match t with
          empty_t _     => empty_t A
        | merge _ x l r => merge A x (inverse r) (inverse l)
    end.

(* Eval compute in inverse (merge nat 5 (merge nat 5 (empty_t nat) (empty_t nat)) (empty_t nat)). *)

(* Ej 4.5.2 *)
Fixpoint count_externo_gtree {A B: Set} (t: gtree (A:=A)(B:=B)) {struct t} : nat :=
    match t with
          node a forest => count_externo_gforest forest
    end
with count_externo_gforest {A B: Set} (t: gforest (A:=A)(B:=B)) {struct t} : nat :=
    match t with
          empty_f _ => 1
        | add_tree tree forest => count_externo_gtree tree + count_externo_gforest forest
    end.

Fixpoint count_interno_gtree {A B: Set} (t: gtree (A:=A)(B:=B)) {struct t} : nat :=
    match t with
          node a forest => 1 + count_interno_gforest forest
    end
with count_interno_gforest {A B: Set} (t: gforest (A:=A)(B:=B)) {struct t} : nat :=
    match t with
          empty_f _ => 0
        | add_tree tree forest => count_interno_gtree tree + count_interno_gforest forest
    end.

Fixpoint interno_ge_externo {A B: Set} (t: gtree (A:=A)(B:=B)) {struct t} : bool :=
    leBool (1 + (count_externo_gtree t)) (count_interno_gtree t).

End ej45.


Section ej49.

(* Ej 4.9.1 *)
Lemma SumO : forall n : nat, sum n 0 = n /\ sum 0 n = n.
Proof.
intros.
split; try reflexivity.
induction n.
  + reflexivity.
  + simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

(* Ej 4.9.2 *)
Lemma SumS : forall n m : nat, sum n (S m) = sum (S n) m.
Proof.
intros.
induction n.
  + reflexivity.
  + simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

(* Ej 4.9.3 *)
Lemma SumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
Proof.
intros.
induction n.
  + reflexivity.
  + simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

(* Ej 4.9.4 *)
Lemma SumConm : forall n m : nat, sum n m = sum m n.
Proof.
intros.
elim (SumO m).
intros.
induction n, m.
  + reflexivity.
  + simpl.
    rewrite <- H.
    reflexivity.
  + simpl.
    rewrite -> IHn.
    reflexivity.
  + simpl.
    rewrite -> IHn.
    rewrite <- SumS.
    reflexivity.
Qed.

End ej49.


Section ej412.

(* Ej 4.12.1 *)
Lemma L7 : forall (A B : Set) (l m : list A) (f : A -> B), map f (append_l l m) = append_l (map f l) (map f m).
Proof.
intros.
induction l.
  + reflexivity.
  + simpl.
    rewrite <- IHl.
    reflexivity.
Qed.

(* Ej 4.12.2 *)
Lemma L8 : forall (A : Set) (l m : list A) (P : A -> bool), filter P (append_l l m) = append_l (filter P l) (filter P m).
Proof.
intros.
induction l.
  + reflexivity.
  + simpl.
    rewrite -> IHl.
    case (P a); reflexivity.
Qed.

(* Ej 4.12.3 *)
Lemma L9 : forall (A : Set) (l : list A) (P : A -> bool), filter P (filter P l) = filter P l.
Proof.
intros.
induction l.
  + reflexivity.
  + assert ((P a = true) \/ (P a = false)).
      * case (P a); [ left | right ]; reflexivity.
      * elim H; intros; simpl; rewrite -> H0.
          - simpl.
            rewrite -> H0, IHl.
            reflexivity.
          - assumption.
Qed.

(* Ej 4.12.4 *)
Lemma L10 : forall (A : Set) (l m n : list A), append_l l (append_l m n) = append_l (append_l l m) n.
Proof.
intros.
induction l.
  * reflexivity.
  * simpl.
    rewrite <- IHl.
    reflexivity.
Qed.

End ej412.


Section ej414.

(* Ej 4.14 *)
Lemma inverse_works : forall (A : Set) (t: bintree A), mirror_bintree t (inverse t).
Proof.
intros.
induction t.
  * simpl.
    apply mirror_empty_t.
  * simpl.
    apply mirror_merge; assumption.
Qed.

End ej414.


Section ej417.

(* Ej 4.17.1 *)
Inductive posfijo {A: Set} : list A -> list A -> Prop :=
      empty_pos (l : list A) : posfijo l l
    | grow_base (x : A) (l1 l2 : list A) : posfijo l1 l2 -> posfijo l1 (cons A x l2).

Infix "_++" := append_l (left associativity, at level 94).
Infix "<<"  := posfijo (left associativity, at level 94).

(* Ej 4.17.2 *)
Lemma append_maintains_prop : forall {A : Set} (l1 l2 l3 : list A), l2 = (l3 _++ l1) -> (l1 << l2).
Proof.
intros.
rewrite H.
clear H.
induction l3.
  * simpl.
    constructor.
  * simpl.
    constructor.
    apply IHl3.
Qed.

Lemma can_grow_prop : forall {A : Set} (l1 l2 : list A), (l1 << l2) -> (exists l3: list A, l2 = (l3 _++ l1)).
Proof.
intros.
elim H.
  * intros.
    exists (empty_l A).
    reflexivity.
  * intros.
    elim H1.
    intros.
    exists (cons A x x0).
    rewrite -> H2.
    simpl.
    reflexivity.
Qed.

(* Ej 4.17.3 - TODO *)

Lemma pos_l1 : forall {A : Set} (l1 l2 : list A), l2 << (l1 _++ l2).
Proof.
intros.
induction l1.
  + simpl.
    constructor.
  + simpl.
    constructor.
    apply IHl1.
Qed.

Require Import Setoid.
Axiom n_must_be_empty : forall {A : Set} (l n : list A), l = (n _++ l) -> n = empty_l A.
Axiom empty_append_is_empty : forall {A : Set} (l n : list A), (l _++ n) = empty_l A -> n = empty_l A.

Lemma pos_antisymmetry : forall {A : Set} (l1 l2 : list A), (l1 << l2) /\ (l2 << l1) -> (l1 = l2).
Proof.
intros.
destruct H.
elim (can_grow_prop l1 l2 H).
intros.
elim (can_grow_prop l2 l1 H0).
intros.
rewrite H2 in H1.
rewrite L10 in H1.
(* por H1, x0 es empty_l *)
assert ((x _++ x0) = (x _++ x0)); auto.
rewrite -> (n_must_be_empty l2 (x _++ x0) H1) in H3 at 1.
symmetry in H3.
rewrite -> (empty_append_is_empty x x0 H3) in H2.
simpl in H2.
assumption.
Qed.

Lemma pos_transitivity : forall {A : Set} (l1 l2 l3: list A), (l1 << l2) /\ (l2 << l3) -> (l1 << l3).
Proof.
intros.
destruct H.
induction H0.
  * assumption.
  * constructor.
    exact (IHposfijo H).
Qed.

(* Ej 4.17.4 *)

Fixpoint ultimo {A : Set} (l : list A) :=
    match l with
      empty_l _   => empty_l A
    | cons _ a (empty_l _) => cons A a (empty_l A)
    | cons _ a xs => ultimo xs
    end.

Theorem ultimo_pos : forall {A : Set} (l : list A), (ultimo l) << l.
Proof.
induction l.
  * simpl.
    constructor.
  * destruct l; constructor.
    assumption.
Qed.

End ej417.


Section ej420.

(* Ej 4.20.1 *)
Inductive ACom (A: Set) : nat -> Set :=
      singleton_acom       : A -> ACom A 0 
    | merge_acom {n: nat}  : A -> ACom A n -> ACom A n -> ACom A (S n).

(* Ej 4.20.2 *)
Fixpoint h {A : Set} {n : nat} (t : ACom A n) := match t with
      singleton_acom _ _ => 1
    | merge_acom _ _ l r => (h l) + (h r)
end.

Axiom potO : forall n : nat, pot (S n) 0 = 1.  
Axiom potS : forall m: nat, pot 2 (S m) = sum (pot 2 m) (pot 2 m).

(* Ej 4.20.3 *)
Lemma acom_n_is_2n : forall {A: Set} {n: nat} (t: ACom A n), h t = pot 2 n.
intros.
induction t.
  * reflexivity.
  * rewrite -> (potS n);
    simpl.
    rewrite -> IHt1, IHt2.
    reflexivity.
Qed.

End ej420.

