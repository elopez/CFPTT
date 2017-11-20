(* Ejercicio 3 - dependencia del 4 *)
Section Ejercicio3.

Variable A B C: Set.

Definition apply := fun (x : A -> B) (y : A) => (x y).
Definition o_ := fun (x : A -> B) (y : B -> C) => fun (z : A) => (y (x z)).
Definition twice := fun (x : A -> A) (y : A) => (x (x y)).

(* Al cerrar la sección, los operadores anteriores se generalizan *)
End Ejercicio3.


(* Ejercicio 4 *)
Section Ejercicio4.

Variable A: Set.

Infix "o" := (o_ A A A) (at level 80, right associativity).
Definition id := fun (x : A) => x.

Theorem e4_1 : forall x:A, (id o id) x = id x.
Proof.
  reflexivity.
Qed.

Theorem e4_2 : forall x:A, (id o id) x = id x.
Proof.
  cbv delta.
  simpl.
  reflexivity.
Qed.

Theorem e4_3 : forall x:A, (id o id) x = id x.
Proof.
  intros.
  unfold o_, id.
  reflexivity.
Qed.

End Ejercicio4.


(* Ejercicio 5 *)
Section Ejercicio5.

(* 5.1 *)
Definition opI (A : Set) (x : A) := x.
Definition opK (A : Set) (B : Set) (x : A) (y : B) := x.
Definition opS (A : Set) (B : Set) (C : Set) (f : A -> B -> C) (g : A -> B) (x : A) := ((f x) (g x)).

(* 5.2 *)
(* Para formalizar el siguiente lema, determine los tipos ?1 ... ?8 adecuados *)
Lemma e52 : forall A B : Set, opS A (B -> A) A (opK A (B -> A)) (opK A B) = opI A.
Proof.
  reflexivity.
Qed.

End Ejercicio5.


(* Ejercicio 10 *)
Section Ejercicio10.

Parameter Array : Set -> nat -> Set.
Parameter emptyA : forall X : Set, Array X 0.
Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

Parameter Matrix : Set -> nat -> Set.
Parameter emptyM : forall {X : Set}, Matrix X 0.
Parameter addM : forall {X : Set}, forall {n : nat}, Matrix X n -> Array X (n + 1) -> Matrix X (n + 1).

Definition M1 := addM emptyM (addA nat 0 1 (emptyA nat)). (* matriz de una columna *)
Definition M2 := addM M1 (addA nat 1 2 (addA nat 0 2 (emptyA nat))). (* matriz de dos columnas *) 
Definition M3 := addM M2 (addA nat 2 3 (addA nat 1 3 (addA nat 0 3 (emptyA nat)))). (* matriz de tres columnas *)

End Ejercicio10.


(* Ejercicio 11 *)
Section Ejercicio11.

Parameter ABNat : forall n: nat, Set.
Parameter emptyAB : ABNat 0.
Parameter addAB : forall {n: nat}, nat -> ABNat n -> ABNat n -> ABNat (n + 1).

Definition AB1 := addAB 7 emptyAB emptyAB.
Definition AB2 := addAB 3 AB1 AB1.

Check AB2.

Parameter BTree : forall T: Set, forall n: nat, Set.
Parameter emptyBT : forall {T: Set}, BTree T 0.
Parameter addBT : forall {T: Set}, forall {n: nat}, T -> BTree T n -> BTree T n -> BTree T (n + 1).

Definition BT1 := addBT 7 emptyBT emptyBT.
Definition BT2 := addBT 3 BT1 BT1.

Check BT2.

Definition BBT1 := addBT false emptyBT emptyBT.
Definition BBT2 := addBT true BBT1 BBT1.

Check BBT2.

End Ejercicio11.


(* Ejercicio 15 *)
Section Ejercicio15.

Variable U : Set.
Variable e : U.
Variable A B : U -> Prop.
Variable P : Prop.
Variable R : U -> U -> Prop.

Lemma Ej315_1 : (forall x : U, A x -> B x) -> (forall x : U, A x) -> forall x : U, B x.
Proof.
  intros.
  exact (H x (H0 x)).
Qed.

Lemma Ej315_2 : forall x : U, A x -> ~ (forall x : U, ~ A x).
Proof.
  unfold not.
  intros.
  exact (H0 x H).
Qed.

Lemma Ej315_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
  exact (fun D => fun P => fun x => D x P).
Qed.

Lemma Ej315_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
  exact (fun G => fun x => G x x).
Qed.

Lemma Ej315_5 : (forall x y: U, R x y -> R y x) ->
                 forall z : U, R e z -> R z e.
Proof.
  exact (fun C => fun z => C e z).
Qed.

End Ejercicio15.

