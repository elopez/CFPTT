Section Ejercicio3.
Variable A B C: Set.

End Ejercicio3.


Section Ejercicio4.
Variable A: Set.

Definition id := ....

Theorem e4 : forall x:A, ...
Proof.

Qed.

End Ejercicio4.


Section Ejercicio5.

(* 5.1 *)
Definition opI (A : Set) (x : A) := x.

Definition opK ...

Definition opS ...

(* 5.2 *)
(* Para formalizar el siguiente lema, determine los tipos ?1 ... ?8 adecuados *)
Lemma e52 : forall A B : Set, opS ?1 ?2 ?3 (opK ?4 ?5) (opK ?6 ?7) = opI ?8.
Proof.

Qed.

End Ejercicio5.


Section Ejercicio6.
Definition N := forall X : Set, X -> (X -> X) -> X.
Definition Zero (X : Set) (o : X) (f : X -> X) := o.
Definition Uno  (X : Set) (o : X) (f : X -> X) := f (Zero X o f).

(* 6.1 *)
Definition Dos  ...

(* 6.2 *)
Definition Succ ...

Lemma succUno : Succ Uno = Dos.
Proof.

Qed.

(* 6.3 *)
Definition Plus (n m : N) : N
                := fun (X : Set) (o : X) (f : X -> X) => n X (m X o f) f.


Infix "++" := Plus (left associativity, at level 94).

Lemma suma1: (Uno ++ Zero) = Uno.
Proof.

Qed.

Lemma suma2: (Uno ++ Uno) = Dos.
Proof.

Qed.

(* 6.4 *)
Definition Prod (n m : N) : N
                := fun (X:Set) (o:X) (f:X->X) => m X o (fun y:X => n X y f).


Infix "**" := ...

(* 6.5 *)
Lemma prod1 : (Uno ** Zero) = Zero.
Proof.

Qed.

Lemma prod2: (Uno ** Dos) = Dos.
Proof.

Qed.

End Ejercicio6.


Section Ejercicio7.
(* 7.1 *)
Definition Bool := ...
Definition t    := ...
Definition f    := ...

(* 7.2 *)
Definition If ...

(* 7.3 *)
Definition Not ...

Lemma CorrecNot : (Not t) = f /\ (Not f) = t.
Proof.

Qed.

(* 7.4 *)
Definition And ...

Definition And' ...

(* 7.5 *)
Infix "&" := ...

Lemma CorrecAnd : (t & t) = t /\ (f & t) = f /\ (t & f) = f.
Proof.

Qed.

End Ejercicio7.



(* Ejercicio8 *)

Section ArrayNat.
Parameter ArrayNat : forall n:nat, Set.
Parameter empty    : ArrayNat 0.
Parameter add      : forall n:nat, nat -> ArrayNat n -> ArrayNat (n + 1).

(* 8.1 *)

(* 8.2 *)

(* 8.3 *)
Parameter Concat : ...

(* 8.4 *)
Parameter Zip : ...

(* 8.5 *)

(* 8.6 *)
Parameter Array' : ...
Parameter empty' : ...
Parameter add'   : ...
Parameter Zip'   : ...

(* 8.7 *)
Parameter ArrayBool : ...

End ArrayNat.


Section Ejercicio9.
...
End Ejercicio9.


Section Ejercicio10.

Parameter Array : Set -> nat -> Set.
Parameter emptyA : forall X : Set, Array X 0.
Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

Parameter Matrix : Set -> nat -> Set.
Parameter emptyM : ...
Parameter addM : ...

Definition M1 := ... (* matriz de una columna *)
Definition M2 := ... (* matriz de dos columnas *) 
Definition M3 := ... (* matriz de tres columnas *)

Check M3.

End Ejercicio10.


Section Ejercicio11.
...
End Ejercicio11.


Section Ejercicio12.
...
End Ejercicio12.


Section Ejercicio13.
Variable A B C: Set.

Lemma e13_1 : (A -> B -> C) -> B -> A -> C.
Proof.

Qed.

Lemma e13_2 : (A -> B) -> (B -> C) -> A -> C.
Proof.

Qed.

Lemma e13_3 : (A -> B -> C) -> (B -> A) -> B -> C.
Proof.

Qed.

End Ejercicio13.



Section Ejercicio14.
Variable A B C: Prop.

Lemma Ej314_1 : (A -> B -> C) -> A -> (A -> C) -> B -> C.
Proof.
  intros f a g b.
        ...
Qed.

Lemma Ej314_2 : A -> ~ ~ A.
Proof.
  unfold not.
  intros.
     ...
Qed.

Lemma Ej314_3 : (A -> B -> C) -> A -> B -> C.
Proof.
     ...
Qed.

Lemma Ej314_4 : (A -> B) -> ~ (A /\ ~ B).
Proof.
  unfold not.
  intros.
  elim H0; intros.
     ...
Qed.

End Ejercicio14.



Section Ejercicio15.

Variable U : Set.
Variable e : U.
Variable A B : U -> Prop.
Variable P : Prop.
Variable R : U -> U -> Prop.

Lemma Ej315_1 : (forall x : U, A x -> B x) -> (forall x : U, A x) ->
forall x : U, B x.
Proof.
  intros.
   ...
Qed.

Lemma Ej315_2 : forall x : U, A x -> ~ (forall x : U, ~ A x).
Proof.
  unfold not.
  intros.
  ...
Qed.

Lemma Ej315_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
    ...
Qed.

Lemma Ej315_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
     ...
Qed.

Lemma Ej315_5 : (forall x y: U, R x y -> R y x) ->
                 forall z : U, R e z -> R z e.
Proof.
     ...
Qed.

End Ejercicio15.
