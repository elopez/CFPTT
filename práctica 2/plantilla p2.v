Section Ejercicio1.


Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.

Theorem e11 : (forall x:U, A(x)) -> forall y:U, A(y).
Proof.
  
Qed.

Theorem e12 : (forall x y:U, (R x y)) -> forall x y:U, (R y x).
Proof.
  
Qed.


Theorem e13 : (forall x: U, ((A x)->(B x)))
                        -> (forall y:U, (A y))
                          -> (forall z:U, (B z)).
Proof.
  
Qed.


End Ejercicio1.



Section Ejercicio2.

Variable U  : Set.
Variable A B: U -> Prop.
Variable P Q: Prop.
Variable R S: U -> U -> Prop.


Theorem e21 : (forall x:U, ((A x)-> ~(forall x:U, ~ (A x)))).
Proof.
  
Qed.

Theorem e22 : (forall x y:U, ((R x y)))-> (forall x:U, (R x x)).
Proof.
  
Qed.

Theorem e23 : (forall x:U, ((P -> (A x))))
                        -> (P -> (forall x: U, (A x))).
Proof.
  
Qed.


Theorem e24 : (forall x:U, ((A x) /\ (B x)))
                        -> (forall x:U, (A x))
                          -> (forall x:U, (B x)).
Proof.
  
Qed.

End Ejercicio2.



Section Ejercicio3.

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Definition H1 := forall x:U, (R x x).
Definition H2 := forall x y z:U, (R x y) /\ (R x z) -> (R y z).

Theorem e231: H1 /\ H2 -> ... 
Proof.
  ...
Qed.

Definition Irreflexiva := ...
Definition Asimetrica := ...
 
Lemma e232 : Asimetrica -> Irreflexiva.
Proof.
  ...
Qed.

End Ejercicio3.



Section Ejercicio4.

Variable U : Set.
Variable A : U->Prop.
Variable R : U->U->Prop.

Theorem e41: (exists x:U, exists y:U, (R x y)) -> exists y:U, exists x:U, (R x y).
Proof.
  
Qed.

Theorem e42: (forall x:U, A(x)) -> ~ exists x:U, ~ A(x).
Proof.
  
Qed.

Theorem e43: (exists x:U, ~(A x)) -> ~(forall x:U, (A x)).
Proof.
  
Qed.

End Ejercicio4.



Section Ejercicio5.

Variable nat      : Set.
Variable S        : nat -> nat.
Variable a b c    : nat.
Variable odd even : nat -> Prop.
Variable P Q      : nat -> Prop.
Variable f        : nat -> nat.

Theorem e51: forall x:nat, exists y:nat, (P(x)->P(y)).
Proof.
  
Qed.

Theorem e52: exists x:nat, (P x)
                            -> (forall y:nat, (P y)->(Q y))
                               -> (exists z:nat, (Q z)).
Proof.
  
Qed.


Theorem e53: even(a) -> (forall x:nat, (even(x)->odd (S(x)))) -> exists y: nat, odd(y).
Proof.
  
Qed.


Theorem e54: (forall x:nat, P(x) /\ odd(x) ->even(f(x)))
                            -> (forall x:nat, even(x)->odd(S(x)))
                            -> even(a)
                            -> P(S(a))
                            -> exists z:nat, even(f(z)).
Proof.
  
Qed.

End Ejercicio5.



Section Ejercicio6.

Variable nat : Set.
Variable S   : nat -> nat.
Variable le  : nat -> nat -> Prop.
Variable f   : nat -> nat.
Variable P   : nat -> Prop.

Axiom le_n: forall n:nat, (le n n).
Axiom le_S: forall n m:nat, (le n m) -> (le n (S m)).
Axiom monoticity: forall n m:nat, (le n m) -> (le (f n) (f m)).


Lemma le_x_Sx: forall x:nat, (le x (S x)).
Proof.
  
Qed.

Lemma le_x_SSx: forall x:nat, (le x (S (S x))).
Proof.
  
Qed.

Theorem T1: forall a:nat, exists b:nat, (le (f a) b).
Proof.
  
Qed.

End Ejercicio6.



Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

Theorem e71: (forall x:U, ((A x) /\ (B x)))
                       -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
  
Qed.

Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof.
  
Qed.

Theorem e73: (forall x:U, A x) \/ (forall y:U, B y) → forall z:U, A z \/ B z.
Proof.
  
Qed.

End Ejercicio7.


Section Ejercicio9.
Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

Lemma not_ex_not_forall: (~exists x :U, ~A x) -> (forall x:U, A x).
Proof.
  
Qed.

Lemma not_forall_ex_not: (~forall x :U, A x) -> (exists x:U,  ~A x).
Proof.
  
Qed.

End Ejercicio9.



Section Ejercicio10.

Variable nat : Set.
Variable  O  : nat.
Variable  S  : nat -> nat.

Axiom disc   : forall n:nat, ~O=(S n).
Axiom inj    : forall n m:nat, (S n)=(S m) -> n=m.
Axiom allNat : forall n: Nat, n = O \/ exists m: nat, S m = n.

Variable sum prod : nat->nat->nat.

Axiom sum0   : forall n :nat, (sum n O)=n.
Axiom sumS   : forall n m :nat, (sum n (S m))=(S (sum n m)).
Axiom prod0  : forall n :nat, (prod n O)=O.
Axiom prodS  : forall n m :nat, (prod n (S m))=(sum n (prod n m)).

Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
  
Qed.

Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
  
Qed.

Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
  
Qed.

Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
  
Qed.

Lemma L10_3: forall n: nat, exists m: nat, prod n (S m) = sum n n. 
Proof.
  ...
Qed.

Lemma L10_4: forall m n: nat, n <> O -> sum m n <> O.  
Proof.
  ...
Qed.

Lemma L10_5: forall m n: nat, sum m n = O -> m = O /\ n = O.  
Proof.
  ...
Qed.


End Ejercicio10.



Section Ejercicio11.

Variable le : nat->nat->Prop.
Axiom leinv: forall n m:nat, (le n m) -> n=O \/
      (exists p:nat, (exists q:nat, n=(S p)/\ m=(S q) /\ (le p q))).

Lemma notle_s_o: forall n:nat, ~(le (S n) O).
Proof.
  
Qed.

End Ejercicio11.
