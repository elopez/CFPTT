Section Ejercicio3.

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Definition H1 := forall x:U, (R x x).
Definition H2 := forall x y z:U, (R x y) /\ (R x z) -> (R y z).

Definition Reflexividad := forall x:U, (R x x).
Definition Transitividad := forall x y z:U, (R x y) /\ (R y z) -> (R x z).
Definition Simetria := forall x y:U, (R x y) -> (R y x).

Theorem e231: H1 /\ H2 -> Reflexividad /\ Transitividad /\ Simetria.
Proof.
  intros.
  elim H.
  intros.
  unfold H1 in H0.
  unfold H2 in H3.
  repeat split.
    + assumption.
    + unfold Transitividad.
      intros.
      destruct H4.
      apply (H3 y x z).
      split.
        * apply (H3 x y x).
          split.
            - assumption.
            - apply H0. 
        * assumption.
    + unfold Simetria.
      intros.
      apply (H3 x y).
      split.
       * assumption.
       * apply H0.
Qed.

Definition Irreflexiva := forall x:U, ~(R x x).
Definition Asimetrica := forall x y:U, (R x y) -> ~(R y x).
 
Lemma e232 : Asimetrica -> Irreflexiva.
Proof.
  unfold Asimetrica, Irreflexiva, not.
  intros.
  apply (H x x); assumption.
Qed.

End Ejercicio3.

Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

Theorem e71: (forall x:U, ((A x) /\ (B x)))
                       -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
  intros W; split; apply W.
Qed.

Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof.
  intros W; destruct W as (x & W); elim W; intros; [ left | right ]; exists x; assumption.
Qed.

Theorem e73: (forall x:U, A x) \/ (forall y:U, B y) -> forall z:U, A z \/ B z.
Proof.
  intros W x; elim W; intros Z; [ left | right ]; apply Z.
Qed.

End Ejercicio7.

Section Ejercicio9.
Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

Lemma not_ex_not_forall: (~exists x :U, ~A x) -> (forall x:U, A x).
Proof.
  unfold not.
  intros.
  elim (classic (A x)).
    + intros.
      assumption.
    + unfold not.
      intros.
      elim H.
      exists x.
      assumption.
Qed.

Lemma not_forall_ex_not: (~forall x:U, A x) -> (exists x:U, ~A x).
Proof.
  intros.
  elim (classic (exists x:U, ~A x)).
    + intro.
      assumption.
    + intro.
      elim H.
      apply (not_ex_not_forall H0).
Qed.

End Ejercicio9.

Section Ejercicio10.

Variable nat : Set.
Variable  O  : nat.
Variable  S  : nat -> nat.

Axiom disc   : forall n:nat, ~O=(S n).
Axiom inj    : forall n m:nat, (S n)=(S m) -> n=m.
Axiom allNat : forall n:nat, n = O \/ exists m: nat, S m = n.

Variable sum prod : nat->nat->nat.

Axiom sum0   : forall n :nat, (sum n O)=n.
Axiom sumS   : forall n m :nat, (sum n (S m))=(S (sum n m)).
Axiom prod0  : forall n :nat, (prod n O)=O.
Axiom prodS  : forall n m :nat, (prod n (S m))=(sum n (prod n m)).

Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
  rewrite -> sumS.
  rewrite -> sum0.
  reflexivity.
Qed.

Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
  unfold not.
  intros.
  destruct H as (H & (m & H0)).
  replace n with (S m) in H.
  apply (disc m).
  assumption.
Qed.

Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
  intros.
  rewrite -> prodS.
  rewrite -> prod0.
  rewrite -> sum0.
  reflexivity.
Qed.

Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
  unfold not.
  intros.
  apply (disc n).
  apply inj.
  symmetry.
  assumption.
Qed.

Lemma L10_3: forall n: nat, exists m: nat, prod n (S m) = sum n n. 
Proof.
  intros.
  exists (S O).
  repeat rewrite -> prodS.
  rewrite -> prod0.
  rewrite -> sum0.
  reflexivity.
Qed.

Lemma L10_4: forall m n: nat, n <> O -> sum m n <> O.  
Proof.
  unfold not.
  intros.
  elim (allNat n).
    + assumption.
    + intros [m1 H1].
      rewrite <- H1 in H0.
      rewrite -> sumS in H0.
      apply (disc (sum m m1)).
      symmetry.
      assumption.
Qed.

Lemma L10_5: forall m n: nat, sum m n = O -> m = O /\ n = O.  
Proof.
  intros.
  elim (allNat n).
    + intros.
      split.
        * rewrite -> H0 in H.
          rewrite -> sum0 in H.
          assumption.
        * assumption.
    + intros [m0 H1].
      split;
          rewrite <- H1 in H;
          rewrite -> sumS in H;
          symmetry in H;
          apply (disc (sum m m0)) in H;
          contradiction.
Qed.

End Ejercicio10.
