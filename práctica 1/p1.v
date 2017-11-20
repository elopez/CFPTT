(* Trabajo Práctico 1 - Emilio López *)

Section P1.
Variables A B C:Prop.

(* Ej 5.1 *)
Theorem e51: (A->B)-> ~B-> ~A.
Proof.
  unfold not.
  intros.
  exact (H0 (H H1)).
Qed.

(* Ej 5.2 *)
Theorem e52: ~(A/\~A).
Proof.
  unfold not.
  intros.
  elim H.
  intros.
  exact (H1 H0).
Qed.

(* Ej 5.3 *)
Theorem e53: (A->B)-> ~(A/\~B).
Proof.
  unfold not.
  intros.
  elim H0.
  intros.
  exact (H2 (H H1)).
Qed.

(* Ej 5.4 *)
Theorem e54: (A/\B)->~(A->~B).
Proof.
  unfold not.
  intros.
  elim H.
  exact H0.
Qed.

(* Ej 5.5 *)
Theorem e55: (~A /\ ~~A) -> False.
Proof.
  unfold not.
  intros.
  elim H.
  intros.
  exact (H1 H0).
Qed.

(* Ej 6.1 *)
Theorem e61: (A\/B) -> ~(~A/\~B).
Proof.
  unfold not.
  intros.
  elim H0.
  intros.
  elim H; assumption.
Qed.

Lemma or_swap: forall A B:Prop, A\/B -> B\/A.
Proof.
  intros.
  elim H; intro; [ right | left ]; assumption.
Qed.

(* Ej 6.2 *)
Theorem e62: A\/B <-> B\/A.
Proof.
  unfold iff.
  split; [ exact (or_swap A B) | exact (or_swap B A) ].
Qed.

(* Ej 6.3 *)
Theorem e63: A\/B -> ((A->B)->B).
Proof.
  intros.
  elim H.
    + assumption.
    + intros.
      assumption.
Qed.

End P1.


Section Logica_Clasica.
Variables A B C: Prop.

Require Import Classical.
Check classic.

(* Ej 8.1 *)
Theorem elim_dobleneg: forall A:Prop, ~~A->A.
Proof.
  intro.
  elim (classic A0).
    + intros.
      assumption.
    + intros.
      absurd (~A0); assumption.
Qed.

(* Ej 8.2 *)
Theorem e82: forall A B:Prop, (A->B)\/(B->A).
Proof.
  intros.
  elim (classic A0).
    + intros.
      right.
      intro.
      assumption.
    + intros.
      left.
      intros.
      absurd A0; assumption.
Qed.

(* Ej 8.3 *)
Theorem demorgan_1: forall A B:Prop, ~(A/\B)-> ~A \/ ~B.
Proof.
  unfold not.
  intros.
  elim (classic A0).
    + intros.
      right.
      intros.
      apply H.
      split; assumption.
    + intros.
      left.
      exact H0.
Qed.

End Logica_Clasica.


Section Traducciones9.

(* Ej 9 *)
(* Definiciones *)
Variable NM RED CONS UTIL : Prop.

(* Una base de datos no está normalizada o no presenta
   redundancia de información. *)
Hypothesis H1 : ~NM \/ ~RED.
(* Una base de datos es consistente o no es útil. *)
Hypothesis H2 : CONS \/ ~UTIL.

(* Si una base de datos está normalizada y es útil,
   entonces es consistente y no presenta redundancia
   de información. *)
Theorem ej9 : (NM /\ UTIL) -> (CONS /\ ~RED).
Proof.
  intros.
  elim H.
  intros.
  split.
    + elim H2.
        * intros.
          assumption.
        * intros.
          absurd UTIL; assumption.
    + elim H1.
        * intros.
          absurd NM; assumption.
        * intros.
          assumption.
Qed.

End Traducciones9.

Section Traducciones12.

Require Import Classical.
Check classic.

(* Ej 12 *)
(* Definiciones *)
Variable PF:Prop. (* el paciente tiene fiebre *)
Variable PA:Prop. (* el paciente tiene piel amarillenta *)
Variable PH:Prop. (* el paciente tiene hepatitis *)
Variable PR:Prop. (* el paciente tiene rubeola *)

(* Si el paciente tiene fiebre o el paciente tiene la piel
   amarillenta, entonces tiene hepatitis o rubeola. *)
Hypothesis Regla1: (PF \/ PA) -> (PH \/ PR).
(* El paciente no tiene rubeola o tiene fiebre. *)
Hypothesis Regla2: (~PR) \/ PF.
(* Si el paciente tiene hepatitis, pero no la rubeola,
   entonces tiene la piel amarillenta. *)
Hypothesis Regla3: (PH /\ (~PR)) -> PA.

Lemma MT: forall P Q:Prop, ((P -> Q) /\ ~Q) -> ~P.
Proof.
  unfold not.
  intros.
  elim H.
  intros.
  absurd Q.
    + assumption.
    + exact (H1 H0).
Qed.

Theorem ej12: (~PA /\ PF) -> PR.
Proof.
  intros.
  elim H.
  intros.

  (* El paciente no puede tener nunca hepatitis
     pero no rubeola, o tendría la piel amarilla. *)
  cut (~(PH /\ (~PR))).
    + intros.
      apply demorgan_1 in H2.
      elim H2.
        * intro.
          elim Regla1.
            - intros.
              absurd PH; assumption.
            - intros.
              assumption.
            - left.
              assumption.
        * intros.
          apply elim_dobleneg in H3.
          assumption.
    + apply (MT (PH /\ (~PR)) PA).
      split; assumption.
Qed.

End Traducciones12.
