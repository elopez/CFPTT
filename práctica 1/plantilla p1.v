(* Practica 1 *)

Section P1.
Variables A B C:Prop.

(* Ej 1.1 *)
Theorem e11: A->A.
Proof.
...
Qed.

(* Ej 1.2 *)
Theorem e12: A->B->A.
Proof.
...
Qed.

(* Ej 1.3 *)
Theorem e13: (A->(B->C))->(A->B)->(A->C).
Proof.
...
Qed.

(*Ej 2.1 *)
Theorem e21: (A->B)->(B->C)->A->C.
Proof.
...
Qed.

(*Ej 2.2 *)
Theorem e22: (A->B->C)->B->A->C.
Proof.
...
Qed.

(*Ej 3.1 *)
Theorem e31_1: A->A->A.
Proof.
...
Qed.

Theorem e31_2: A->A->A.
Proof.
...
Qed.

(* Ej 3.2 *)
Theorem e32_1: (A->B->C)->A->(A->C)->B->C.
Proof.
...
Qed.

Theorem e32_2: (A->B->C)->A->(A->C)->B->C.
Proof.
...
Qed.

(* Ej 4.1 *)
Theorem e41: A -> ~~A.
Proof.
...
Qed.

(* Ej 4.2 *)
Theorem e42: A -> B -> (A /\ B).
Proof.
...
Qed.

(* Ej 4.3 *)
Theorem e43: (A->B->C) -> (A/\B->C).
Proof.
...
Qed.

(* Ej 4.4 *)
Theorem e44: A->(A\/B).
Proof.
...
Qed.

(* Ej 4.5 *)
Theorem e45: B->(A\/B).
Proof.
...
Qed.

(* Ej 4.6 *)
Theorem e46: (A \/ B) -> (B \/ A).
Proof.
...
Qed.

(* Ej 4.7 *)
Theorem e47: (A->C)->(B->C)->A\/B->C.
Proof.
...
Qed.

(* Ej 4.8 *)
Theorem e48: False->A.
Proof.
...
Qed.

(* Ej 5.1 *)
Theorem e51: (A->B)-> ~B-> ~A.
Proof.
...
Qed.

(* Ej 5.2 *)
Theorem e52: ~(A/\~A).
Proof.
...
Qed.

(* Ej 5.3 *)
Theorem e53: (A->B)-> ~(A/\~B).
Proof.
...
Qed.

(* Ej 5.4 *)
Theorem e54: (A/\B)->~(A->~B).
Proof.
...
Qed.

(* Ej 5.5 *)
Theorem e55: (~A /\ ~~A) -> False.
Proof.
...
Qed.

(* Ej 6.1 *)
Theorem e61: (A\/B) -> ~(~A/\~B).
Proof.
...
Qed.

(* Ej 6.2 *)
Theorem e62: A\/B <-> B\/A.
Proof.
...
Qed.

(* Ej 6.3 *)
Theorem e63: A\/B -> ((A->B)->B).
Proof.
...
Qed.

End P1.


Section Logica_Clasica.
Variables A B C: Prop.

(* Ej 7.1 *)
Theorem e71: A \/ ~A -> ~~A->A.
Proof.
...
Qed.

(* Ej 7.2 *)
Theorem e72: A\/~A -> ((A->B) \/ (B->A)).
Proof.
...
Qed.

(* Ej 7.3 *)
Theorem e73: (A \/ ~A) -> ~(A /\ B) -> ~A \/ ~B.
Proof.
...
Qed.


Require Import Classical.
Check classic.

(* Ej 8.1 *)
Theorem e81: forall A:Prop, ~~A->A.
Proof.
...
Qed.

(* Ej 8.2 *)
Theorem e82: forall A B:Prop, (A->B)\/(B ->A).
Proof.
...
Qed.

(* Ej 8.3 *)
Theorem e83: forall A B:Prop, ~(A/\B)-> ~A \/ ~B.
Proof.
...
Qed.

End Logica_Clasica.


Section Traducciones.

(* Ej 9 *)
(* Definiciones *)
Variable NM RED CONS UTIL : Prop.

Hypothesis H1 : ...
Hypothesis H2 : ...

Theorem ej9 : ...
Proof.
...
Qed.


(* Ej 10 y 11 *)
(* Formalizaciones a cargo del estudiante *)


(* Ej 12 *)
(* Definiciones *)
Variable PF:Prop. (* el paciente tiene fiebre *)
Variable PA:Prop. (* el paciente tiene piel amarillenta *)
Variable PH:Prop. (* el paciente tiene hepatitis *)
Variable PR:Prop. (* el paciente tiene rubeola *)

Hypothesis Regla1: ...
Hypothesis Regla2: ...
Hypothesis Regla3: ...


Theorem ej12: (~PA /\ PF) -> ...

End Traducciones.
