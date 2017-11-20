(* Ejercicio 5.5 *)
Section ej55.

(* Ejercicio 5.5.1 *)
Definition Var := nat.

Inductive BoolExpr :=
  | V (x: nat)  : BoolExpr
  | B (b: bool) : BoolExpr
  | AND (e1 e2: BoolExpr) : BoolExpr
  | NOT (e: BoolExpr) : BoolExpr.

Notation "x /\ y" := (AND x y) (at level 80, right associativity).
Notation "~ x" := (NOT x) (at level 75, right associativity).
Notation "¿ x" := (V x) (at level 70, right associativity).

(* Ejercicio 5.5.2 *)
Definition Valor := bool.
Definition Memoria : Set := Var -> Valor.

Definition lookup (m: Memoria) (v: Var) : Valor := m v.

Inductive BEval (m: Memoria) : BoolExpr -> Valor -> Prop :=
  | evar (v: Var)            : BEval m (¿ v) (lookup m v)
  | eboolt                   : BEval m (B true) true
  | eboolf                   : BEval m (B false) false
  | eandl (e1 e2: BoolExpr)  : BEval m e1 false -> BEval m (e1 /\ e2) false
  | eandr (e1 e2: BoolExpr)  : BEval m e2 false -> BEval m (e1 /\ e2) false
  | eandrl (e1 e2: BoolExpr) : BEval m e1 true -> BEval m e2 true -> BEval m (e1 /\ e2) true
  | enott (e: BoolExpr)      : BEval m e true -> BEval m (~ e) false
  | enotf (e: BoolExpr)      : BEval m e false -> BEval m (~ e) true.

(* Ejercicio 5.5.3.a *)
Theorem true_not_false : forall m: Memoria, ~BEval m (B true) false.
Proof.
unfold not.
intros.
inversion H.
Qed.

(* Ejercicio 5.5.3.b *)
Theorem e1_true_w_and : forall (m: Memoria) (e1 e2: BoolExpr) (w: Valor), BEval m e1 true -> BEval m e2 w -> BEval m (e1 /\ e2) w.
Proof.
intros.
destruct w.
apply (eandrl m e1 e2 H H0).
apply (eandr m e1 e2 H0).
Qed.

(* Ejercicio 5.5.3.c *)
Theorem e1_e2_w1_w2_eq : forall (m: Memoria) (e: BoolExpr) (w1 w2: Valor), BEval m e w1 -> BEval m e w2 -> w1 = w2.
Proof.
induction e; intros; auto.
  * inversion H.
    inversion H0.
    reflexivity.
  * inversion H;
    rewrite <- H2 in H0;
    inversion H0;
    reflexivity.
  * inversion H;
    inversion H0;
    auto.
  * inversion H;
    inversion H0;
    auto.
Qed.

(* Ejercicio 5.5.3.d *)
Theorem e1_false_then_not_and : forall (m: Memoria) (e1 e2: BoolExpr), BEval m e1 false -> ~BEval m (e1 /\ e2) true.
Proof.
unfold not.
intros.
inversion H0.
pose (e1_e2_w1_w2_eq m e1 false true H H3).
discriminate.
Qed.


(* Ejercicio 5.5.4 *)
Require Import Coq.Bool.Bool.
Fixpoint beval (m: Memoria) (e: BoolExpr) : Valor :=
    match e with
        | V x => lookup m x
        | B v => v
        | AND e1 e2 => (beval m e1) && (beval m e2)
        | NOT e => negb (beval m e)
    end.

(* Ejercicio 5.5.5 *)
Theorem beval_correct : forall (m: Memoria) (e: BoolExpr), BEval m e (beval m e).
Proof.
intros.
induction e; simpl.
  * constructor.
  * case b; constructor.
  * case (beval m e1), (beval m e2); simpl.
    + apply (eandrl m e1 e2 IHe1 IHe2).
    + apply (eandr m e1 e2 IHe2).
    + apply (eandl m e1 e2 IHe1).
    + apply (eandl m e1 e2 IHe1).
  * destruct (beval m e); simpl.
    + apply (enott m e); assumption.
    + apply (enotf m e); assumption.
Qed.

End ej55.


(* Ejercicio 5.6 y 5.7 *)
Section ej56_ej57.

(* notación BoolExpr *)
Notation "x /\ y" := (AND x y) (at level 80, right associativity).
Notation "~ x" := (NOT x) (at level 75, right associativity).
Notation "* x" := (V x) (at level 70, right associativity).
Notation "'TRUE'" := (B true).
Notation "'FALSE'" := (B false).

(* Ejercicio 5.6.1 *)
Inductive Instr :=
  | NOOP : Instr
  | ASSIGN (x: nat) (y: BoolExpr) : Instr
  | IFS (b: BoolExpr) (t f: Instr) : Instr
  | WHILE (e: BoolExpr) (c: Instr) : Instr
  | REPEAT (n: nat) (c: Instr) : Instr
  | BEGIN (l: LInstr)
with
  LInstr :=
  | EMPTY : LInstr
  | CONS (x: Instr) (y: LInstr).

(* Ejercicio 5.6.2 + extras *)
Notation "'SKIP'" := NOOP.
Notation "x <- y" := (ASSIGN x y) (at level 90, right associativity).
Notation "'IF?' b 'THEN' x 'ELSE' y" := (IFS b x y) (at level 80, right associativity).
Notation "'WHILE' b 'DO' x" := (WHILE b x) (at level 80, right associativity).
Notation "'BEGIN' l 'END'" := (BEGIN l) (at level 90, right associativity).
Notation "x ; y" := (CONS x y) (at level 100, right associativity).
Notation "x ; " := (CONS x EMPTY) (at level 100, right associativity).

(* Ejercicio 5.6.2.a *)
Definition PP (v1 v2: Var) := BEGIN 
    v1 <- TRUE; 
    v2 <- ~ *v1;
END.

(* Ejercicio 5.6.2.b *)
Definition swap (aux v1 v2: Var) := BEGIN 
    aux <- *v1;
    v1  <- *v2;
    v2  <- *aux;  
END.

(* Ejercicio 5.6.3 *)
Require Import Coq.Arith.EqNat.

Definition update (m: Memoria) (v: Var) (val: Valor) : Memoria :=
  fun x => if beq_nat x v then val else lookup m x.

(* Ejercicio 5.6.4 *)
Theorem update_works : forall (m: Memoria) (v: Var) (val: Valor), lookup (update m v val) v = val.
Proof.
intros.
unfold lookup, update.
rewrite <- (beq_nat_refl v).
reflexivity.
Qed.

(* Ejercicio 5.6.5 *)
Theorem update_other_works : forall (m: Memoria) (v v': Var) (val: Valor), v <> v' -> lookup (update m v val) v' = lookup m v'.
Proof.
intros.
unfold lookup, update.
apply (beq_nat_false_iff v v') in H.
rewrite <- PeanoNat.Nat.eqb_sym.
rewrite H.
reflexivity.
Qed.


(* Ejercicio 5.7.1 *)
Inductive Execute (m: Memoria) : Instr -> Memoria -> Prop :=
  | xAss (v: Var) (be: BoolExpr) (w: Valor)               : BEval m be w -> Execute m (v <- be) (update m v w)
  | xSkip                                                 : Execute m SKIP m
  | xIFthen (be: BoolExpr) (p1 p2: Instr) (m': Memoria)   : BEval m be true -> Execute m p1 m' -> Execute m (IF? be THEN p1 ELSE p2) m'
  | xIFelse (be: BoolExpr) (p1 p2: Instr) (m': Memoria)   : BEval m be false -> Execute m p2 m' -> Execute m (IF? be THEN p1 ELSE p2) m'
  | xWhileTrue (be: BoolExpr) (p: Instr) (m1 m2: Memoria) : BEval m be true -> Execute m p m1 -> Execute m1 (WHILE be DO p) m2 -> Execute m (WHILE be DO p) m2
  | xWhileFalse (be: BoolExpr) (p: Instr)                 : BEval m be false -> Execute m (WHILE be DO p) m
  | xRepeat0 (p: Instr)                                   : Execute m (REPEAT 0 p) m
  | xRepeatS (p: Instr) (m1 m2: Memoria) (n: nat)         : Execute m p m1 -> Execute m1 (REPEAT n p) m2 -> Execute m (REPEAT (S n) p) m2
  | xBeginEnd (pl: LInstr) (m': Memoria)                  : ExecuteL m pl m' -> Execute m (BEGIN pl END) m'
with ExecuteL (m: Memoria) : LInstr -> Memoria -> Prop :=
  | xEmptyblock                                    : ExecuteL m EMPTY m
  | xNext (p: Instr) (pl: LInstr) (m1 m2: Memoria) : Execute m p m1 -> ExecuteL m1 pl m2 ->ExecuteL m (p; pl) m2.

(* Ejercicio 5.7.2 *)
Theorem if_reversed : forall (m m': Memoria) (e1 e2: Instr), Execute m (IF? ~ FALSE THEN e1 ELSE e2) m' -> Execute m (IF? FALSE THEN e2 ELSE e1) m'.
Proof.
intros.
inversion_clear H.
  * apply xIFelse; auto; constructor.
  * inversion_clear H0.
    inversion_clear H.
Qed.

(* Ejercicio 5.7.3 *)
Lemma bool_contradict : forall (c: bool) (m: Memoria), ~BEval m (~ B c) c.
Proof.
unfold not.
induction c; intros; inversion_clear H; inversion_clear H0.
Qed.

Theorem gen_if_reversed : forall (c: bool) (m m': Memoria) (e1 e2: Instr), Execute m (IF? ~ (B c) THEN e1 ELSE e2) m' -> Execute m (IF? (B c) THEN e2 ELSE e1) m'.
Proof.
intros.
induction c; intros.
inversion_clear H.
  * apply (bool_contradict true m) in H0; contradiction.
  * apply xIFthen; auto; constructor.
  * apply xIFelse; auto.
    - constructor.
    - inversion_clear H; auto.
      apply (bool_contradict false m) in H0; contradiction.
Qed.

(* Ejercicio 5.7.4 *)
Theorem empty_false : forall (m m': Memoria) (p: Instr), Execute m (WHILE FALSE DO p) m' -> m = m'.
Proof.
intros.
inversion H.
  * inversion H2.
  * reflexivity.
Qed.

(* Ejercicio 5.7.5 *)
Theorem expand_while_eq : forall (m m': Memoria) (c: BoolExpr) (p: Instr), ExecuteL m ((IF? c THEN p ELSE SKIP); WHILE c DO p;) m' -> Execute m (WHILE c DO p) m'.
Proof.
intros.
inversion_clear H.
inversion_clear H1.
inversion H2.
rewrite -> H3 in H.
inversion_clear H0.
  * apply (xWhileTrue m c p m1 m' H1 H4 H).
  * inversion H4.
    assumption.
Qed.

(* Ejercicio 5.7.6 *)
Theorem repeat_seq : forall (m m': Memoria) (n: nat) (i: Instr), ExecuteL m (i; REPEAT n i;) m' -> Execute m (REPEAT (S n) i) m'.
Proof.
intros.
inversion_clear H.
inversion_clear H1.
inversion H2.
rewrite -> H3 in H.
apply (xRepeatS m i m1 m' n H0 H).
Qed.

(* Ejercicio 5.7.7 *)
Theorem repeat_sum : forall (n1 n2: nat) (i: Instr) (m1 m2 m3: Memoria), Execute m1 (REPEAT n1 i) m2 -> Execute m2 (REPEAT n2 i) m3 -> Execute m1 (REPEAT (n1+n2) i) m3.
Proof.
induction n1; intros.
  * simpl.
    inversion H.
    assumption.
  * simpl.
    inversion H.
    pose (IHn1 n2 i m0 m2 m3 H5 H0).
    apply (xRepeatS m1 i m0 m3 (n1 + n2) H3 e).
Qed.

(* Ejercicio 5.7.8 *)
Theorem PProof : forall (v1 v2: Var) (m1 m2: Memoria), v1 <> v2 -> Execute m1 (PP v1 v2) m2 -> lookup m2 v1 = true /\ lookup m2 v2 = false.
Proof.
intros.
apply beq_nat_false_iff in H.
inversion_clear H0.
inversion_clear H1.
inversion_clear H2.
inversion H3.
rewrite <- H4.
clear H3.
clear H4.

inversion H0.
inversion H5.
rewrite <- H7 in H3.
clear H7.
clear H5.
clear H4.
clear H2.

inversion H1.
clear H2.
clear H5.
inversion H6.
  * rewrite <- H7 in H4.
    clear H7.
    clear H2.
    clear H5.
    clear H6.
    split; rewrite <- H3; simpl; unfold lookup, update.
      + rewrite -> H.
        unfold lookup.
        rewrite <- (beq_nat_refl v1).
        reflexivity.
      + unfold lookup, update.
        rewrite <- (beq_nat_refl v2).
        reflexivity.
  * rewrite <- H3 in H6.
    rewrite <- H7 in H6.
    inversion H6.
    inversion H9.
    unfold lookup, update in H12.
    rewrite <- (beq_nat_refl v1) in H12.
    discriminate.
Qed.

End ej56_ej57.