(*******************************************************************
 * Este archivo especifica las acciones
 * (Como transformadores de estado)
 ******************************************************************)

Require Export State.

Section Actions.

Inductive Action :=
  | read : vadd -> Action
  | write : vadd -> value -> Action
  | chmod : Action
.

Definition Pre := state -> Action -> Prop.
Definition Post := state -> Action -> state -> Prop.


End Actions.