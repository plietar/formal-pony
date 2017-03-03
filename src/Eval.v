Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Require Import Ast.

Inductive value : expr -> Prop :=
| v_null : value expr_null
| v_term : forall n, value (expr_term n)
.

Reserved Notation "t1 '==>' t2" (at level 40).
Inductive step : expr -> expr -> Prop :=
| E_Seq : forall v e,
        value v ->
        expr_seq v e ==> e
| E_Recover : forall v,
        value v ->
        expr_recover v ==> v
where "e1 '==>' e2" := (step e1 e2).

Hint Constructors step.
