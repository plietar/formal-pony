Require Import ch2o.prelude.base.
Require Import Coq.Lists.List.

Theorem pigeonhole {X Ys: Type} `{Size (list X)} `{Size Ys} `{ElemOf X Ys} : forall (xs: list X) (ys: Ys),
  base.NoDup xs ->
  Forall (λ x, x ∈ ys) xs ->
  size xs ≤ size ys.
Proof.

Admitted.
