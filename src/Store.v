Require Import Coq.Structures.Equalities.
Require Import Coq.Lists.List.

Module Type HasDefault (Import T: Typ).
  Parameter Inline(30) default : t.
End HasDefault.

Module Type Default := Typ <+ HasDefault.

Module Type Eqb := Typ <+ HasEqb.

Module Store (K: Eqb) (V: Default).
  Definition store := list (K.t * V.t).
  Definition empty : store := nil.

  Fixpoint get (st: store) (k: K.t) : V.t :=
    match st with
    | nil => V.default
    | (k', v) :: tail =>
        if K.eqb k k'
        then v
        else get tail k
    end.

  Fixpoint set (st: store) (k: K.t) (v: V.t) : store :=
    match st with
    | nil => (k, v) :: nil
    | (k', v') :: tail =>
        if K.eqb k k'
        then (k, v) :: tail
        else (k', v') :: set tail k v
    end.
End Store.

