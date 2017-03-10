Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import ch2o.prelude.prelude.

Inductive expr : Type :=
| expr_temp : N -> expr
| expr_seq : expr -> expr -> expr
| expr_recover : expr -> expr
| expr_local : string -> expr
| expr_assign_local : string -> expr -> expr
| expr_field : expr -> string -> expr
| expr_assign_field : expr -> string -> expr -> expr
| expr_call : expr -> string -> list_expr  -> expr
| expr_ctor : string -> string -> list_expr -> expr
with list_expr : Type :=
| list_expr_nil : list_expr
| list_expr_cons : expr -> list_expr -> list_expr
.

Fixpoint list_expr_coerce (l: list expr) := match l with
| nil => list_expr_nil
| (h :: t) => list_expr_cons h (list_expr_coerce t)
end.

Fixpoint list_expr_uncoerce (l: list_expr) := match l with
| list_expr_nil => nil
| list_expr_cons h t => h :: (list_expr_uncoerce t)
end.

Inductive expr_hole : Type :=
| expr_hole_id : expr_hole
| expr_hole_seq : expr_hole -> expr -> expr_hole
| expr_hole_recover : expr_hole -> expr_hole
| expr_hole_assign_local : string -> expr_hole -> expr_hole
| expr_hole_field : expr_hole -> string -> expr_hole
| expr_hole_assign_field1 : expr -> string -> expr_hole -> expr_hole
| expr_hole_assign_field2 : expr_hole -> string -> N -> expr_hole
| expr_hole_call1 : expr -> string -> list N -> expr_hole -> list_expr -> expr_hole
| expr_hole_call2 : expr_hole -> string -> list N -> expr_hole
| expr_hole_ctor : string -> string -> list N -> expr_hole -> list_expr -> expr_hole
.

Inductive make_hole : expr -> expr -> expr_hole -> Prop :=
| make_hole_id: forall e, make_hole e e expr_hole_id

| make_hole_seq: forall e1 e2 eh e1', make_hole e1 eh e1' ->
    make_hole (expr_seq e1 e2) eh (expr_hole_seq e1' e2)

| make_hole_recover: forall e1 eh e1', make_hole e1 eh e1' ->
    make_hole (expr_recover e1) eh (expr_hole_recover e1')

| make_hole_assign_local: forall n e1 eh e1', make_hole e1 eh e1' ->
    make_hole (expr_assign_local n e1) eh (expr_hole_assign_local n e1')

| make_hole_field: forall e1 n eh e1', make_hole e1 eh e1' ->
    make_hole (expr_field e1 n) eh (expr_hole_field e1' n)

| make_hole_assign_field1: forall e1 n e2 eh e2', make_hole e2 eh e2' ->
    make_hole (expr_assign_field e1 n e2) eh (expr_hole_assign_field1 e1 n e2')

| make_hole_assign_field2: forall e1 n t eh e1', make_hole e1 eh e1' ->
    make_hole (expr_assign_field e1 n (expr_temp t)) eh (expr_hole_assign_field2 e1' n t)

| make_hole_call1: forall e eh e' e0 n ts es,
    make_hole e eh e' ->
    make_hole (expr_call e0 n (list_expr_coerce (fmap expr_temp ts ++ (e :: list_expr_uncoerce es)))) eh (expr_hole_call1 e0 n ts e' es)

| make_hole_call2: forall e0 eh e0' n ts,
    make_hole e0 eh e0' ->
    make_hole (expr_call e0 n (list_expr_coerce (fmap expr_temp ts))) eh (expr_hole_call2 e0' n ts)

| make_hole_ctor: forall e eh e' n m ts es,
    make_hole e eh e' ->
    make_hole (expr_ctor n m (list_expr_coerce (fmap expr_temp ts ++ (e :: list_expr_uncoerce es)))) eh (expr_hole_ctor n m ts e' es).

Fixpoint fill_hole (cps: expr_hole) (filler: expr) : expr :=
  match cps with
  | expr_hole_id => filler
  | expr_hole_seq cps' e2 => expr_seq (fill_hole cps' filler) e2
  | expr_hole_recover cps' => expr_recover (fill_hole cps' filler)
  | expr_hole_assign_local name cps' => expr_assign_local name (fill_hole cps' filler)
  | expr_hole_field cps' name => expr_field (fill_hole cps' filler) name
  | expr_hole_assign_field1 e1 name cps' => expr_assign_field e1 name (fill_hole cps' filler)
  | expr_hole_assign_field2 cps' name t2 => expr_assign_field (fill_hole cps' filler) name (expr_temp t2)
  | expr_hole_call1 e0 name ts cps' es => expr_call e0 name (list_expr_coerce ((fmap expr_temp ts) ++ (fill_hole cps' filler) :: list_expr_uncoerce es))
  | expr_hole_call2 cps' name ts => expr_call (fill_hole cps' filler) name (list_expr_coerce (fmap expr_temp ts))
  | expr_hole_ctor n m ts cps' es => expr_ctor n m (list_expr_coerce ((fmap expr_temp ts) ++ (fill_hole cps' filler) :: list_expr_uncoerce es))
  end.

Fixpoint compose_hole (a: expr_hole) (b: expr_hole) : expr_hole :=
  match a with
  | expr_hole_id => b
  | expr_hole_seq cps' e2 => expr_hole_seq (compose_hole cps' b) e2
  | expr_hole_recover cps' => expr_hole_recover (compose_hole cps' b)
  | expr_hole_assign_local name cps' => expr_hole_assign_local name (compose_hole cps' b)
  | expr_hole_field cps' name => expr_hole_field (compose_hole cps' b) name
  | expr_hole_assign_field1 e1 name cps' => expr_hole_assign_field1 e1 name (compose_hole cps' b)
  | expr_hole_assign_field2 cps' name t2 => expr_hole_assign_field2 (compose_hole cps' b) name t2
  | expr_hole_call1 e0 name ts cps' es => expr_hole_call1 e0 name ts (compose_hole cps' b) es
  | expr_hole_call2 cps' name ts => expr_hole_call2 (compose_hole cps' b) name ts
  | expr_hole_ctor n m ts cps' es => expr_hole_ctor n m ts (compose_hole cps' b) es
  end.

Inductive item : Type :=
| item_field : string -> item
| item_ctor : string -> list string -> expr -> item
| item_func : string -> list string -> expr -> item
| item_behv : string -> list string -> expr -> item
.

Inductive item_stub : Type :=
| item_stub_ctor : string -> list string -> item_stub
| item_stub_func : string -> list string -> item_stub
| item_stub_behv : string -> list string -> item_stub
.

Inductive def : Type :=
| def_class : string -> list item -> def
| def_actor : string -> list item -> def
| def_trait : string -> list item_stub -> def
| def_iface : string -> list item_stub -> def
.

Definition program : Type := list def.


(*
Require Import Coq.Program.Equality.

Lemma id_fill: forall e, fill_hole expr_hole_id e = e.
Proof. auto. Qed.

Lemma id_compose_left: forall h1, compose_hole expr_hole_id h1 = h1.
Proof. auto. Qed.

Lemma id_compose_right: forall h1, compose_hole h1 expr_hole_id = h1.
Proof.
induction 0.
auto.
simpl. rewrite IHh1. reflexivity.
simpl. rewrite IHh1. reflexivity.
simpl. rewrite IHh1. reflexivity.
simpl. rewrite IHh1. reflexivity.
simpl. rewrite IHh1. reflexivity.
simpl. rewrite IHh1. reflexivity.
simpl. rewrite IHh1. reflexivity.
Qed.

Lemma composition: forall h1 h2 e,
  fill_hole h2 (fill_hole h1 e) = fill_hole (compose_hole h2 h1) e.
Proof.
intros.
dependent induction h1.
rewrite id_compose_right.
rewrite id_fill.
reflexivity.

dependent induction h2.
rewrite id_fill. rewrite id_compose_left. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.

dependent induction h2.
rewrite id_fill. rewrite id_compose_left. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.

dependent induction h2.
rewrite id_fill. rewrite id_compose_left. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.

dependent induction h2.
rewrite id_fill. rewrite id_compose_left. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.

dependent induction h2.
rewrite id_fill. rewrite id_compose_left. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.

dependent induction h2.
rewrite id_fill. rewrite id_compose_left. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.

dependent induction h2.
rewrite id_fill. rewrite id_compose_left. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
simpl. rewrite <- IHh2. simpl. reflexivity.
Qed.
*)

