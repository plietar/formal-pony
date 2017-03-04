Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.String.

Require Import Ast.
Require Import Store.

Definition addr := nat.
Module addr_eq.
  Definition t := addr.
  Definition eqb x y : bool := beq_nat x y.
End addr_eq.

Definition object := string.
Definition actor := string.

Module heap_default.
  Definition t : Type := actor + object.
  Definition default : t := inl EmptyString.
End heap_default.

Module Heap.
  Include Store addr_eq heap_default.
  Definition alloc_addr (st: store) : addr :=
    List.length st.
End Heap.

Definition heap := Heap.store.

Inductive local_id : Type :=
| SourceId: string -> local_id
| TempId: nat -> local_id.

Module local_id_eq.
  Definition t := local_id.
  Definition eqb x y : bool :=
    match x, y with
    | SourceId x', SourceId y' => if string_dec x' y' then true else false
    | TempId x', TempId y' => beq_nat x' y'
    | _, _ => false
    end.
End local_id_eq.

Inductive value : Type :=
| v_null: value
| v_addr: addr -> value.

Module value_default.
  Definition t := value.
  Definition default := v_null.
End value_default.

Module Frame.
  Include Store local_id_eq value_default.
  Definition alloc_temp (st: store) : nat :=
    List.length st.
End Frame.

Definition frame := Frame.store.

Reserved Notation "h1 / f1 / e1 '==>' h2 / f2 / e2"
  (at level 40, e1 at level 39, h2 at level 39, f1 at level 38, f2 at level 38).

Inductive step : heap * frame * expr -> heap * frame * expr -> Prop :=
| E_Seq : forall h f t e,
    h / f / expr_seq (expr_temp t) e ==> h / f / e

| E_Recover : forall h f t,
    h / f / expr_recover (expr_temp t) ==> h / f / (expr_temp t)

| E_Local : forall h f t f' name,
    t = Frame.alloc_temp f ->
    f' = Frame.set f (TempId t) (Frame.get f (SourceId name)) ->
    h / f / expr_local name ==> h / f' / expr_temp t

| E_Asn_Local : forall h f f' t t' name,
    t' = Frame.alloc_temp f ->
    f' = Frame.set (Frame.set f (TempId t') (Frame.get f (SourceId name)))
              (SourceId name) (Frame.get f (TempId t)) ->
    h / f / expr_assign_local name (expr_temp t) ==> h / f' / expr_temp t'

| E_Seq1 : forall h f f' e1 e1' e2,
    h / f / e1 ==> h / f' / e1' ->
    h / f / expr_seq e1 e2 ==> h / f' / expr_seq e1' e2

| E_Recover1 : forall h f f' e e',
    h / f / e ==> h / f' / e' ->
    h / f / expr_recover e ==> h / f' / expr_recover e'

| E_Asn_Local1 : forall h f f' name e e',
    h / f / e ==> h / f' / e' ->
    h / f / expr_assign_local name e ==> h / f' / expr_assign_local name e'

where "h1 / f1 / e1 '==>' h2 / f2 / e2" := (step (h1,f1,e1) (h2,f2,e2)).

Reserved Notation "h1 / f1 / e1 '==>*' h2 / f2 / e2"
  (at level 40, e1 at level 39, h2 at level 39, f1 at level 38, f2 at level 38).

Inductive multistep : heap * frame * expr -> heap * frame * expr -> Prop :=
| multi_refl : forall h f e, multistep (h, f, e) (h, f, e)

| multi_trans : forall h1 f1 e1 h2 f2 e2 h3 f3 e3,
    h1 / f1 / e1 ==> h2 / f2 / e2 ->
    h2 / f2 / e2 ==>* h3 / f3 / e3 ->
    h1 / f1 / e1 ==>* h3 / f3 / e3
where "h1 / f1 / e1 '==>*' h2 / f2 / e2" := (multistep (h1, f1, e1) (h2, f2, e2)).

Theorem multi_one : forall h1 f1 e1 h2 f2 e2,
  h1 / f1 / e1 ==> h2 / f2 / e2 ->
  h1 / f1 / e1 ==>* h2 / f2 / e2.
Proof.
intros.
apply multi_trans with (h2 := h2) (f2 := f2) (e2 := e2).
exact H.
apply multi_refl.
Qed.

Theorem multi_concat : forall h1 f1 e1 h2 f2 e2 h3 f3 e3,
  h1 / f1 / e1 ==>* h2 / f2 / e2 ->
  h2 / f2 / e2 ==>* h3 / f3 / e3 ->
  h1 / f1 / e1 ==>* h3 / f3 / e3.
Proof.
  intros.
  generalize dependent h3.
  generalize dependent f3.
  generalize dependent e3.
  induction H.
  + intros. exact H0.
  + intros.
    apply multi_trans with (h2 := h3) (f2 := f3) (e2 := e3).
    exact H.
    apply IHmultistep.
    exact H1.
Qed.

Lemma E_RecoverN : forall h h' f f' e e',
    h / f / e ==>* h' / f' / e' ->
    h / f / expr_recover e ==>* h' / f' / expr_recover e'.
Admitted.

Lemma E_SeqN : forall h h' f f' e1 e1' e2,
    h / f / e1 ==>* h' / f' / e1' ->
    h / f / expr_seq e1 e2 ==>* h' / f' / expr_seq e1' e2.
Admitted.

Lemma E_Asn_LocalN : forall h h' f f' name e e',
    h / f / e ==>* h' / f' / e' ->
    h / f / expr_assign_local name e ==>* h' / f' / expr_assign_local name e'.
Admitted.
