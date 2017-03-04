Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.String.

Require Import Ast.
Require Import Store.

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
| v_addr: nat -> value.

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

Reserved Notation "f1 / e1 '==>' f2 / e2"
  (at level 40, e1 at level 39, f2 at level 39).

Inductive step : frame * expr -> frame * expr -> Prop :=
| E_Seq : forall f t e,
    f / expr_seq (expr_temp t) e ==> f / e

| E_Recover : forall f t,
    f / expr_recover (expr_temp t) ==> f / (expr_temp t)

| E_Local : forall f t f' name,
    t = Frame.alloc_temp f ->
    f' = Frame.set f (TempId t) (Frame.get f (SourceId name)) ->
    f / expr_local name ==> f' / expr_temp t

| E_Asn_Local : forall f f' t t' name,
    t' = Frame.alloc_temp f ->
    f' = Frame.set (Frame.set f (TempId t') (Frame.get f (SourceId name)))
              (SourceId name) (Frame.get f (TempId t)) ->
    f / expr_assign_local name (expr_temp t) ==> f' / expr_temp t'

| E_Seq1 : forall f f' e1 e1' e2,
    f / e1 ==> f' / e1' ->
    f / expr_seq e1 e2 ==> f' / expr_seq e1' e2

| E_Recover1 : forall f f' e e',
    f / e ==> f' / e' ->
    f / expr_recover e ==> f' / expr_recover e'

| E_Asn_Local1 : forall f f' name e e',
    f / e ==> f' / e' ->
    f / expr_assign_local name e ==> f' / expr_assign_local name e'

where "f1 / e1 '==>' f2 / e2" := (step (f1,e1) (f2,e2)).

Reserved Notation "f1 / e1 '==>*' f2 / e2"
  (at level 40, e1 at level 39, f2 at level 39).

Inductive multistep : frame * expr -> frame * expr -> Prop :=
| multi_refl : forall f e, multistep (f, e) (f, e)

| multi_trans : forall f1 e1 f2 e2 f3 e3,
    f1 / e1 ==> f2 / e2 ->
    f2 / e2 ==>* f3 / e3 ->
    f1 / e1 ==>* f3 / e3
where "f1 / e1 '==>*' f2 / e2" := (multistep (f1, e1) (f2, e2)).

Theorem multi_one : forall f1 e1 f2 e2,
  f1 / e1 ==> f2 / e2 ->
  f1 / e1 ==>* f2 / e2.
Proof.
intros.
apply multi_trans with (f2 := f2) (e2 := e2).
exact H.
apply multi_refl.
Qed.

Theorem multi_concat : forall f1 e1 f2 e2 f3 e3,
  f1 / e1 ==>* f2 / e2 ->
  f2 / e2 ==>* f3 / e3 ->
  f1 / e1 ==>* f3 / e3.
Proof.
  intros.
  generalize dependent f3.
  generalize dependent e3.
  induction H.
  + intros. exact H0.
  + intros.
    apply multi_trans with (f2 := f3) (e2 := e3).
    exact H.
    apply IHmultistep.
    exact H1.
Qed.

Lemma E_RecoverN : forall f f' e e',
    f / e ==>* f' / e' ->
    f / expr_recover e ==>* f' / expr_recover e'.
Admitted.

Lemma E_SeqN : forall f f' e1 e1' e2,
    f / e1 ==>* f' / e1' ->
    f / expr_seq e1 e2 ==>* f' / expr_seq e1' e2.
Admitted.

Lemma E_Asn_LocalN : forall f f' name e e',
    f / e ==>* f' / e' ->
    f / expr_assign_local name e ==>* f' / expr_assign_local name e'.
Admitted.
