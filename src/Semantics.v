Require Import Ast.
Require Import Store.
Require Import Entities.

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

| E_Fld : forall h f f' t t' name addr,
    t' = Frame.alloc_temp f ->
    v_addr addr = Frame.get f (TempId t) ->
    f' = Frame.set f (TempId t') (Heap.get_field h addr name) ->
    h / f / expr_field (expr_temp t) name ==> h / f' / expr_temp t'

| E_Asn_Field : forall h h' f f' t t' t'' name addr,
    t'' = Frame.alloc_temp f ->
    v_addr addr = Frame.get f (TempId t) ->
    f' = Frame.set f (TempId t'') (Heap.get_field h addr name) ->
    h' = Heap.set_field h addr name (Frame.get f (TempId t')) ->

    h / f / expr_assign_field (expr_temp t) name (expr_temp t') ==>
    h' / f' / expr_temp t''

| E_Seq1 : forall h f f' e1 e1' e2,
    h / f / e1 ==> h / f' / e1' ->
    h / f / expr_seq e1 e2 ==> h / f' / expr_seq e1' e2

| E_Recover1 : forall h f f' e e',
    h / f / e ==> h / f' / e' ->
    h / f / expr_recover e ==> h / f' / expr_recover e'

| E_Asn_Local1 : forall h f f' name e e',
    h / f / e ==> h / f' / e' ->
    h / f / expr_assign_local name e ==> h / f' / expr_assign_local name e'

| E_Fld1 : forall h f f' e e' name,
    h / f / e ==> h / f' / e' ->
    h / f / expr_field e name ==> h / f' / expr_field e' name

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
