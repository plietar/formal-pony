(*
Require Import ch2o.prelude.base.
Require Import ch2o.prelude.option.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Strings.String.

Require Import Ast.
Require Import Store.
Require Import Entities.

Reserved Notation "LHS '⇒' RHS" (at level 40).

Open Scope string_scope.

Inductive step : heap * list frame * expr -> heap * list frame * expr -> Prop :=
| E_Seq : forall χ φ t e stack,
    (χ, φ :: stack, expr_seq (expr_temp t) e) ⇒ (χ, φ :: stack, e)

| E_Recover : forall χ φ t stack,
    (χ, φ :: stack, expr_recover (expr_temp t)) ⇒ (χ, φ :: stack, (expr_temp t))

| E_Local : forall χ φ t φ' x stack,
    not (elem_of t φ) ->
    φ' = <[t := φ !!! x]> φ ->
    (χ, φ :: stack, expr_local x) ⇒ (χ, φ' :: stack, expr_temp t)

| E_Asn_Local : forall χ φ φ' t t' x stack,
    not (elem_of t' φ) ->
    φ' = <[t' := φ !!! x]>(<[x := φ !!! t]>φ) ->
    (χ, φ :: stack, expr_assign_local x (expr_temp t)) ⇒ (χ, φ' :: stack, expr_temp t')

| E_Fld : forall χ φ φ' t t' f addr stack,
    not (elem_of t' φ) ->
    v_addr addr = φ !!! t ->
    φ' = <[t' := χ !!! (addr, f)]> φ ->
    (χ, φ :: stack, expr_field (expr_temp t) f) ⇒ (χ, φ' :: stack, expr_temp t')

| E_Asn_Fld : forall χ χ' φ φ' t t' t'' f addr stack,
    not (elem_of t'' φ) ->
    v_addr addr = φ !!! t ->
    φ' = <[t'' := χ !!! (addr, f)]>φ ->
    χ' = <[(addr, f) := φ !!! t']>χ ->

    (χ, φ :: stack, expr_assign_field (expr_temp t) f(expr_temp t')) ⇒
    (χ', φ' :: stack, expr_temp t'')

| E_Sync : forall χ φ φ' φ'' t hole e0 name stack addr,
    v_addr addr = φ !!! t ->

    φ'' = {|
      method := name;
      locals := <["this" := (v_addr addr)]>empty;
      hole := expr_hole_id
    |} ->

    φ' = {|
      method := φ.(method);
      locals := φ.(locals);
      hole := hole
    |} ->
    
    make_hole e0 (expr_call (expr_temp t) name nil) hole ->

    (χ, φ :: stack, e0) ⇒ (χ, φ'' :: φ' :: stack, (expr_local "this"))

| E_Return : forall χ φ φ' φ'' hole t t' stack,
    not (elem_of t' φ) ->

    φ'' = {|
      method := φ.(method);
      locals := <[t' := φ' !!! t]>φ.(locals);
      hole := expr_hole_id
    |} ->

    (χ, φ' :: φ :: stack, expr_temp t) ⇒
    (χ, φ'' :: stack, fill_hole φ.(hole) (expr_temp t'))

| E_Fld_Null : forall χ φ t f stack,
    φ !!! t = v_null ->

    (χ, φ :: stack, expr_field (expr_temp t) f) ⇒
    (χ, φ :: stack, expr_temp t)

| E_Asn_Fld_Null : forall χ φ t t' f stack,
    φ !!! t = v_null ->

    (χ, φ :: stack, expr_assign_field (expr_temp t) f (expr_temp t')) ⇒
    (χ, φ :: stack, expr_temp t)

| E_Call_Null : forall χ φ t name stack,
    φ !!! t = v_null ->

    (χ, φ :: stack, expr_call (expr_temp t) name nil) ⇒
    (χ, φ :: stack, expr_temp t)

| E_Seq1 : forall χ χ' φ φ' e1 e1' e2 stack,
    (χ, φ :: stack, e1) ⇒ (χ', φ' :: stack, e1') ->
    (χ, φ :: stack, expr_seq e1 e2) ⇒ (χ', φ' :: stack, expr_seq e1' e2)

| E_Recover1 : forall χ χ' φ φ' e e' stack,
    (χ, φ :: stack, e) ⇒ (χ', φ' :: stack, e') ->
    (χ, φ :: stack, expr_recover e) ⇒ (χ', φ' :: stack, expr_recover e')

| E_Asn_Local1 : forall χ χ' φ φ' name e e' stack,
    (χ, φ :: stack, e) ⇒ (χ', φ' :: stack, e') ->
    (χ, φ :: stack, expr_assign_local name e) ⇒ (χ', φ' :: stack, expr_assign_local name e')

| E_Fld1 : forall χ χ' φ φ' e e' name stack,
    (χ, φ :: stack, e) ⇒ (χ', φ' :: stack, e') ->
    (χ, φ :: stack, expr_field e name) ⇒ (χ', φ' :: stack, expr_field e' name)

| E_Asn_Fld1 : forall χ χ' φ φ' e1 e1' e2 name stack,
    (χ, φ :: stack, e1) ⇒ (χ', φ' :: stack, e1') ->

    (χ, φ :: stack, expr_assign_field e1 name e2) ⇒
    (χ', φ' :: stack, expr_assign_field e1' name e2)

| E_Asn_Fld2 : forall χ χ' φ φ' t1 e2 e2' name stack,
    (χ, φ :: stack, e2) ⇒ (χ', φ' :: stack, e2') ->

    (χ, φ :: stack, expr_assign_field (expr_temp t1) name e2) ⇒
    (χ', φ' :: stack, expr_assign_field (expr_temp t1) name e2')

where "LHS '⇒' RHS" := (step LHS RHS).

Reserved Notation "LHS '⇒*' RHS" (at level 40).

Inductive multistep : heap * list frame * expr -> heap * list frame * expr -> Prop :=
| multi_refl : forall h f e, (h, f, e) ⇒* (h, f, e)

| multi_trans : forall h1 f1 e1 h2 f2 e2 h3 f3 e3 stack,
    (h1, f1::stack, e1) ⇒ (h2, f2::stack, e2) ->
    (h2, f2::stack, e2) ⇒* (h3, f3::stack, e3) ->
    (h1, f1::stack, e1) ⇒* (h3, f3::stack, e3)
where "LHS '⇒*' RHS" := (multistep LHS RHS).

Theorem multi_one : forall h1 f1 e1 h2 f2 e2 stack,
  (h1, f1 :: stack, e1) ⇒ (h2, f2 :: stack, e2) ->
  (h1, f1 :: stack, e1) ⇒* (h2, f2 :: stack, e2).
Proof.
intros.
apply multi_trans with (h2 := h2) (f2 := f2) (e2 := e2).
exact H.
apply multi_refl.
Qed.

Theorem multi_concat : forall h1 f1 e1 h2 f2 e2 h3 f3 e3 stack,
  (h1, f1 :: stack, e1) ⇒* (h2, f2 :: stack, e2) ->
  (h2, f2 :: stack, e2) ⇒* (h3, f3 :: stack, e3) ->
  (h1, f1 :: stack, e1) ⇒* (h3, f3 :: stack, e3).
Proof.
intros.
generalize dependent h3.
generalize dependent f3.
generalize dependent e3.
dependent induction H.
- intros. exact H0.
- intros. apply multi_trans with h4 f4 e4.
  exact H. apply IHmultistep. exact H1.
Qed.

Lemma E_RecoverN : forall h h' f f' e e' stack,
    (h, f :: stack, e) ⇒* (h', f' :: stack, e') ->
    (h, f :: stack, expr_recover e) ⇒* (h', f' :: stack, expr_recover e').
Proof.
intros.
dependent induction H.
- apply multi_refl.
- apply multi_trans with (h2 := h2) (f2 := f2) (e2 := expr_recover e2).
  apply E_Recover1. exact H.
  apply IHmultistep.
Qed.

Lemma E_SeqN : forall h h' f f' e1 e1' e2 stack,
    (h, f :: stack, e1) ⇒* (h', f' :: stack, e1') ->
    (h, f :: stack, expr_seq e1 e2) ⇒* (h', f' :: stack, expr_seq e1' e2).
Proof.
intros.
dependent induction H.
- apply multi_refl.
- apply multi_trans with (h2 := h2) (f2 := f2) (e2 := expr_seq e0 e2).
  apply E_Seq1. exact H.
  apply IHmultistep.
Qed.

Lemma E_Asn_LocalN : forall h h' f f' name e e' stack,
    (h, f :: stack, e) ⇒* (h', f' :: stack, e') ->
    (h, f :: stack, expr_assign_local name e) ⇒* (h', f' :: stack, expr_assign_local name e').
Proof.
intros.
dependent induction H.
- apply multi_refl.
- apply multi_trans with (h2 := h2) (f2 := f2) (e2 := expr_assign_local name e2).
  apply E_Asn_Local1. exact H.
  apply IHmultistep.
Qed.

Lemma E_FldN : forall h h' f f' e e' name stack,
    (h, f :: stack, e) ⇒* (h', f' :: stack, e') ->
    (h, f :: stack, expr_field e name) ⇒* (h', f' :: stack, expr_field e' name).
Proof.
intros.
dependent induction H.
- apply multi_refl.
- apply multi_trans with (h2 := h2) (f2 := f2) (e2 := expr_field e2 name).
  apply E_Fld1. exact H.
  apply IHmultistep.
Qed.

Lemma E_Asn_Fld1N : forall h h' f f' e1 e1' e2 name stack,
    (h, f :: stack, e1) ⇒* (h', f' :: stack, e1') ->

    (h, f :: stack, expr_assign_field e1 name e2) ⇒*
    (h', f' :: stack, expr_assign_field e1' name e2).
Proof.
intros.
dependent induction H.
apply multi_refl.
- apply multi_trans with (h2 := h2) (f2 := f2) (e2 := expr_assign_field e0 name e2).
  apply E_Asn_Fld1. exact H.
  apply IHmultistep.
Qed.

Lemma E_Asn_Fld2N : forall h h' f f' t1 e2 e2' name stack,
    (h, f :: stack, e2) ⇒* (h', f' :: stack, e2') ->

    (h, f :: stack, expr_assign_field (expr_temp t1) name e2) ⇒*
    (h', f' :: stack, expr_assign_field (expr_temp t1) name e2').
Proof.
intros.
dependent induction H.
apply multi_refl.
- apply multi_trans with (h2 := h2) (f2 := f2) (e2 := expr_assign_field (expr_temp t1) name e0).
  apply E_Asn_Fld2. exact H.
  apply IHmultistep.
Qed.
*)
