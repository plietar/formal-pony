Require Import ch2o.prelude.base.
Require Import ch2o.prelude.option.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.Strings.String.

Require Import Ast.
Require Import Store.
Require Import Entities.

Open Scope string_scope.

Section step.
Context (p: program).

Inductive step : heap * list frame * expr -> heap * list frame * expr -> Prop :=
| step_hole : forall χ χ' φ φ' σ e e' ectx,
    step (χ, φ::σ, e) (χ, φ'::σ, e') ->
    step (χ, φ::σ, fill_hole ectx e) (χ', φ'::σ, fill_hole ectx e')

| step_seq : forall χ σ t e,
    step (χ, σ, expr_seq (expr_temp t) e)
         (χ, σ, e)

| step_recover : forall χ σ t,
    step (χ, σ, expr_recover (expr_temp t))
         (χ, σ, (expr_temp t))

| step_local : forall χ φ σ t φ' x,
    not (t ∈ φ) ->
    φ' = <[t := φ !!! x]> φ ->
    step (χ, φ::σ, expr_local x)
         (χ, φ'::σ, expr_temp t)

| step_asn_local : forall χ φ φ' σ t t' x,
    not (t' ∈ φ) ->
    φ' = <[t' := φ !!! x]>(<[x := φ !!! t]>φ) ->
    step (χ, φ::σ, expr_assign_local x (expr_temp t))
         (χ, φ'::σ, expr_temp t')

| step_field : forall χ φ φ' σ t t' f ω,
    not (t' ∈ φ) ->
    v_addr ω = φ !!! t ->
    φ' = <[t' := χ !!! (ω, f)]> φ ->
    step (χ, φ::σ, expr_field (expr_temp t) f)
         (χ, φ'::σ, expr_temp t')

| step_asn_field : forall χ χ' φ φ' σ t t' t'' f ω,
    not (t'' ∈ φ) ->
    v_addr ω = φ !!! t ->
    φ' = <[t'' := χ !!! (ω, f)]>φ ->
    χ' = <[(ω, f) := φ !!! t']>χ ->

    step (χ, φ::σ, expr_assign_field (expr_temp t) f (expr_temp t'))
           (χ', φ'::σ, expr_temp t'')

| step_sync : forall χ φ φ' φ'' σ ectx t m e ts ω,
    v_addr ω = φ !!! t ->

    φ'' = {|
      method := m;
      locals := <["this" := (v_addr ω)]>empty;
      hole := expr_hole_id
    |} ->

    φ' = {|
      method := φ.(method);
      locals := φ.(locals);
      hole := ectx
    |} ->

    step (χ, φ :: σ, fill_hole ectx (expr_call (expr_temp t) m (list_expr_temps ts)))
         (χ, φ'' :: φ' :: σ, e)

| step_ctor : forall χ χ' ω φ φ' φ'' σ ectx kt k e ts,
    not (ω ∈ heap_dom χ) ->
    χ' = <[ω := {| name := kt; fields := empty |}]>χ ->

    φ'' = {|
      method := k;
      locals := <["this" := (v_addr ω)]>empty;
      hole := expr_hole_id
    |} ->

    φ' = {|
      method := φ.(method);
      locals := φ.(locals);
      hole := ectx
    |} ->

    step (χ, φ :: σ, fill_hole ectx (expr_ctor kt k (list_expr_temps ts)))
         (χ', φ'' :: φ' :: σ, e)

| step_return : forall χ φ φ' φ'' t t' σ,
    not (t' ∈ φ) ->
    φ'' = {|
        method := φ.(method);
        locals := <[t' := φ' !!! t]>φ.(locals);
        hole := φ.(hole);
    |} ->
    step (χ, φ' :: φ :: σ, expr_temp t)
         (χ, φ'' :: σ, fill_hole φ.(hole) (expr_temp t'))

| step_field_null : forall χ φ σ t f,
    v_null = φ !!! t ->

    step (χ, φ::σ, expr_field (expr_temp t) f)
         (χ, φ::σ, expr_temp t)

| step_asn_field_null : forall χ φ σ t t' f,
    v_null = φ !!! t ->

    step (χ, φ::σ, expr_assign_field (expr_temp t) f (expr_temp t'))
         (χ, φ::σ, expr_temp t)

| step_call_null : forall χ φ σ t n ts,
    v_null = φ !!! t ->

    step (χ, φ::σ, expr_call (expr_temp t) n (list_expr_temps ts))
         (χ, φ::σ, expr_temp t)
.

End step.
