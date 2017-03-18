(*Require Import Ast.*)

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Strings.String.

Require Import Coq.Structures.Equalities.
Require Import Coq.Arith.EqNat.

Require Import ch2o.prelude.nmap.
Require Import ch2o.prelude.base.

Require Import common.
Require Import Ast.
Require Import Semantics.
Require Import Entities.

Require Import Store.

Open Scope string_scope.

Section eval.
Context (P: program).

Inductive redex : Type :=
| redex_null : redex
| redex_seq : temp -> expr -> redex
| redex_recover : temp -> redex
| redex_local : string -> redex
| redex_assign_local : string -> temp -> redex
| redex_field : temp -> string -> redex
| redex_assign_field : temp -> string -> temp -> redex
| redex_call : temp -> string -> list temp -> redex
| redex_ctor : string -> string -> list temp -> redex
.

Fixpoint find_redex (e: expr) : (redex * expr_hole) + temp :=
  match e with
  | expr_temp t => inr t
  | expr_null => inl (redex_null, expr_hole_id)
  | expr_local x => inl (redex_local x, expr_hole_id)

  | expr_seq e1 e2 =>
      inl $ match find_redex e1 with
      | inl (r, ectx) => (r, expr_hole_seq ectx e2)
      | inr t => (redex_seq t e2, expr_hole_id)
      end

  | expr_recover e1 =>
      inl $ match find_redex e1 with
      | inl (r, ectx) => (r, expr_hole_recover ectx)
      | inr t => (redex_recover t, expr_hole_id)
      end

  | expr_assign_local x e1 =>
      inl $ match find_redex e1 with
      | inl (r, ectx) => (r, expr_hole_assign_local x ectx)
      | inr t => (redex_assign_local x t, expr_hole_id)
      end

  | expr_field e1 x =>
      inl $ match find_redex e1 with
      | inl (r, ectx) => (r, expr_hole_field ectx x)
      | inr t => (redex_field t x, expr_hole_id)
      end

  | expr_assign_field e1 x e2 =>
      inl $ match find_redex e1, find_redex e2 with
      | _, inl (r, ectx) => (r, expr_hole_assign_field1 e1 x ectx)
      | inl (r, ectx), inr t2 => (r, expr_hole_assign_field2 ectx x t2)
      | inr t1, inr t2 => (redex_assign_field t1 x t2, expr_hole_id)
      end

  | expr_call e0 n es =>
      inl $ match find_redex e0, list_find_redex es nil with
      | _, inl (r, ts, ectx, es') => (r, expr_hole_call1 e0 n ts ectx es')
      | inl (r, ectx), inr ts => (r, expr_hole_call2 ectx n ts)
      | inr t0, inr ts => (redex_call t0 n ts, expr_hole_id)
      end

  | expr_ctor kt k es =>
      inl $ match list_find_redex es nil with
      | inl (r, ts, ectx, es') => (r, expr_hole_ctor kt k ts ectx es')
      | inr ts => (redex_ctor kt k ts, expr_hole_id)
      end
  end
with 
  list_find_redex (es: list_expr) (ts: list temp) : (redex * list temp * expr_hole * list_expr + list temp) :=
  match es with
  | list_expr_nil => inr ts
  | list_expr_cons e es' =>
      match find_redex e with
      | inr t => list_find_redex es' (ts ++ [t])
      | inl (r, ectx) => inl (r, ts, ectx, es')
      end
  end
.

Definition eval_redex (χ: heap) (σ: list frame) (r: redex) (ectx: expr_hole) : option (heap * list frame * expr) :=
  match r, ectx, σ with
  | redex_null, ectx, (φ::σ') =>
      let t := fresh φ in
      let φ' := <[t := v_null]>φ in
      Some (χ, φ'::σ', fill_hole ectx (expr_temp t))

  | redex_seq t e2, ectx, (φ::σ') => Some (χ, φ::σ', fill_hole ectx e2)
  | redex_recover t, ectx, (φ::σ') => Some (χ, φ::σ', fill_hole ectx (expr_temp t))
  | redex_local x, ectx, (φ::σ') =>
      let t := fresh φ in
      let φ' := <[t := φ !!! x]>φ in
      Some (χ, φ'::σ', fill_hole ectx (expr_temp t))

  | redex_assign_local x t, ectx, (φ::σ') =>
      let t' := fresh φ in
      let φ' := <[t' := φ !!! x]>(<[x := φ !!! t]>φ) in
      Some (χ, φ'::σ', fill_hole ectx (expr_temp t'))

  | redex_field t x, ectx, (φ::σ') =>
      match φ !!! t with
      | v_null => Some (χ, φ::σ', fill_hole ectx (expr_temp t))
      | v_addr ω =>
          let t' := fresh φ in
          let φ' := <[t' := χ !!! (ω, x)]> φ in
          Some (χ, φ'::σ', fill_hole ectx (expr_temp t'))
      end

  | redex_assign_field t x t', ectx, (φ::σ') =>
      match φ !!! t with
      | v_null => Some (χ, φ::σ', fill_hole ectx (expr_temp t))
      | v_addr ω =>
          let t'' := fresh φ in
          let φ' := <[t'' := χ !!! (ω, x)]> φ in
          let χ' := <[(ω, x) := φ !!! t']>χ in
          Some (χ', φ'::σ', fill_hole ectx (expr_temp t''))
      end

  | redex_call t0 n ts, ectx, (φ::σ') =>
      match φ !!! t0 with
      | v_addr ω => 
        obj <- χ !! ω;
        '(xs, body) <- lookup_Mr P obj.(name) n;

        let φ'' := {|
          method := n;
          locals := <[* xs := map (φ !!!) ts ]>(<["this" := v_addr ω]>empty);
          hole := expr_hole_id
        |} in

        let φ' := {|
          method := φ.(method);
          locals := φ.(locals);
          hole := ectx
        |} in

        Some (χ, φ'' :: φ' :: σ', body)

      | v_null => Some (χ, φ :: σ', fill_hole ectx (expr_temp t0))
      end

  | redex_ctor kt k ts, ectx, (φ::σ') =>
      fs <- lookup_Fs P kt;
      '(xs, body) <- lookup_Mr P kt k;

      let ω := Nfresh χ in
      let fields := <[* fs := v_null ]>empty in
      let χ' := <[ ω := {| name := kt; fields := fields |} ]>χ in

      let φ'' := {|
        method := k;
        locals := <[* xs := map (φ !!!) ts ]>(<["this" := v_addr ω]>empty);
        hole := expr_hole_id
      |} in

      let φ' := {|
        method := φ.(method);
        locals := φ.(locals);
        hole := ectx
      |} in

      Some (χ', φ'' :: φ' :: σ', body)

  | redex_null, _, [] => None
  | redex_seq _ _, _, [] => None
  | redex_recover _, _, [] => None
  | redex_local _, _, [] => None
  | redex_assign_local _ _, _, [] => None
  | redex_field _ _, _, [] => None
  | redex_assign_field _ _ _, _, [] => None
  | redex_call _ _ _, _, [] => None
  | redex_ctor _ _ _, _, [] => None
  end.

Definition eval (χ: heap) (σ: list frame) (e: expr) : option (heap * list frame * expr) :=
  match find_redex e, σ with
  | inl (r, ectx), σ => eval_redex χ σ r ectx
  | inr t, (φ'::φ::σ') =>
      let t' := fresh φ in
      let φ'' := {|
          method := φ.(method);
          locals := <[ t' := φ' !!! t ]>φ.(locals);
          hole := expr_hole_id
      |} in

      Some (χ, φ'' :: σ', fill_hole φ.(hole) (expr_temp t'))

  | inr _, [] => None
  | inr _, [_] => None
  end.
End eval.

Definition expr_redex (r: redex) : expr :=
  match r with
  | redex_null => expr_null
  | redex_seq t e2 => expr_seq (expr_temp t) e2
  | redex_recover t => expr_recover (expr_temp t)
  | redex_local x => expr_local x
  | redex_assign_local x t => expr_assign_local x (expr_temp t)
  | redex_field t f => expr_field (expr_temp t) f
  | redex_assign_field t0 f t1 => expr_assign_field (expr_temp t0) f (expr_temp t1)
  | redex_call t0 n ts => expr_call (expr_temp t0) n (list_expr_temps ts)
  | redex_ctor kt k ts => expr_ctor kt k (list_expr_temps ts)
  end.

Lemma find_redex_fill : forall e e' r ectx,
  find_redex e = inl (r, ectx) ->
  e' = expr_redex r ->
  e = fill_hole ectx (e').
Proof.
Admitted.

Lemma eval_redex_sound : forall P χ χ' σ σ' ectx r e e',
  find_redex e = inl (r, ectx) ->
  eval_redex P χ σ r ectx = Some (χ', σ', e') -> step P (χ, σ, e) (χ', σ', e').
Proof.
intros.
destruct σ.
unfold eval_redex in  H0.
destruct r.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.
inversion H0.

remember r as r0.
destruct r.
unfold eval_redex in H0.
rewrite Heqr0 in H0.
inversion H0.
assert (e = fill_hole ectx (expr_redex r0)).
apply find_redex_fill with r0.
exact H.
reflexivity.
rewrite H1.
rewrite Heqr0.
unfold expr_redex.
apply step_hole.
apply step_null.
admit.
reflexivity.

unfold eval_redex in H0.
rewrite Heqr0 in H0.
inversion H0.
assert (e = fill_hole ectx (expr_redex r0)).
apply find_redex_fill with r0.
exact H.
reflexivity.
rewrite H1.
rewrite Heqr0.
unfold expr_redex.
apply step_hole.
apply step_seq.

unfold eval_redex in H0.
rewrite Heqr0 in H0.
inversion H0.
assert (e = fill_hole ectx (expr_redex r0)).
apply find_redex_fill with r0.
exact H.
reflexivity.
rewrite H1.
rewrite Heqr0.
unfold expr_redex.
apply step_hole.
apply step_recover.

unfold eval_redex in H0.
rewrite Heqr0 in H0.
inversion H0.
assert (e = fill_hole ectx (expr_redex r0)).
apply find_redex_fill with r0.
exact H.
reflexivity.
rewrite H1.
rewrite Heqr0.
unfold expr_redex.
apply step_hole.
apply step_local.
admit.
reflexivity.

unfold eval_redex in H0.
rewrite Heqr0 in H0.
inversion H0.
assert (e = fill_hole ectx (expr_redex r0)).
apply find_redex_fill with r0.
exact H.
reflexivity.
rewrite H1.
rewrite Heqr0.
unfold expr_redex.
apply step_hole.
apply step_asn_local.
admit.
reflexivity.

unfold eval_redex in H0.
rewrite Heqr0 in H0.
assert (e = fill_hole ectx (expr_redex r0)).
apply find_redex_fill with r0.
exact H.
reflexivity.
rewrite H1.
rewrite Heqr0.
unfold expr_redex.
destruct (f !!! t) eqn:?.
inversion H0.
apply step_hole.
apply step_field_null.
symmetry.
exact Heqy.
inversion H0.
apply step_hole.
apply step_field with a.
admit.
symmetry.
exact Heqy.
reflexivity.

unfold eval_redex in H0.
rewrite Heqr0 in H0.
assert (e = fill_hole ectx (expr_redex r0)).
apply find_redex_fill with r0.
exact H.
reflexivity.
rewrite H1.
rewrite Heqr0.
unfold expr_redex.
destruct (f !!! t) eqn:?.
inversion H0.
apply step_hole.
apply step_asn_field_null.
symmetry.
exact Heqy.
inversion H0.
apply step_hole.
apply step_asn_field with a.
admit.
symmetry.
exact Heqy.
reflexivity.
reflexivity.

unfold eval_redex in H0.
rewrite Heqr0 in H0.
assert (e = fill_hole ectx (expr_redex r0)).
apply find_redex_fill with r0.
exact H.
reflexivity.
rewrite H1. rewrite Heqr0.
unfold expr_redex.
destruct (f !!! t) eqn:?.
inversion H0.
apply step_hole.
apply step_call_null.
auto.
destruct (χ !! a) eqn:?. simpl in H0.
destruct (lookup_Mr P (name o) s) eqn:?.
simpl in H0.
destruct p as [xs body].
inversion H0.
apply step_sync with xs a.
symmetry.
exact Heqy.
rewrite <- H3. rewrite Heqo.
simpl.
symmetry. rewrite <- H5. exact Heqo0.
reflexivity.
reflexivity.
simpl in H0. inversion H0.
simpl in H0. inversion H0.

unfold eval_redex in H0.
rewrite Heqr0 in H0.
assert (e = fill_hole ectx (expr_redex r0)).
apply find_redex_fill with r0.
auto with *.
auto with *.
rewrite H1.
rewrite Heqr0.
unfold expr_redex.
destruct (lookup_Fs P s) as [fs|] eqn:?. simpl in H0.
destruct (lookup_Mr P s s0) eqn:?. simpl in H0.
destruct p as [xs body].
inversion H0.
apply step_ctor with (Nfresh χ) fs xs.

apply fin_map_dom.not_elem_of_dom.
apply Nfresh_fresh.
auto with *.
auto with *.
auto with *.
auto with *.
auto with *.
simpl in H0. inversion H0.
simpl in H0. inversion H0.

Admitted.

Lemma eval_sound : forall P χ χ' σ σ' e e',
  eval P χ σ e = Some (χ', σ', e') -> step P (χ, σ, e) (χ', σ', e').
Proof.
intros.
unfold eval in H.
destruct (find_redex e) eqn:?.
destruct p.
apply eval_redex_sound with (P:=P) (r:=r) (ectx:=e0).
exact Heqs.
exact H.

assert (e = expr_temp t).
destruct e.
unfold find_redex in Heqs. inversion Heqs. reflexivity.

unfold find_redex in Heqs. inversion Heqs.
unfold find_redex in Heqs. inversion Heqs.
unfold find_redex in Heqs. inversion Heqs.
unfold find_redex in Heqs. inversion Heqs.
unfold find_redex in Heqs. inversion Heqs.
unfold find_redex in Heqs. inversion Heqs.
unfold find_redex in Heqs. inversion Heqs.
unfold find_redex in Heqs. inversion Heqs.
unfold find_redex in Heqs. inversion Heqs.

destruct σ.
inversion H.
destruct σ.
inversion H.
inversion H.
rewrite H0.
apply step_return.
admit.
reflexivity.
Admitted.
