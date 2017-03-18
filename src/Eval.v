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
      match find_redex e1 with
      | inl (r, ectx) => inl (r, expr_hole_seq ectx e2)
      | inr t => inl (redex_seq t e2, expr_hole_id)
      end

  | expr_recover e1 =>
      match find_redex e1 with
      | inl (r, ectx) => inl (r, expr_hole_recover ectx)
      | inr t => inl (redex_recover t, expr_hole_id)
      end

  | expr_assign_local x e1 =>
      match find_redex e1 with
      | inl (r, ectx) => inl (r, expr_hole_assign_local x ectx)
      | inr t => inl (redex_assign_local x t, expr_hole_id)
      end

  | expr_field e1 x =>
      match find_redex e1 with
      | inl (r, ectx) => inl (r, expr_hole_field ectx x)
      | inr t => inl (redex_field t x, expr_hole_id)
      end

  | expr_assign_field e1 x e2 =>
      match find_redex e1, find_redex e2 with
      | _, inl (r, ectx) => inl (r, expr_hole_assign_field1 e1 x ectx)
      | inl (r, ectx), inr t2 => inl (r, expr_hole_assign_field2 ectx x t2)
      | inr t1, inr t2 => inl (redex_assign_field t1 x t2, expr_hole_id)
      end

  | expr_call e0 n es =>
      match find_redex e0, list_find_redex es nil with
      | _, inl (r, ts, ectx, es') => inl (r, expr_hole_call1 e0 n ts ectx es')
      | inl (r, ectx), inr ts => inl (r, expr_hole_call2 ectx n ts)
      | inr t0, inr ts => inl (redex_call t0 n ts, expr_hole_id)
      end

  | expr_ctor kt k es =>
      match list_find_redex es nil with
      | inl (r, ts, ectx, es') => inl (r, expr_hole_ctor kt k ts ectx es')
      | inr ts => inl (redex_ctor kt k ts, expr_hole_id)
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


Definition eval (χ: heap) (σ: list frame) (e: expr) : option (heap * list frame * expr) :=
  match find_redex e, σ with
  | inl (redex_null, ectx), (φ::σ') =>
      let t := fresh φ in
      let φ' := <[t := v_null]>φ in
      Some (χ, φ'::σ', fill_hole ectx (expr_temp t))

  | inl (redex_seq t e2, ectx), _ => Some (χ, σ, fill_hole ectx e2)
  | inl (redex_recover t, ectx), _ => Some (χ, σ, fill_hole ectx (expr_temp t))
  | inl (redex_local x, ectx), (φ::σ') =>
      let t := fresh φ in
      let φ' := <[t := φ !!! x]>φ in
      Some (χ, φ'::σ', fill_hole ectx (expr_temp t))

  | inl (redex_assign_local x t, ectx), (φ::σ') =>
      let t' := fresh φ in
      let φ' := <[t' := φ !!! x]>(<[x := φ !!! t]>φ) in
      Some (χ, φ'::σ', fill_hole ectx (expr_temp t'))

  | inl (redex_field t x, ectx), (φ::σ') =>
      match φ !!! t with
      | v_null => Some (χ, φ::σ', fill_hole ectx (expr_temp t))
      | v_addr ω =>
          let t' := fresh φ in
          let φ' := <[t' := χ !!! (ω, x)]> φ in
          Some (χ, φ'::σ', fill_hole ectx (expr_temp t'))
      end

  | inl (redex_assign_field t x t', ectx), (φ::σ') =>
      match φ !!! t with
      | v_null => Some (χ, φ::σ', fill_hole ectx (expr_temp t))
      | v_addr ω =>
          let t'' := fresh φ in
          let φ' := <[t'' := χ !!! (ω, x)]> φ in
          let χ' := <[(ω, x) := φ !!! t']>χ in
          Some (χ', φ'::σ', fill_hole ectx (expr_temp t''))
      end

  | inl (redex_call t0 n ts, ectx), (φ::σ') =>
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

      | v_null => Some (χ, φ :: σ', expr_temp t0)
      end

  | inl (redex_ctor kt k ts, ectx), (φ::σ') =>
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

  | inr t, (φ'::φ::σ') =>
      let t' := fresh φ in
      let φ'' := {|
          method := φ.(method);
          locals := <[ t' := φ' !!! t ]>φ.(locals);
          hole := expr_hole_id
      |} in
      
      Some (χ, φ'' :: σ', fill_hole φ.(hole) (expr_temp t'))

  | inl (redex_null, _), [] => None
  | inl (redex_local _, _), [] => None
  | inl (redex_assign_local _ _, _), [] => None
  | inl (redex_field _ _, _), [] => None
  | inl (redex_assign_field _ _ _, _), [] => None
  | inl (redex_call _ _ _, _), [] => None
  | inl (redex_ctor _ _ _, _), [] => None
  | inr _, [] => None
  | inr _, [_] => None
  end.
End eval.
