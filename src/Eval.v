(*Require Import Ast.*)

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Strings.String.

Require Import Coq.Structures.Equalities.
Require Import Coq.Arith.EqNat.

Require Import ch2o.prelude.base.

Require Import Ast.
Require Import Semantics.
Require Import Entities.
Require Import Store.

Fixpoint eval' (h: heap) (stack: list frame) (e: expr) (cps: expr_hole) : option (heap * list frame * expr) :=
  match stack, e with
  | nil, _ => None
  | (_ :: nil), expr_temp t => None

  | (f :: f' :: stack'), expr_temp t =>
    let cps := f'.(hole) in
    let t' := fresh f' in
    let value := f !!! t in
    let f'' := {|
      method := f'.(method);
      locals := <[t' := value]>f'.(locals);
      hole := expr_hole_id
    |} in
    Some (h, f'' :: stack', fill_hole cps (expr_temp t'))

  | (f :: stack'), expr_call (expr_temp t) name =>
    match f !!! t with
    | v_addr addr => 
      let f'' := {|
        method := name;
        locals := <["this" := v_addr addr]>empty;
        hole := expr_hole_id
      |} in

      let f' := {|
        method := f.(method);
        locals := f.(locals);
        hole := cps
      |} in

      Some (h, f'' :: f' :: stack', expr_local "this")

    | v_null => Some (h, f :: stack', fill_hole cps (expr_temp t))
    end

  | (f :: stack'), expr_seq (expr_temp t) e' => Some (h, f :: stack', fill_hole cps e')

  | (f :: stack'), expr_recover (expr_temp t) => Some (h, f :: stack', fill_hole cps (expr_temp t))

  | (f :: stack'), expr_local name =>
      let t := fresh f in
      let f' := <[t := f !!! name]>f in

      Some (h, f' :: stack', fill_hole cps (expr_temp t))

  | (f :: stack'), expr_assign_local name (expr_temp t) =>
      let t' := fresh f in
      let f' := <[t' := f !!! name]>(<[name := f !!! t]>f) in

      Some (h, f' :: stack', fill_hole cps (expr_temp t'))

  | (f :: stack'), expr_field (expr_temp t) name =>
    match f !!! t with
    | v_addr addr => 
      let t' := fresh f in
      let f' := <[t' := h !!! (addr, name)]>f in

      Some (h, f' :: stack', fill_hole cps (expr_temp t'))

    | v_null => Some (h, f :: stack', fill_hole cps (expr_temp t))
    end

  | (f :: stack'), expr_assign_field (expr_temp t) name (expr_temp t') =>
    match f !!! t with
    | v_addr addr => 
      let t'' := fresh f in
      let f' := <[t'' := h !!! (addr, name)]>f in
      let h' := <[(addr, name) := f !!! t']>h in

      Some (h', f' :: stack', fill_hole cps (expr_temp t''))

    | v_null => Some (h, f :: stack', fill_hole cps (expr_temp t))
    end

  | stack, expr_seq e1 e2 => eval' h stack e1 (compose_hole cps (expr_hole_seq expr_hole_id e2))
  | stack, expr_recover e1 => eval' h stack e1 (compose_hole cps (expr_hole_recover expr_hole_id))

  | stack, expr_assign_local name e1 => eval' h stack e1 (compose_hole cps (expr_hole_assign_local name expr_hole_id))
  | stack, expr_field e1 name => eval' h stack e1 (compose_hole cps (expr_hole_field expr_hole_id name))
  | stack, expr_assign_field e1 name (expr_temp t2) => eval' h stack e1 (compose_hole cps (expr_hole_assign_field2 expr_hole_id name t2))
  | stack, expr_assign_field e1 name e2 => eval' h stack e2 (compose_hole cps (expr_hole_assign_field1 e1 name expr_hole_id))
  | stack, expr_call e1 name => eval' h stack e1 (compose_hole cps (expr_hole_call1 expr_hole_id name))
  end.

Definition eval (h: heap) (stack: list frame) (e: expr) : option (heap * list frame * expr) :=
  eval' h stack e expr_hole_id.
