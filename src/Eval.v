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
(*Require Import Semantics.*)
Require Import Entities.

Require Import Store.

Open Scope string_scope.

Fixpoint lookup_ctor (m: string) (its: list item) : option (list string * expr) :=
  match its with
  | nil => None
  | item_ctor name args body :: tail =>
      if string_dec m name
      then Some (args, body)
      else lookup_ctor m tail
  | _ :: tail => lookup_ctor m tail
  end.

Fixpoint lookup_method (m: string) (its: list item) : option (list string * expr) :=
  match its with
  | nil => None
  | item_func name args body :: tail =>
      if string_dec m name
      then Some (args, body)
      else lookup_method m tail
  | _ :: tail => lookup_method m tail
  end.

Fixpoint lookup_class (ty: string) (its: list def) : option (list item) :=
  match its with
  | nil => None
  | def_class name items :: tail =>
      if string_dec ty name
      then Some items
      else lookup_class ty tail
  | _ :: tail => lookup_class ty tail
  end.

Fixpoint expr_size (e: expr) : nat :=
  match e with
  | expr_temp _ => 1
  | expr_seq e1 e2 => 1 + expr_size e1 + expr_size e2
  | expr_recover e => 1 + expr_size e
  | expr_local _ => 1
  | expr_assign_local _ e => 1 + expr_size e
  | expr_field e _ => 1 + expr_size e
  | expr_assign_field e1 _ e2 => 1 + expr_size e1 + expr_size e2
  | expr_call e0 _ es => 1 + expr_size e0 + expr_list_size es
  | expr_ctor _ _ es => 1 + expr_list_size es
  end
with expr_list_size es := match es with
  | list_expr_nil => 0
  | list_expr_cons e tail => expr_size e + expr_list_size tail
end.

Fixpoint eval' (p: program) (h: heap) (stack: list frame) (e: expr) (cps: expr_hole)
  : option (heap * list frame * expr) :=
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

  | (f :: stack'), (expr_call e0 mname es) =>
    match eval_args p h stack nil es (fun ts es' => compose_hole cps (expr_hole_call1 e0 mname ts expr_hole_id es')) with
    | None => None
    | Some (inl x) => Some x
    | Some (inr ts) =>
      match e0 with
      | expr_temp t0 =>
        match f !!! t0 with
        | v_addr addr => 
          obj <- h !! addr;
          '(argnames, body) <- lookup_class obj.(name) p >>= lookup_method mname;

          let f'' := {|
            method := mname;
            locals := fold_left (fun f_ u => <[fst u := f !!! snd u]>f_) (zip argnames ts) (<["this" := v_addr addr]>empty);
            hole := expr_hole_id
          |} in

          let f' := {|
            method := f.(method);
            locals := f.(locals);
            hole := cps
          |} in

          Some (h, f'' :: f' :: stack', body)

        | v_null => Some (h, f :: stack', fill_hole cps (expr_temp t0))
        end
      | _ => eval' p h stack e0 (compose_hole cps (expr_hole_call2 expr_hole_id mname ts))
      end
    end

  | (f :: stack'), expr_ctor tyname ctor es =>
    match eval_args p h stack nil es (fun ts es' => compose_hole cps (expr_hole_ctor tyname ctor ts expr_hole_id es')) with
    | None => None
    | Some (inl x) => Some x
    | Some (inr ts) =>
      '(argnames, body) <- lookup_class tyname p >>= lookup_ctor ctor;

      let addr := Nfresh h in
      let h' := <[ addr := {| name := tyname; fields := empty |} ]>h in

      let f'' := {|
        method := ctor;
        locals := fold_left (fun f_ u => <[fst u := f !!! snd u]>f_) (zip argnames ts) (<["this" := v_addr addr]>empty);
        hole := expr_hole_id
      |} in

      let t := fresh f in

      let f' := {|
        method := f.(method);
        locals := f.(locals);
        hole := cps
      |} in

      Some (h', f'' :: f' :: stack', body)
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

  | stack, expr_seq e1 e2 => eval'  p h stack e1 (compose_hole cps (expr_hole_seq expr_hole_id e2))
  | stack, expr_recover e1 => eval'  p h stack e1 (compose_hole cps (expr_hole_recover expr_hole_id))

  | stack, expr_assign_local name e1 => eval'  p h stack e1 (compose_hole cps (expr_hole_assign_local name expr_hole_id))
  | stack, expr_field e1 name => eval'  p h stack e1 (compose_hole cps (expr_hole_field expr_hole_id name))
  | stack, expr_assign_field e1 name (expr_temp t2) => eval'  p h stack e1 (compose_hole cps (expr_hole_assign_field2 expr_hole_id name t2))
  | stack, expr_assign_field e1 name e2 => eval'  p h stack e2 (compose_hole cps (expr_hole_assign_field1 e1 name expr_hole_id))
  end
with
  eval_args (p: program) (h: heap) (stack: list frame) (ts: list N) (es: list_expr) (cps: list N -> list_expr -> expr_hole) : option ((heap * list frame * expr) + list N) :=
  match es with
  | list_expr_nil => Some (inr ts)
  | list_expr_cons (expr_temp t) tail => eval_args p h stack (t::ts) tail cps
  | list_expr_cons e tail => fmap inl (eval' p h stack e (cps ts tail))
  end.

Definition eval (p: program) (h: heap) (stack: list frame) (e: expr) : option (heap * list frame * expr) :=
  eval' p h stack e expr_hole_id.
