Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.String.

Require Import Store.

Definition addr := nat.

Inductive value : Type :=
| v_null: value
| v_addr: addr -> value.

Inductive local_id : Type :=
| SourceId: string -> local_id
| TempId: nat -> local_id.

Module addr_eq.
  Definition t := addr.
  Definition eqb x y : bool := beq_nat x y.
End addr_eq.

Module local_id_eq.
  Definition t := local_id.
  Definition eqb x y : bool :=
    match x, y with
    | SourceId x', SourceId y' => if string_dec x' y' then true else false
    | TempId x', TempId y' => beq_nat x' y'
    | _, _ => false
    end.
End local_id_eq.

Module value_default.
  Definition t := value.
  Definition default := v_null.
End value_default.

Module field_id_eq.
  Definition t := string.
  Definition eqb x y : bool := if string_dec x y then true else false.
End field_id_eq.

Module Frame.
  Include Store local_id_eq value_default.
  Definition alloc_temp (st: store) : nat :=
    List.length st.
End Frame.
Definition frame := Frame.store.

Module Fields.
  Include Store field_id_eq value_default.
End Fields.

Definition object : Type := string * Fields.store.

Module object_default.
  Definition t : Type := object.
  Definition default : t := (EmptyString, Fields.empty).
End object_default.

Module Heap.
  Include Store addr_eq object_default.
  Definition alloc_addr (st: store) : addr :=
    List.length st.

  Definition create (st: store) (name: string) : store * addr :=
    let addr := alloc_addr st in
    let obj := (name, Fields.empty) in
    (set st addr obj, addr).

  Definition get_field (st: store) (a: addr) (f: string) : value :=
    let obj := get st a in
    Fields.get (snd obj) f.

  Definition set_field (st: store) (a: addr) (f: string) (v: value) : store :=
    let obj := get st a in
    let fields' := Fields.set (snd obj) f v in
    set st a (fst obj, fields').
End Heap.

Definition heap := Heap.store.
