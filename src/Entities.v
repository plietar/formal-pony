Require Import ch2o.prelude.base.
Require Import ch2o.prelude.nmap.

Require Import Coq.Arith.EqNat.
Require Import Coq.Strings.String.

Require Import Ast.
Require Import Store.
Require Export localmap.

Definition addr := N.

Inductive value : Type :=
| v_null: value
| v_addr: addr -> value.

Record frame : Type := {
  method: string;
  locals: localmap value;
  hole: expr_hole
}.

Instance frame_lookup {K} `{l: Lookup K value (localmap value)} : Lookup K value frame := {
  lookup k f := lookup k f.(locals)
}.

Instance frame_insert {K} `{l: Insert K value (localmap value)} : Insert K value frame := {
  insert k v f := {|
    method := f.(method);
    locals := insert k v f.(locals);
    hole := f.(hole)
  |}
}.

Instance frame_elem_of : ElemOf local_id frame :=
  fun l f => elem_of l (dom localset f.(locals)).

Instance frame_elem_of_temp : ElemOf temp frame :=
  fun t f => elem_of (TempId t) (dom localset f.(locals)).

Instance frame_elem_of_var : ElemOf string frame :=
  fun x f => elem_of (SourceId x) (dom localset f.(locals)).

Instance frame_fresh_temp : Fresh temp frame :=
  fun f => fresh f.(locals).

Record object : Type := {
  name: string;
  fields: stringmap.stringmap value
}.

Definition heap := Nmap object.
Definition heap_dom (χ: heap) : Nset := dom Nset χ.

Instance heap_field_lookup : Lookup (addr * string) value heap := {
  lookup idx χ :=
    let (ω, f) := idx in
    match χ !! ω with
    | Some obj => obj.(fields) !! f
    | None => None
    end
}.

Instance heap_field_insert : Insert (addr * string) value heap := {
  insert idx v χ :=
    let (ω, f) := idx in

    alter (fun obj => {|
      name := obj.(name);
      fields := insert f v obj.(fields)
    |}) ω χ
}.

Class LookupDefault (K A M : Type) := lookup_default: K -> M -> A.
Notation "m !!! i" := (lookup_default i m) (at level 20) : C_scope.
Notation "(!!!)" := lookup_default (only parsing) : C_scope.
Notation "( m !!!)" := (λ i, lookup_default i m) (only parsing) : C_scope.
Notation "(!!! i )" := (lookup_default i) (only parsing) : C_scope.

Instance value_lookup_default {K M} `{l : Lookup K value M} : LookupDefault K value M :=
  fun k m => from_option v_null (lookup k m).

