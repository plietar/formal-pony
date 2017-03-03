Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Inductive expr : Type :=
| expr_this : expr
| expr_var : string -> expr
| expr_assign_var : string -> expr -> expr
| expr_seq : expr -> expr -> expr
| expr_field : expr -> string -> expr
| expr_assign_field : expr -> string -> expr -> expr
| expr_recover : expr -> expr
| expr_call : expr -> string -> list expr -> expr

| expr_null : expr
| expr_term : nat -> expr
.

Inductive item : Type :=
| item_field : string -> item
| item_ctor : string -> list string -> expr -> item
| item_func : string -> list string -> expr -> item
| item_behv : string -> list string -> expr -> item
.

Inductive item_stub : Type :=
| item_stub_ctor : string -> list string -> item_stub
| item_stub_func : string -> list string -> item_stub
| item_stub_behv : string -> list string -> item_stub
.

Inductive def : Type :=
| def_class : string -> list item -> def
| def_actor : string -> list item -> def
| def_trait : string -> list item_stub -> def
| def_iface : string -> list item_stub -> def
.

Inductive program : Type := Program : list def -> program.
