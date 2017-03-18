Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.BinNums.
Require Import ch2o.prelude.prelude.
Require Import common.

Definition temp := N.

Inductive expr : Type :=
| expr_temp : temp -> expr
| expr_null : expr
| expr_seq : expr -> expr -> expr
| expr_recover : expr -> expr
| expr_local : string -> expr
| expr_assign_local : string -> expr -> expr
| expr_field : expr -> string -> expr
| expr_assign_field : expr -> string -> expr -> expr
| expr_call : expr -> string -> list_expr  -> expr
| expr_ctor : string -> string -> list_expr -> expr
with list_expr : Type :=
| list_expr_nil : list_expr
| list_expr_cons : expr -> list_expr -> list_expr
.

Fixpoint list_expr_coerce (l: list expr) := match l with
| nil => list_expr_nil
| (h :: t) => list_expr_cons h (list_expr_coerce t)
end.

Fixpoint list_expr_uncoerce (l: list_expr) := match l with
| list_expr_nil => nil
| list_expr_cons h t => h :: (list_expr_uncoerce t)
end.

Definition list_expr_temps ts := list_expr_coerce (map expr_temp ts).

Inductive expr_hole : Type :=
| expr_hole_id : expr_hole
| expr_hole_seq : expr_hole -> expr -> expr_hole
| expr_hole_recover : expr_hole -> expr_hole
| expr_hole_assign_local : string -> expr_hole -> expr_hole
| expr_hole_field : expr_hole -> string -> expr_hole
| expr_hole_assign_field1 : expr -> string -> expr_hole -> expr_hole
| expr_hole_assign_field2 : expr_hole -> string -> temp -> expr_hole
| expr_hole_call1 : expr -> string -> list temp -> expr_hole -> list_expr -> expr_hole
| expr_hole_call2 : expr_hole -> string -> list temp -> expr_hole
| expr_hole_ctor : string -> string -> list temp -> expr_hole -> list_expr -> expr_hole
.

Fixpoint fill_hole (cps: expr_hole) (filler: expr) : expr :=
  match cps with
  | expr_hole_id => filler
  | expr_hole_seq cps' e2 => expr_seq (fill_hole cps' filler) e2
  | expr_hole_recover cps' => expr_recover (fill_hole cps' filler)
  | expr_hole_assign_local name cps' => expr_assign_local name (fill_hole cps' filler)
  | expr_hole_field cps' name => expr_field (fill_hole cps' filler) name
  | expr_hole_assign_field1 e1 name cps' => expr_assign_field e1 name (fill_hole cps' filler)
  | expr_hole_assign_field2 cps' name t2 => expr_assign_field (fill_hole cps' filler) name (expr_temp t2)
  | expr_hole_call1 e0 name ts cps' es => expr_call e0 name (list_expr_coerce ((fmap expr_temp ts) ++ (fill_hole cps' filler) :: list_expr_uncoerce es))
  | expr_hole_call2 cps' name ts => expr_call (fill_hole cps' filler) name (list_expr_coerce (fmap expr_temp ts))
  | expr_hole_ctor n m ts cps' es => expr_ctor n m (list_expr_coerce ((fmap expr_temp ts) ++ (fill_hole cps' filler) :: list_expr_uncoerce es))
  end.

Inductive cap : Type :=
| cap_iso : cap
| cap_tag : cap
| cap_ref : cap
with ecap : Type :=
| ecap_cap : cap -> ecap
| cap_iso_eph : ecap
.

Coercion ecap_cap : cap >-> ecap.

Inductive ty : Type :=
| ty_name : string -> ecap -> ty.

Definition field : Type := string * ty.
Definition ctor : Type := string * (list (string * ty) * expr).
Definition func : Type := string * (cap * list (string * ty) * ty * expr).
Definition behv : Type := string * (list (string * ty) * expr).

Definition ctor_stub : Type := string * (list (string * ty) * expr).
Definition func_stub : Type := string * (cap * list (string * ty) * ty * expr).
Definition behv_stub : Type := string * (list (string * ty) * expr).

Definition class : Type := string * (list field * list ctor * list func).
Definition actor : Type := string * (list field * list ctor * list func * list behv).
Definition trait : Type := string * (list ctor_stub * list func_stub * list behv_stub).
Definition iface : Type := string * (list ctor_stub * list func_stub * list behv_stub).

Definition program : Type := list trait * list iface * list class * list actor.

Section lookup.
Context (P: program).

Fixpoint lookup_P (ds: string) : option (list field * list ctor * list func * list behv) :=
  let '(nts, sts, cts, ats) := P in
  match cts !! ds, ats !! ds with
  | Some (fs, ks, ms), _ => Some (fs, ks, ms, nil)
  | None, Some (fs, ks, ms, bs) => Some (fs, ks, ms, bs)
  | None, None => None
  end.

Fixpoint lookup_Fs (ds: string) : option (list string) :=
  '(fs, ks, ms, bs) <- lookup_P ds;
  Some (map fst fs).

Fixpoint lookup_F (ds f: string) : option ty :=
  '(fs, ks, ms, bs) <- lookup_P ds;
  fs !! f.

Definition lookup_Md (ds n: string) : option (ty * list (string * ty) * ty) :=
  '(_, ks, ms, bs) <- lookup_P ds;
  '(args_ty, _) <- ks !! n;
  Some (ty_name ds cap_ref, args_ty, ty_name ds cap_ref).

Definition lookup_Mr (ds n: string) : option (list string * expr) :=
  '(_, ks, ms, bs) <- lookup_P ds;
  match ks !! n, ms !! n, bs !! n with
  | Some (args_ty, e), _, _ => Some (map fst args_ty, e)
  | None, Some (_, args_ty, _, e), _ => Some (map fst args_ty, e)
  | None, None, Some (args_ty, e) => Some (map fst args_ty, e)
  | None, None, None => None
  end.

End lookup.
