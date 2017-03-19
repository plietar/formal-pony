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
| cap_trn : cap
| cap_ref : cap
| cap_val : cap
| cap_box : cap
| cap_tag : cap
with ecap : Type :=
| ecap_cap : cap -> ecap
| cap_iso_eph : ecap
| cap_trn_eph : ecap
.

Coercion ecap_cap : cap >-> ecap.

Inductive ty : Type :=
| ty_name : string -> ecap -> ty
| ty_null : ty.

Definition field : Type := string * ty.
Definition ctor : Type := string * (list (string * ty) * expr).
Definition func : Type := string * (cap * list (string * ty) * ty * expr).
Definition behv : Type := string * (list (string * ty) * expr).

Definition ctor_stub : Type := string * (list (string * ty)).
Definition func_stub : Type := string * (cap * list (string * ty) * ty).
Definition behv_stub : Type := string * (list (string * ty)).

Definition class : Type := string * (list field * list ctor * list func * list string).
Definition actor : Type := string * (list field * list ctor * list func * list behv * list string).
Definition trait : Type := string * (list ctor_stub * list func_stub * list behv_stub * list string).
Definition iface : Type := string * (list ctor_stub * list func_stub * list behv_stub * list string).

Definition program : Type := list trait * list iface * list class * list actor.

Section lookup.
Context (P: program).

Definition lookup_is_trait (ds: string) : bool :=
  let '(nts, sts, cts, ats) := P in
  if decide (is_Some (nts !! ds)) then true else false.

Definition lookup_is_interface (ds: string) : bool :=
  let '(nts, sts, cts, ats) := P in
  if decide (is_Some (sts !! ds)) then true else false.

Definition lookup_is_class (ds: string) : bool :=
  let '(nts, sts, cts, ats) := P in
  if decide (is_Some (cts !! ds)) then true else false.

Definition lookup_is_actor (ds: string) : bool :=
  let '(nts, sts, cts, ats) := P in
  if decide (is_Some (ats !! ds)) then true else false.

Definition lookup_P (ds: string) : option (list field * list ctor * list func * list behv * list string + list ctor_stub * list func_stub * list behv_stub * list string) :=
  let '(nts, sts, cts, ats) := P in
  match nts !! ds, sts !! ds, cts !! ds, ats !! ds with
  | Some (ks, ms, bs, is), _, _, _ => Some (inr (ks, ms, bs, is))
  | None, Some (ks, ms, bs, is), _, _ => Some (inr (ks, ms, bs, is))
  | None, None, Some (fs, ks, ms, is), _ => Some (inl (fs, ks, ms, nil, is))
  | None, None, None, Some (fs, ks, ms, bs, is) => Some (inl (fs, ks, ms, bs, is))
  | None, None, None, None => None
  end.

Definition lookup_Fs (ds: string) : option (list string) :=
  match lookup_P ds with
  | Some (inl (fs, ks, ms, bs, is)) => Some (map fst fs)
  | Some (inr _) => None
  | None => None
  end.

Definition lookup_F (ds f: string) : option ty :=
  match lookup_P ds with
  | Some (inl (fs, ks, ms, bs, is)) => fs !! f
  | Some (inr _) => None
  | None => None
  end.

Definition lookup_Mr (ds n: string) : option (list string * expr) :=
  match lookup_P ds with
  | Some (inl (fs, ks, ms, bs, is)) =>
      match ks !! n, ms !! n, bs !! n with
      | Some (args_ty, e), _, _ => Some (map fst args_ty, e)
      | None, Some (_, args_ty, _, e), _ => Some (map fst args_ty, e)
      | None, None, Some (args_ty, e) => Some (map fst args_ty, e)
      | None, None, None => None
      end

  | Some (inr _) => None
  | None => None
  end.

Definition lookup_Is (ds: string) : option (list string) :=
  match lookup_P ds with
  | Some (inl (fs, ks, ms, bs, is)) => Some is
  | Some (inr (ks, ms, bs, is)) => Some is
  | None => None
  end.

Fixpoint lookup_Ks (maxdepth: nat) (ds: string) : option (list ctor_stub) :=
  match maxdepth, lookup_P ds with
  | S _, Some (inl (fs, ks, ms, bs, is)) =>
      Some (map (λ kt, (fst kt, fst (snd kt))) ks)

  | S maxdepth', Some (inr (ks, ms, bs, is)) =>
      ks' <- concatMapM (lookup_Ks maxdepth') is;
      Some (ks ++ ks')

  | S _, None => None
  | O, _ => None
  end.

Fixpoint lookup_Ms (maxdepth: nat) (ds: string) : option (list func_stub) :=
  match maxdepth, lookup_P ds with
  | S _, Some (inl (fs, ks, ms, bs, is)) =>
      Some (map (λ mt, (fst mt, fst (snd mt))) ms)

  | S maxdepth', Some (inr (ks, ms, bs, is)) =>
      ms' <- concatMapM (lookup_Ms maxdepth') is;
      Some (ms ++ ms')

  | S _, None => None
  | O, _ => None
  end.

Definition lookup_Md (ds n: string) : option (ty * list (string * ty) * ty) :=
  ks <- lookup_Ks 1000 ds;
  ms <- lookup_Ms 1000 ds;

  match ks !! n, ms !! n with
  | Some args_ty, _ =>
      Some (ty_name ds cap_ref, args_ty, ty_name ds cap_ref)

  | None, Some (reccap, args_ty, retty) =>
      Some (ty_name ds (ecap_cap reccap), args_ty, retty)

  | None, None => None
  end.

End lookup.

Instance program_size : Size program :=
  fun P => let '(nt, st, ct, at_) := P in length nt + length st + length ct + length at_.

Instance program_elem_of : ElemOf string program :=
  fun ds P =>
    let '(nts, sts, cts, ats) := P in
    (∃ x, (ds, x) ∈ nts) ∨ (∃ x, (ds, x) ∈ sts) ∨ (∃ x, (ds, x) ∈ cts) ∨ (∃ x, (ds, x) ∈ ats).

Lemma list_tuple_lookup_not_elem {B}: forall (l: list (string*B)) (k: string),
  list_tuple_lookup k l = None -> forall (v: B), not (elem_of (k, v) l).
intros.
induction l.
apply not_elem_of_nil.
destruct a.
unfold list_tuple_lookup in H.
destruct (string_dec k s).
inversion H.
fold (list_tuple_lookup k l) in H.
apply not_elem_of_cons.
auto with *.
Qed.

Lemma list_tuple_lookup_elem {B}: forall (l: list (string*B)) (k: string) (v: B),
  elem_of (k, v) l -> (exists v', list_tuple_lookup k l = Some v').
intros.
induction l.
- contradict H. apply not_elem_of_nil.
- destruct a as [k0 v0].
  unfold list_tuple_lookup.
  destruct (elem_of_cons l (k,v) (k0,v0)).
  destruct (string_dec k k0).
  + exists v0. auto.
  + fold (list_tuple_lookup k l).
    apply IHl.
    destruct (H0 H).
    * auto with *.
    * exact H2.
Qed.

Lemma list_tuple_lookup_elem' {B}: forall (l: list (string*B)) (k: string) (v: B),
  list_tuple_lookup k l = Some v -> elem_of (k, v) l.
Proof.
intros.
induction l.
- unfold list_tuple_lookup in H.
  inversion H.

- unfold list_tuple_lookup in H.
  destruct a as [k0 v0].
  destruct (string_dec k k0).
  + inversion H.
    destruct (elem_of_cons l (k,v) (k0,v0)).
    assert ((k,v)=(k0,v0)).
    auto with *.
    rewrite <- H1. rewrite e.
    rewrite <- H1 in H2. rewrite e in H2.
    auto with *.
  + fold (list_tuple_lookup k l) in H.
    destruct (elem_of_cons l (k,v) (k0,v0)).
    apply H1.
    right.
    apply IHl.
    exact H.
Admitted.

Lemma lookup_P_is_some_elem_of1 : forall P ds,
  ds ∈ P -> is_Some (lookup_P P ds).
Proof.
intros.
destruct P as [[[nts sts] cts] ats].
unfold elem_of, program_elem_of in H.
unfold is_Some, lookup_P.

destruct  (nts !! ds) as [x|] eqn:?.
destruct x as [[[ks ms] bs] is].
exists (inr (ks,ms,bs,is)).
auto.

destruct  (sts !! ds) as [x|] eqn:?.
destruct x as [[[ks ms] bs] is].
exists (inr (ks,ms,bs,is)).
auto.

destruct  (cts !! ds) as [x|] eqn:?.
destruct x as [[[fs ks] ms] is].
exists (inl (fs,ks,ms,nil,is)).
auto.

destruct  (ats !! ds) as [x|] eqn:?.
destruct x as [[[[fs ks] ms] bs] is].
exists (inl (fs,ks,ms,bs,is)).
auto.

destruct H as [H|[H|[H|H]]].
destruct H. contradict H. apply list_tuple_lookup_not_elem. auto.
destruct H. contradict H. apply list_tuple_lookup_not_elem. auto.
destruct H. contradict H. apply list_tuple_lookup_not_elem. auto.
destruct H. contradict H. apply list_tuple_lookup_not_elem. auto.
Qed.

Lemma lookup_P_is_some_elem_of2 : forall P ds,
   is_Some (lookup_P P ds) -> ds ∈ P.
Proof.
intros.
destruct P as [[[nts sts] cts] ats].
unfold is_Some, lookup_P in H.
unfold elem_of, program_elem_of.

destruct  (nts !! ds) as [x|] eqn:?.
- destruct x as [[[ks ms] bs] is].
  left.
  exists (ks,ms,bs,is).
  apply list_tuple_lookup_elem'.
  auto.

- destruct  (sts !! ds) as [x|] eqn:?.
  + destruct x as [[[ks ms] bs] is].
    right. left.
    exists (ks,ms,bs,is).
    apply list_tuple_lookup_elem'.
    auto.

  + destruct  (cts !! ds) as [x|] eqn:?.
    * destruct x as [[[fs ks] ms] is].
      right. right. left.
      exists (fs,ks,ms,is).
      apply list_tuple_lookup_elem'.
      auto.

    * destruct  (ats !! ds) as [x|] eqn:?.
      ++ destruct x as [[[[fs ks] ms] bs] is].
         right. right. right.
         exists (fs,ks,ms,bs,is).
         apply list_tuple_lookup_elem'.
         auto.

      ++ destruct H.
         inversion H.

Qed.
