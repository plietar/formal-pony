Require Import Ast.
Require Import ch2o.prelude.stringmap.
Require Import ch2o.prelude.base.
Require Import ch2o.prelude.list.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Sumbool.
Require Import pigeon.
Require Import common.

Definition subtype_cap (sub super: ecap) := 
  match sub, super with
  | cap_iso_eph, _ => Some ()
  | cap_iso, cap_iso => Some ()
  | cap_ref, cap_ref => Some ()
  | _, cap_tag => Some ()
  | _, _ => None
  end.

Record Subtyping : Type := {
  subtype_ty' : ty -> ty -> option unit;
  subtype_structural' : string -> string -> option unit;
}.

Definition assumes_wf (P: program) (assumes: list (string * string)) : Prop :=
  ch2o.prelude.base.NoDup assumes ∧ Forall (λ a, a ∈ (P, P)) assumes.

Program Fixpoint subtyping (P: program) (assumes: list (string * string) | assumes_wf P assumes)
    {measure (size (P,P) - size (assumes: list (string * string)))} : Subtyping :=

  let fix subclass (maxdepth: nat) (sub_name: string) (super_name: string) : option unit :=
    let fix subtype_nominal (is: list string) :=
      match maxdepth, is with
      | S maxdepth', i::is' =>
          match subclass maxdepth' i super_name with
          | Some () => Some ()
          | None => subtype_nominal is'
          end
      | O, _ => None
      | _, nil => None
      end
    in

    match decide (elem_of (sub_name, super_name) (assumes: list (string * string))) with
    | left _ => Some ()
    | right HnotElem =>
        is <- lookup_Is P sub_name;

        if string_beq sub_name super_name
        then Some () else

        if decide (is_Some (subtype_nominal is))
        then Some () else

        if decide (is_Some (lookup_P P sub_name) ∧ is_Some (lookup_P P super_name))
        then
          let assumes' := ((sub_name, super_name)::assumes) in
          subtype_structural' (subtyping P assumes') sub_name super_name
        else

        None
    end
  in

  let subtype_ty (sub_ty: ty) (super_ty: ty) :=
    match sub_ty, super_ty with
    | ty_name name_sub cap_sub, ty_name name_super cap_super =>
        _ <- subclass 100 name_sub name_super;
        subtype_cap cap_sub cap_super

    | ty_null, _ => Some ()
    | _, ty_null => None
    end
  in

  let fix subtype_args (sub_args: list (string * ty)) (super_args: list (string * ty)) :=
    match sub_args, super_args with
    | nil, nil => Some ()
    | (_, sub_arg_ty)::sub_args', (_, super_arg_ty)::super_args' =>
        _ <- subtype_ty sub_arg_ty super_arg_ty;
        subtype_args sub_args' super_args'
    | _, _ => None
    end
  in

  let subtype_method (sub_method: func_stub) (super_method: func_stub) : option unit :=
    let '(_, (sub_recv, sub_args, sub_retty)) := sub_method in
    let '(_, (super_recv, super_args, super_retty)) := super_method in

    _ <- subtype_cap sub_recv super_recv;  (* Covariant receiver capability *)
    _ <- subtype_args super_args sub_args; (* Contravariant arguments *)
    _ <- subtype_ty sub_retty super_retty; (* Covariant return type *)
    Some ()
  in

  let subtype_structural (sub_name: string) (super_name: string) : option unit :=
    sub_ms <- lookup_Ms P 100 sub_name;
    super_ms <- lookup_Ms P 100 super_name;

    _ <- mapM (λ m, m' <- sub_ms !! (fst m); subtype_method (fst m, m') m) super_ms;

    Some ()
  in

  {|
      subtype_ty' := subtype_ty;
      subtype_structural' := subtype_structural;
  |}.

Next Obligation.
unfold assumes_wf.
destruct H2.
split.
+ apply NoDup_cons_2.
  exact HnotElem.
  exact H2.
+ apply Forall_cons.
  unfold elem_of, collection_cross_elem.
  - split.
    * apply lookup_P_is_some_elem_of2.
      auto.
    * apply lookup_P_is_some_elem_of2.
      auto.
  - exact H3.
Defined.

Next Obligation.
destruct H2.
assert ((size ((sub_name, super_name)::assumes)) <= size (P, P)).

apply pigeonhole.
+ apply NoDup_cons_2.
  exact HnotElem.
  exact H2.
+ apply Forall_cons.
  unfold elem_of, collection_cross_elem.
  - split.
    * apply lookup_P_is_some_elem_of2.
      auto.
    * apply lookup_P_is_some_elem_of2.
      auto.
  - exact H3.
+
unfold size, list_size, Datatypes.length, collection_cross_size in H4.
fold (Datatypes.length assumes) in H4.

unfold size, list_size, Datatypes.length, collection_cross_size.
fold (Datatypes.length assumes).
fold (size P).

omega.

Defined.

Next Obligation.
split.
intros.
unfold not.
intros.
destruct H1.
auto with *.
unfold not.
intros.
destruct H1.
auto with *.
Defined.

Next Obligation.
split.
intros.
unfold not.
intros.
destruct H3.
auto with *.
unfold not.
intros.
destruct H3.
auto with *.
Defined.

Program Definition subtyping' (P: program) : Subtyping := subtyping P nil.
Next Obligation.
unfold assumes_wf.
split.
apply NoDup_nil_2.
apply Forall_nil.
Qed.

Definition subtype_ty P := subtype_ty' (subtyping' P).
Definition subtype_structural P := subtype_structural' (subtyping' P).
