Require Import Ast.
Require Import ch2o.prelude.stringmap.
Require Import ch2o.prelude.base.
Require Import ch2o.prelude.list.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Sumbool.
Require Import common.
Require Import subtyping.
Open Scope string_scope.

Definition ty_ctx := stringmap ty.

Class Viewpoint (A B C: Type) := adapt_viewpoint: A -> B -> option C.
Notation "a ▷ b" := (adapt_viewpoint a b) (at level 60, right associativity) : C_scope.

Class ExtractViewpoint (A B C: Type) := extract_viewpoint: A -> B -> option C.
Notation "a ▶ b" := (extract_viewpoint a b) (at level 60, right associativity) : C_scope.

Class Alias (A: Type) := alias: A -> A.
Class Unalias (A: Type) := unalias: A -> A.

Instance viewpoint_cap: Viewpoint ecap cap ecap := {
  adapt_viewpoint a b := match a, b with
  | cap_iso_eph, cap_iso => Some cap_iso_eph
  | cap_iso_eph, cap_trn => Some cap_iso_eph
  | cap_iso_eph, cap_ref => Some cap_iso_eph
  | cap_iso_eph, cap_val => Some (ecap_cap cap_val)
  | cap_iso_eph, cap_box => Some (ecap_cap cap_val)

  | cap_iso, cap_iso => Some (ecap_cap cap_iso)
  | cap_iso, cap_trn => Some (ecap_cap cap_iso)
  | cap_iso, cap_ref => Some (ecap_cap cap_iso)
  | cap_iso, cap_val => Some (ecap_cap cap_val)
  | cap_iso, cap_box => Some (ecap_cap cap_tag)

  | cap_trn_eph, cap_iso => Some cap_iso_eph
  | cap_trn_eph, cap_trn => Some cap_trn_eph
  | cap_trn_eph, cap_ref => Some cap_trn_eph
  | cap_trn_eph, cap_val => Some (ecap_cap cap_val)
  | cap_trn_eph, cap_box => Some (ecap_cap cap_val)

  | cap_trn, cap_iso => Some (ecap_cap cap_iso)
  | cap_trn, cap_trn => Some (ecap_cap cap_trn)
  | cap_trn, cap_ref => Some (ecap_cap cap_trn)
  | cap_trn, cap_val => Some (ecap_cap cap_val)
  | cap_trn, cap_box => Some (ecap_cap cap_box)

  | cap_ref, cap_iso => Some (ecap_cap cap_iso)
  | cap_ref, cap_trn => Some (ecap_cap cap_trn)
  | cap_ref, cap_ref => Some (ecap_cap cap_ref)
  | cap_ref, cap_val => Some (ecap_cap cap_val)
  | cap_ref, cap_box => Some (ecap_cap cap_box)

  | cap_val, cap_iso => Some (ecap_cap cap_val)
  | cap_val, cap_trn => Some (ecap_cap cap_val)
  | cap_val, cap_ref => Some (ecap_cap cap_val)
  | cap_val, cap_val => Some (ecap_cap cap_val)
  | cap_val, cap_box => Some (ecap_cap cap_val)

  | cap_box, cap_iso => Some (ecap_cap cap_tag)
  | cap_box, cap_trn => Some (ecap_cap cap_box)
  | cap_box, cap_ref => Some (ecap_cap cap_box)
  | cap_box, cap_val => Some (ecap_cap cap_val)
  | cap_box, cap_box => Some (ecap_cap cap_box)

  | cap_tag, _ => None
  | _, cap_tag => Some (ecap_cap cap_tag)
  end
}.

Instance extract_viewpoint_cap: ExtractViewpoint ecap cap ecap := {
  extract_viewpoint a b := match a, b with
  | cap_iso_eph, cap_iso => Some cap_iso_eph
  | cap_iso_eph, cap_trn => Some cap_iso_eph
  | cap_iso_eph, cap_ref => Some cap_iso_eph
  | cap_iso_eph, cap_val => Some (ecap_cap cap_val)
  | cap_iso_eph, cap_box => Some (ecap_cap cap_val)

  | cap_iso, cap_iso => Some cap_iso_eph
  | cap_iso, cap_trn => Some (ecap_cap cap_val)
  | cap_iso, cap_ref => Some (ecap_cap cap_tag)
  | cap_iso, cap_val => Some (ecap_cap cap_val)
  | cap_iso, cap_box => Some (ecap_cap cap_tag)

  | cap_trn_eph, cap_iso => Some cap_iso_eph
  | cap_trn_eph, cap_trn => Some cap_trn_eph
  | cap_trn_eph, cap_ref => Some cap_trn_eph
  | cap_trn_eph, cap_val => Some (ecap_cap cap_val)
  | cap_trn_eph, cap_box => Some (ecap_cap cap_val)

  | cap_trn, cap_iso => Some cap_iso_eph
  | cap_trn, cap_trn => Some (ecap_cap cap_val)
  | cap_trn, cap_ref => Some (ecap_cap cap_box)
  | cap_trn, cap_val => Some (ecap_cap cap_val)
  | cap_trn, cap_box => Some (ecap_cap cap_box)

  | cap_ref, cap_iso => Some cap_iso_eph
  | cap_ref, cap_trn => Some cap_trn_eph
  | cap_ref, cap_ref => Some (ecap_cap cap_ref)
  | cap_ref, cap_val => Some (ecap_cap cap_val)
  | cap_ref, cap_box => Some (ecap_cap cap_box)

  | cap_val, _ => None
  | cap_box, _ => None
  | cap_tag, _ => None

  | _, cap_tag => Some (ecap_cap cap_tag)
  end
}.

Instance viewpoint_cap_ty: Viewpoint ecap ty ty := {
  adapt_viewpoint a b := match b with
  | ty_name n (ecap_cap c) =>
      c' <- a ▷ c;
      Some (ty_name n c')
  | ty_name n (ecap_iso_eph) => None
  | ty_null => Some (ty_null)
  end
}.

Instance extract_viewpoint_cap_ty: ExtractViewpoint ecap ty ty := {
  extract_viewpoint a b := match b with
  | ty_name n (ecap_cap c) =>
      c' <- a ▶ c;
      Some (ty_name n c')
  | ty_name n (ecap_iso_eph) => None
  | ty_null => Some (ty_null)
  end
}.

Instance alias_cap : Alias ecap := {
  alias a := match a with
  | cap_iso_eph => cap_iso
  | cap_trn_eph => cap_trn
  | cap_iso => cap_tag
  | cap_trn => cap_box
  | cap_ref => cap_ref
  | cap_val => cap_val
  | cap_box => cap_box
  | cap_tag => cap_tag
  end
}.

Instance unalias_cap : Unalias ecap := {
  unalias a := match a with
  | cap_iso_eph => cap_iso_eph
  | cap_trn_eph => cap_trn_eph
  | cap_iso => cap_iso_eph
  | cap_trn => cap_trn_eph
  | cap_ref => cap_ref
  | cap_val => cap_val
  | cap_box => cap_box
  | cap_tag => cap_tag
  end
}.

Instance alias_ty : Alias ty := {
  alias a := match a with
  | ty_name n c => ty_name n (alias c)
  | ty_null => ty_null
  end
}.

Instance unalias_ty : Unalias ty := {
  unalias a := match a with
  | ty_name n c => ty_name n (unalias c)
  | ty_null => ty_null
  end
}.

Section checker.
Context (P: program).

Fixpoint ck_expr (Γ: ty_ctx) (e: expr) : option ty :=
  let ck_alias (e: expr) (expected: ty) : option unit :=
    ety <- ck_expr Γ e;
    subtype_ty P ety (unalias expected)
  in

  match e with
  | expr_null => Some ty_null

  | expr_seq e1 e2 =>
      ty1 <- ck_expr Γ e1;
      ty2 <- ck_expr Γ e2;
      Some ty2

  | expr_local x => Γ !! x

  | expr_assign_local x e =>
      lhs_ty <- Γ !! x;
      _ <- ck_alias e lhs_ty;
      Some (unalias lhs_ty)

  | expr_field e f =>
      base_ty <- ck_expr Γ e;
      match base_ty with
      | ty_name ds cap =>
          field_ty <- lookup_F P ds f;
          cap ▷ field_ty
      | ty_null => None
      end

  | expr_assign_field e f e' =>
      base_ty <- ck_expr Γ e;
      match base_ty with
      | ty_name ds cap =>
          field_ty <- lookup_F P ds f;
          _ <- ck_alias e' field_ty;
          cap ▶ field_ty
      | ty_null => None
      end

  | expr_ctor kt k es =>
      '(_, args, retty) <- lookup_Md P kt k;
      _ <- ck_args Γ es (map snd args);

      Some retty

  | expr_call e0 m es =>
      baset <- ck_expr Γ e0;
      match baset with
      | ty_name ds cap =>
          '(_, args, retty) <- lookup_Md P ds m;
          _ <- ck_args Γ es (map snd args);

          Some retty
      | ty_null => None
      end

  | _ => None
  end
with
  ck_args (Γ: ty_ctx) (es: list_expr) (args: list ty) : option unit :=
    let ck_alias (e: expr) (expected: ty) : option unit :=
      ety <- ck_expr Γ e;
      subtype_ty P ety (unalias expected)
    in

    match es, args with
    | list_expr_nil, nil => Some ()
    | list_expr_cons e es', arg :: args' =>
        _ <- ck_alias e arg;
        ck_args Γ es' args'
    | _, _ => None
    end
.

Definition wf_method (name: string) (receiver: ty) (args_ty: list (string * ty)) (ret_ty: ty) (body: expr) : option unit :=
  let Γ : ty_ctx := map_of_list (("this", receiver)::args_ty) in
  body_ty <- ck_expr Γ body;
  subtype_ty P body_ty ret_ty.

Definition wf_ctor (ds: string) (kt: ctor) : option unit :=
  let '(k, (args_ty, body)) := kt in
  let receiver := ty_name ds cap_ref in
  wf_method k receiver args_ty receiver body.

Definition wf_func (ds: string) (mt: func) : option unit :=
  let '(m, (recv_cap, args_ty, ret_ty, body)) := mt in
  let receiver := ty_name ds recv_cap in
  wf_method m receiver args_ty ret_ty body.

Definition wf_class (ct : class) : option unit :=
  let '(ds, (fs, ks, ms, is)) := ct in
  _ <- mapM (wf_ctor ds) ks;
  _ <- mapM (wf_func ds) ms;
  Some ().

Definition wf_actor (cl : actor) : option unit := None.

Definition wf_program : option unit :=
  let '(nts, sts, cts, ats) := P in
  _ <- mapM wf_class cts;
  _ <- mapM wf_actor ats;
  Some ().

End checker.
