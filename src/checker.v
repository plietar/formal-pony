Require Import Ast.
Require Import ch2o.prelude.stringmap.
Require Import ch2o.prelude.base.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Sumbool.
Require Import common.

Definition ty_ctx := stringmap ty.

Section checker.
Context (P: program).
Context (Γ: ty_ctx).

Class Viewpoint (A B: Type) := adapt_viewpoint: A -> B -> B.
Notation "a ⊳ b" := (adapt_viewpoint a b) (at level 60, right associativity) : C_scope.

Class Alias (A: Type) := alias: A -> A.
Class Subtype (A: Type) := is_subtype: A -> A -> bool.

Instance viewpoint_cap: Viewpoint cap cap := {
  adapt_viewpoint a b := match a, b with
  | cap_iso, cap_iso => cap_iso
  | cap_iso, cap_ref => cap_iso

  | cap_ref, cap_iso => cap_iso
  | cap_ref, cap_ref => cap_ref

  | _, cap_tag => cap_tag

  | cap_tag, _ => cap_tag
  end
}.

Instance viewpoint_cap_ty: Viewpoint cap ty := {
  adapt_viewpoint a b := match b with
  | ty_name n c => ty_name n (a ⊳ c)
  end
}.

Instance alias_cap : Alias cap := {
  alias a := match a with
  | cap_iso => cap_tag
  | cap_ref => cap_ref
  | cap_tag => cap_tag
  end
}.

Instance alias_ty : Alias ty := {
  alias a := match a with
  | ty_name n c => ty_name n (alias c)
  end
}.

Instance subtype_cap : Subtype cap := {
  is_subtype a b := match a, b with
  | cap_iso, cap_iso => true
  | _, cap_tag => true
  | _, _ => false
  end
}.

Instance subtype_ty : Subtype ty := {
  is_subtype a b :=
    match a, b with
    | ty_name name_a cap_a, ty_name name_b cap_b =>
        if string_dec name_a name_b
        then is_subtype cap_a cap_b
        else false
    end
}.

Fixpoint ck_expr (e: expr) : option ty :=
  match e with
  | expr_local x => Γ !! x
  | expr_field e f =>
      baset <- ck_expr e;
      match baset with
      | ty_name name cap =>
          cls <- lookup_class name P;
          fty <- lookup_field f cls;
          Some (cap ⊳ fty)
      end

  | expr_assign_local x e =>
      lhs <- Γ !! x;
      rhs <- ck_expr e;
      if is_subtype (alias rhs) lhs
      then Some lhs
      else None

  | expr_ctor name ctor_name es =>
      cls <- lookup_class name P;
      '(args, _) <- lookup_ctor ctor_name cls;
      _ <- ck_args es (map snd args);

      Some (ty_name name cap_ref)

  | expr_call e0 m es =>
      baset <- ck_expr e0;
      match baset with
      | ty_name name cap =>
          cls <- lookup_class name P;
          '(reccap, args, retty, _) <- lookup_method m cls;
          _ <- ck_args es (map snd args);

          Some retty
      end

  | _ => None
  end
with
  ck_args (es: list_expr) (args: list ty) : option unit :=
    match es, args with
    | list_expr_nil, nil => Some ()
    | list_expr_cons e es', arg :: args' =>
        ety <- ck_expr e;
        if is_subtype (alias ety) arg
        then ck_args es' args'
        else None
    | _, _ => None
    end.
End checker.
