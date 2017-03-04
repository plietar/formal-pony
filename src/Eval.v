(*Require Import Ast.*)

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Strings.String.

Require Import Coq.Structures.Equalities.
Require Import Coq.Arith.EqNat.

Require Import Ast.
Require Import Semantics.
Require Import Entities.
Require Import Store.

Fixpoint eval (h: heap) (f: frame) (e: expr) : heap * frame * nat :=
  match e with
  | expr_temp t => (h, f, t)

  | expr_recover e' => eval h f e'
  | expr_local name =>
      let t := Frame.alloc_temp f in
      let f' := Frame.set f (TempId t) (Frame.get f (SourceId name)) in
      (h, f', t)

  | expr_assign_local name e =>
      let '(h', f', t) := eval h f e in
      let t' := Frame.alloc_temp f' in
      let f'' := Frame.set f' (TempId t') (Frame.get f' (SourceId name)) in
      let f''' := Frame.set f'' (SourceId name) (Frame.get f' (TempId t)) in
      (h', f''', t')

  | expr_field e name =>
      let '(h', f', t) := eval h f e in
      match Frame.get f' (TempId t) with
      | v_addr addr =>
        let t' := Frame.alloc_temp f' in
        let value := Heap.get_field h' addr name in
        let f'' := Frame.set f' (TempId t') value in

        (h', f'', t')
      | v_null => (h', f', t)
      end

  | expr_assign_field e name e' =>
      let '(h', f', t) := eval h f e in
      let '(h'', f'', t') := eval h' f' e' in

      match Frame.get f'' (TempId t) with
      | v_addr addr =>
        let t''' := Frame.alloc_temp f'' in
        let old_value := Heap.get_field h'' addr name in
        let value := Frame.get f'' (TempId t') in

        let h''' := Heap.set_field h'' addr name value in
        let f''' := Frame.set f'' (TempId t''') old_value in

        (h''', f''', t''')
      | v_null => (h'', f'', t)
      end

  | expr_seq e1 e2 =>
      let '(h', f', _) := eval h f e1
      in eval h' f' e2
  end.

Theorem eval_step: forall h h' f f' e t,
  (eval h f e = (h', f', t) -> h / f / e ==>* h' / f' / expr_temp t).
Admitted.

(*
Proof.
intros f e.
generalize dependent f.
induction e.
+ intros.
  simpl in H.
  inversion H.
  symmetry in H1.
  symmetry in H2.
  rewrite H1.
  rewrite H2.
  apply multi_refl.

+ intros.
  simpl in H.
  remember (eval f e1) as E.
  symmetry in HeqE.
  destruct E.

  apply multi_concat with (f2 := f0) (e2 := (expr_seq (expr_temp n) e2)).
  - apply E_SeqN.
    apply IHe1.
    exact HeqE.
  - apply multi_trans with (f2 := f0) (e2 := e2).
    * apply E_Seq.
    * apply IHe2.
      exact H.

+ intros.
  simpl in H.
  apply multi_concat with (f2 := f') (e2 := expr_recover (expr_temp t)).
  - apply E_RecoverN.
    apply IHe.
    exact H.
  - apply multi_one.
    apply E_Recover.

+ intros.
  simpl in H.
  inversion H.
  apply multi_one.
  apply E_Local.
  reflexivity.
  reflexivity.

+ intros.
  simpl in H.
  remember (eval f e) as E.
  symmetry in HeqE.
  destruct E.
  apply multi_concat with (f2 := f0) (e2 := expr_assign_local s (expr_temp n)).
  - apply E_Asn_LocalN.
    apply IHe.
    exact HeqE.

  - apply multi_one.
    inversion H.
    apply E_Asn_Local.
    * reflexivity.
    * reflexivity.

Qed.
*)
