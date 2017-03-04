(*Require Import Ast.*)

Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Strings.String.

Require Import Coq.Structures.Equalities.
Require Import Coq.Arith.EqNat.

Require Import Ast.
Require Import Semantics.
Require Import Store.

Fixpoint eval (f: frame) (e: expr) : frame * nat :=
  match e with
  | expr_temp t => (f, t)

  | expr_recover e' => eval f e'
  | expr_local name =>
      let t := Frame.alloc_temp f in
      let f' := Frame.set f (TempId t) (Frame.get f (SourceId name)) in
      (f', t)

  | expr_assign_local name e =>
      let (f', t) := eval f e in
      let t' := Frame.alloc_temp f' in
      let f'' := Frame.set f' (TempId t') (Frame.get f' (SourceId name)) in
      let f''' := Frame.set f'' (SourceId name) (Frame.get f' (TempId t)) in
      (f''', t')

  | expr_seq e1 e2 =>
      let (f', _) := eval f e1
      in eval f' e2
  end.

Theorem eval_step: forall f e f' t,
  (eval f e = (f', t) -> f / e ==>* f' / expr_temp t).
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

