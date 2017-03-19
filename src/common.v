Require Import ch2o.prelude.nmap.
Require Import ch2o.prelude.base.
Require Import Coq.Strings.String.
Require Import Coq.Init.Peano.

Notation "m >>= f" := (mbind f m) (at level 60, right associativity) : C_scope.
Notation "( m >>=)" := (λ f, mbind f m) (only parsing) : C_scope.
Notation "(>>= f )" := (mbind f) (only parsing) : C_scope.
Notation "(>>=)" := (λ m f, mbind f m) (only parsing) : C_scope.

Notation "x <- y ; z" := (y >>= (λ x : _, z))
  (at level 65, only parsing, right associativity) : C_scope.
Infix "<$>" := fmap (at level 60, right associativity) : C_scope.
Notation "' ( x1 , x2 ) <- y ; z" :=
  (y >>= (λ x : _, let ' (x1, x2) := x in z))
  (at level 65, only parsing, right associativity) : C_scope.
Notation "' ( x1 , x2 , x3 ) <- y ; z" :=
  (y >>= (λ x : _, let ' (x1,x2,x3) := x in z))
  (at level 65, only parsing, right associativity) : C_scope.
Notation "' ( x1 , x2 , x3  , x4 ) <- y ; z" :=
  (y >>= (λ x : _, let ' (x1,x2,x3,x4) := x in z))
  (at level 65, only parsing, right associativity) : C_scope.
Notation "' ( x1 , x2 , x3  , x4 , x5 ) <- y ; z" :=
  (y >>= (λ x : _, let ' (x1,x2,x3,x4,x5) := x in z))
  (at level 65, only parsing, right associativity) : C_scope.
Notation "' ( x1 , x2 , x3  , x4 , x5 , x6 ) <- y ; z" :=
  (y >>= (λ x : _, let ' (x1,x2,x3,x4,x5,x6) := x in z))
  (at level 65, only parsing, right associativity) : C_scope.

Class Zip (A: Type) (B: Type) (C: Type) := zip: list A -> B -> list (A*C).

Instance zip_list {A} {B} : Zip A (list B) B :=
  let fix z a b := match a, b with
  | ah::a', bh::b' => (ah, bh)::(z a' b')
  | nil, _ => nil
  | _, nil => nil
  end in z.

Instance zip_one {A} {B} : Zip A B B :=
  let fix z a b := match a with
  | ah::a' => (ah, b)::(z a' b)
  | nil => nil
  end in z.

Fixpoint insert_all {K: Type} {A: Type} {M: Type} {i: Insert K A M} (l: list (K*A)) (m: M) : M :=
  match l with
  | (k,a)::l' => insert_all l' (insert k a m)
  | nil => m
  end.

Definition insertZip {A: Type} {B: Type} {C: Type} {M: Type} {i: Insert A C M} {z: Zip A B C} (a: list A) (b: B)
  := insert_all (zip a b).

Notation "<[* k := a ]>" := (insertZip k a)
  (at level 5, right associativity, format "<[* k := a ]>") : C_scope.

Instance list_tuple_lookup {B} : Lookup string B (list (string * B)) := {
  lookup :=
    let fix look k l := match l with
    | (k', v)::tail => 
        if string_dec k k'
        then Some v
        else look k tail
    | nil => None
    end in look
}.

Fixpoint mapM {A B: Type} {M: Type -> Type} {r: MRet M} {b: MBind M} (f: A -> M B) (xs: list A) : M (list B) :=
  match xs with
  | x::tail => f x >>= (λ y, mapM f tail >>= (λ ys, mret (y :: ys)))
  | nil => mret nil
  end.

Fixpoint concatMapM {A B: Type} {M: Type -> Type} {r: MRet M} {b: MBind M} (f: A -> M (list B)) (xs: list A) : M (list B) :=
  match xs with
  | x::tail => f x >>= (λ y, concatMapM f tail >>= (λ ys, mret (y ++ ys)))
  | nil => mret nil
  end.

Definition trace {A B: Type} (_: A) (x: B) := x.
Definition traceId {A: Type} (x: A) := x.

Lemma pair_eq_dec' {A B: Type} `{forall x y : A, Decision (x=y)} `{forall x y : B, Decision (x=y)} : forall x y : (A*B), {x = y} + {x <> y}.
Proof.
intros.
destruct x as [x0 x1].
destruct y as [y0 y1].
destruct (decide (x0=y0)).
destruct (decide (x1=y1)).
auto with *.
auto with *.
destruct (decide (x1=y1)).
auto with *.
auto with *.
Qed.

Instance pair_eq_dec {A B: Type} `{∀ x y : A, Decision (x=y)} `{∀ x y : B, Decision (x=y)} :
  ∀ x y : A*B, Decision (x=y) := pair_eq_dec'.

Instance collection_cross_size {X Y: Type} `{Size X} `{Size Y}: Size (X*Y) :=
  fun xy => let (x,y) := xy in (size x * size y).

Instance collection_cross_elem {X Y Xs Ys: Type} `{ElemOf X Xs} `{ElemOf Y Ys}: ElemOf (X*Y) (Xs*Ys) :=
  fun xy xys =>
  let '((x,y), (xs, ys)) := (xy, xys) in x ∈ xs ∧ y ∈ ys.

Instance list_size {X: Type} : Size (list X) :=
  fun xs => Datatypes.length xs.

Definition string_beq a b := if string_dec a b then true else false.

