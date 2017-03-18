Require Import ch2o.prelude.nmap.
Require Import ch2o.prelude.base.
Require Import Coq.Strings.String.

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
