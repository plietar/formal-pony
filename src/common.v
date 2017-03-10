Require Import ch2o.prelude.nmap.
Require Import ch2o.prelude.base.

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
