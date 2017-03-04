Require Import Eval.
Require Import Semantics.

Require Import Coq.extraction.ExtrHaskellBasic.
Require Import Coq.extraction.ExtrHaskellString.
Require Import Coq.extraction.ExtrHaskellNatInteger.

Definition init : heap * frame :=
    (Heap.empty, Frame.empty).

Extraction Language Haskell.
Cd "out".
Separate Extraction init eval.
Cd "..".
