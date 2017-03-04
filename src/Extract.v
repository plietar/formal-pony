Require Import Eval.
Require Import Semantics.
Require Import Entities.

Require Import Coq.Strings.String.
Require Import Coq.extraction.ExtrHaskellBasic.
Require Import Coq.extraction.ExtrHaskellString.
Require Import Coq.extraction.ExtrHaskellNatInteger.

Definition init : heap * frame :=
    let h := Heap.empty in
    let f := Frame.empty in

    let (h', addr) := Heap.create h "Foo" in
    let f' := Frame.set f (SourceId "x") (v_addr addr) in

    (h', f').

Extraction Language Haskell.
Cd "out".
Separate Extraction init eval.
Cd "..".
