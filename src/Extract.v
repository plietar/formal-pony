Require Import Eval.
Require Import Ast.
Require Import common.
(*Require Import Semantics.*)
Require Import checker.
Require Import Entities.
Require Import ch2o.prelude.base.
Require Import ch2o.prelude.stringmap.
Require Import ch2o.prelude.nmap.
Require Import ch2o.prelude.pmap.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.extraction.ExtrHaskellBasic.
Require Import Coq.extraction.ExtrHaskellString.
Require Import Coq.extraction.ExtrHaskellNatInteger.
Require Import Coq.NArith.BinNatDef.

Definition init : heap * list frame * ty_ctx :=
    let f := {|
      method := "<interactive>";
      locals := empty;
      hole := expr_hole_id
    |} in

    (empty, f::nil, empty).

Definition N_to_nat := N.to_nat.
Definition P_to_nat := Pos.to_nat.

Definition heap_to_list (h: heap): list (nat * object) :=
    fmap (prod_map N.to_nat id) (map_to_list h).

Definition fields_to_list (m: stringmap value): list (string * value) :=
    map_to_list m.

Extraction Language Haskell.
Set Extraction KeepSingleton.

Extract Inlined Constant trace => "Debug.Trace.traceShow".
Extract Inlined Constant traceId => "Debug.Trace.traceShowId".

Extraction "main/Extracted.pre.hs"
    init eval ck_expr ty_ctx
    frame local_id
    heap_to_list fields_to_list
    N_to_nat P_to_nat
    Nto_list Pto_list
    stringmap_to_list
    list_expr_coerce
    list_expr_uncoerce
    ty wf_program.

