Require Import Eval.
Require Import Ast.
Require Import Semantics.
Require Import Entities.
Require Import ch2o.prelude.base.
Require Import ch2o.prelude.stringmap.
Require Import ch2o.prelude.nmap.

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.extraction.ExtrHaskellBasic.
Require Import Coq.extraction.ExtrHaskellString.
Require Import Coq.extraction.ExtrHaskellNatInteger.

Definition init : heap * list frame :=
    let obj := {| name := "Foo"; fields := empty |} in
    let h := empty in
    let addr : N := Nfresh h in
    let h' := <[ addr := obj ]>h in
    let f := {|
      method := "<init>";
      locals := <[ "x" := v_addr addr ]>empty;
      hole := expr_hole_id
    |} in

    (h', f::nil).

Extraction Language Haskell.
Extraction "main/Extracted.pre.hs"
    init eval frame local_id.

