Require Import ch2o.prelude.nmap.
Require Import ch2o.prelude.stringmap.
Require Import ch2o.prelude.fin_map_dom.
Require Import ch2o.prelude.base.
Require Import ch2o.prelude.mapset.
Require Import Coq.Strings.String.

Inductive local_id : Type :=
| SourceId: string -> local_id
| TempId: N -> local_id.

Definition localmap (A: Type) : Type := (Nmap A * stringmap A).

Instance localmap_lookup_temp {A} : Lookup N A (localmap A) :=
  fun t m => lookup t (fst m).

Instance localmap_lookup_var {A} : Lookup string A (localmap A) :=
  fun x m => lookup x (snd m).

Instance localmap_lookup {A} : Lookup local_id A (localmap A) := {
  lookup l m := match l with
  | TempId t => lookup t m
  | SourceId x => lookup x m
  end
}.

Instance localmap_insert_temp {A} : Insert N A (localmap A) :=
  fun t v m => (insert t v (fst m), snd m).

Instance localmap_insert_var {A} : Insert string A (localmap A) :=
  fun x v m => (fst m, insert x v (snd m)).

Instance localmap_insert {A} : Insert local_id A (localmap A) := {
  insert l v m := match l with
  | TempId t => insert t v m
  | SourceId x => insert x v m
  end
}.

Instance localmap_empty A : Empty (localmap A) := (empty, empty).

Instance localmap_merge : Merge localmap :=
  fun A B C f m1 m2 => (merge f (fst m1) (fst m2), merge f (snd m1) (snd m2)).

Instance localmap_fresh_temp {A} : Fresh N (localmap A) :=
  fun m => Nfresh (fst m).

Notation localset := (mapset localmap).
Instance localmap_dom {A} : Dom (localmap A) localset := mapset_dom.
