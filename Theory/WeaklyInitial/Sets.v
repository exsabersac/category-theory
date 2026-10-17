Require Import Category.Lib.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Theory.WeaklyInitial.

Generalizable All Variables.

(*
   本文件给出集合相关实例或构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Sets_initial_characterization :
  @Initial Sets ↔ WeaklyInitialFamily Sets :=
  initial_iff_weakly_initial_family_complete Sets_Complete Sets_HasEqualizers.

(* The round trip: the initial object, as a singleton family, through
   Freyd's construction, back to an initial object. *)
Definition Sets_wif : WeaklyInitialFamily Sets :=
  fst Sets_initial_characterization Sets_Initial.

Definition Sets_initial_recovered : @Initial Sets :=
  snd Sets_initial_characterization Sets_wif.

Definition Sets_roundtrip_iso :
  @initial_obj Sets Sets_initial_recovered ≅ @initial_obj Sets Sets_Initial :=
  initial_unique Sets_initial_recovered Sets_Initial.

(* The family is the singleton at the empty set, on the nose. *)
Example Sets_wif_index : wif_index Sets_wif = poly_unit := eq_refl.

Example Sets_wif_obj (u : poly_unit) :
  wif_obj Sets_wif u = @initial_obj Sets Sets_Initial := eq_refl.
