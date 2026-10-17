(*
   本文件为测试：ProbeIndexedHom。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Indexed.Hom.

Generalizable All Variables.

(** ** (1a) An index universe strictly above the ambient hom universe *)

Section IndexAboveHoms.

Universes uo uh ua.
Constraint uh < ua.

Context (C : Category@{uo uh uh}) (A : Type@{ua}) (f : A -> C).

(* Positive control 1: the TARGET functor alone accepts the large index —
   its object action is a fresh dependent-function setoid, which lifts. *)
Check (iprod_hom_functor f).

(* Positive control 2: the coproduct-side target functor likewise. *)
Check (icoprod_hom_functor f).

(* Positive control 3: the SOURCE functor is formable at this category, so
   neither half of the comparison is what gets rejected. *)
Check (fun q : C => fobj[Curried_CoHom C] q).

(* Negative 1: the comparison map itself is not formable — the two functors
   have to live in ONE [Sets], and the hom-functor pins that [Sets]' carrier
   universe to [C]'s hom universe. *)
Fail Check (fun (q : C) (proj : forall a : A, q ~> f a) =>
              @iprod_hom_transform C A f q proj).

(* Negative 2: hence neither is the isomorphism. *)
Fail Check (fun (q : C) (proj : forall a : A, q ~> f a)
                (H : @IsIndexedProduct C A f q proj) =>
              @iprod_hom_iso C A f q proj H).

(* Negative 3: the coproduct side is the same statement at [C^op] and
   inherits the same bound. *)
Fail Check (fun (p : C) (inj : forall a : A, f a ~> p) =>
              @icoprod_hom_transform C A f p inj).

End IndexAboveHoms.

(** ** (1b) The limit-shaped bridges, and why they carry [{A : Set}] *)

Section LimitShapeIndex.

Universes uo ub.
Constraint Set < ub.

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (C : Category@{uo Set Set}) (A : Type@{ub}) (f : A -> C).

(* Positive control 4: the limit shape IS formable at this large index. *)
Check (Limit (DiscreteCat_Functor f)).

(* Positive control 5: so is the product object read off it. *)
Check (fun L : Limit (DiscreteCat_Functor f) => @iprod C A f L).

(* Negative 4: the hom-set bijection at that limit is not — the group (1a)
   bound now reads "index at or below [Set]". *)
Fail Check (fun L : Limit (DiscreteCat_Functor f) => @limit_hom_iso C A f L).

(* Negative 5: dually. *)
Fail Check (fun L : Limit (@DiscreteCat_Functor A (C^op) f) =>
              @colimit_hom_iso C A f L).

End LimitShapeIndex.

(** ** (2) The round trip is not definitional *)

Section Conversion.

Context {C : Category}.
Context {A : Type}.
Context {f : A -> C}.
Context {q : C}.
Context {proj : forall a : A, q ~> f a}.
Context (H : IsIndexedProduct f q proj).
Context (c : C).
Context (u : c ~> q).
Context (fam : forall a : A, c ~> f a).

(* Positive control 6: the forward leg IS the comparison map, on the nose. *)
Definition probe_to_control :
  to (iprod_hom_iso H) = iprod_hom_transform f q proj := eq_refl.

(* Positive control 7: the backward leg's value IS the mediator named by the
   pre-existing [∃!] accessor, on the nose. *)
Definition probe_from_control :
  transform (from (iprod_hom_iso H)) c fam = unique_obj (iprod_desc H fam)
  := eq_refl.

(* Positive control 8: and the forward leg computes to restriction along the
   projections. *)
Definition probe_transform_control :
  transform (to (iprod_hom_iso H)) c u = fun a : A => proj a ∘ u := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_roundtrip :
  transform (from (iprod_hom_iso H)) c
    (transform (to (iprod_hom_iso H)) c u) = u := eq_refl.

End Conversion.

Section ConversionSets.

Context {A : Type}.
Context (F : A -> obj[Sets]).
Context (c : obj[Sets]).
Context (fam : forall a : A, c ~{Sets}~> F a).
Context (u : c ~{Sets}~> Sets_iprod_obj F).

(* Positive control 9: at [Sets] the backward leg computes to the tupling
   map of Instance/Sets/Products.v. *)
Definition probe_sets_from_control :
  transform (from (Sets_iprod_hom_iso F)) c fam = Sets_iprod_tuple F c fam
  := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_sets_roundtrip :
  transform (from (Sets_iprod_hom_iso F)) c
    (transform (to (Sets_iprod_hom_iso F)) c u) = u := eq_refl.

(* Positive control 10: the agreement holds one level further in, at the
   underlying map, so the rejection above is about the certificate field and
   not about either leg being stuck. *)
Definition probe_sets_roundtrip_value_control (x : c) :
  transform (from (Sets_iprod_hom_iso F)) c
    (transform (to (Sets_iprod_hom_iso F)) c u) x = u x := eq_refl.

End ConversionSets.
