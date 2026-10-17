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

(* 相关说明。 （已译） *)

Section IndexAboveHoms.

Universes uo uh ua.
Constraint uh < ua.

Context (C : Category@{uo uh uh}) (A : Type@{ua}) (f : A -> C).

(* Positive control 1: TARGET 函子 alone accepts large index —
 对象 action fresh dependent-function setoid, lifts. （已译） *)
Check (iprod_hom_functor f).

(* Positive control 2: the coproduct-side target functor likewise. *)
Check (icoprod_hom_functor f).

(* Positive control 3: SOURCE 函子 formable at 范畴, so
 neither half comparison what gets rejected. （已译） *)
Check (fun q : C => fobj[Curried_CoHom C] q).

(* Negative 1: comparison map itself not formable — two 函子
 have live ONE [Sets], hom-函子 pins [Sets]' carrier
 universe [C]'s hom universe. （已译） *)
Fail Check (fun (q : C) (proj : forall a : A, q ~> f a) =>
              @iprod_hom_transform C A f q proj).

(* Negative 2: hence neither is the isomorphism. *)
Fail Check (fun (q : C) (proj : forall a : A, q ~> f a)
                (H : @IsIndexedProduct C A f q proj) =>
              @iprod_hom_iso C A f q proj H).

(* 相关说明。 （已译） *)
Fail Check (fun (p : C) (inj : forall a : A, f a ~> p) =>
              @icoprod_hom_transform C A f p inj).

End IndexAboveHoms.

(* 相关说明。 （已译） *)

Section LimitShapeIndex.

Universes uo ub.
Constraint Set < ub.

(*
   本节说明（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Context (C : Category@{uo Set Set}) (A : Type@{ub}) (f : A -> C).

(* 相关说明。 （已译） *)
Check (Limit (DiscreteCat_Functor f)).

(* Positive control 5: so is the product object read off it. *)
Check (fun L : Limit (DiscreteCat_Functor f) => @iprod C A f L).

(* 相关说明。 （已译） *)
Fail Check (fun L : Limit (DiscreteCat_Functor f) => @limit_hom_iso C A f L).

(* Negative 5: dually. *)
Fail Check (fun L : Limit (@DiscreteCat_Functor A (C^op) f) =>
              @colimit_hom_iso C A f L).

End LimitShapeIndex.

(* 相关说明。 （已译） *)

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

(* 相关说明。 （已译） *)
Definition probe_to_control :
  to (iprod_hom_iso H) = iprod_hom_transform f q proj := eq_refl.

(* 相关说明。 （已译） *)
Definition probe_from_control :
  transform (from (iprod_hom_iso H)) c fam = unique_obj (iprod_desc H fam)
  := eq_refl.

(* 相关说明。 （已译） *)
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

(* 相关说明。 （已译） *)
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

(* 相关说明。 （已译） *)
Definition probe_sets_roundtrip_value_control (x : c) :
  transform (from (Sets_iprod_hom_iso F)) c
    (transform (to (Sets_iprod_hom_iso F)) c u) x = u x := eq_refl.

End ConversionSets.
