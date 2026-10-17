(*
   本文件为测试：ProbeUniversalElement。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Construction.Elements.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Universal.Element.Elements.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Coq.Nat.
Require Import Category.Theory.Universal.Element.Examples.

Local Open Scope category_scope.

Section Probes.

Context {D : Category}.
Context {H : D ⟶ Sets}.
Context {r : D}.
Context (U : AUniversalElement H r).

(* * ** (1) The mate computes; covariant 引理's term not it

 Positive controls: action [eq_refl], two agree up to
 [≈]. （已译） *)

Check (fun (d : D) (k : r ~{D}~> d) =>
         eq_refl : transform (ue_mate H r (@aue_elem D H r U)) d k
                     = fmap[H] k (@aue_elem D H r U)).

Check (ue_mate_covariant H r (@aue_elem D H r U)).
Check (ue_mate_is_transform H r U).

(** Negative: covariant Yoneda 引理's mate not same TERM.
 (Stripped: cannot unify [(Covariant_Yoneda_Lemma D H r)⁻¹ aue_elem] and
 [ue_mate H r aue_elem].) （已译） *)
Fail Check (eq_refl : from (Covariant_Yoneda_Lemma D H r) (@aue_elem D H r U)
                        = ue_mate H r (@aue_elem D H r U)).

(** 本节：Negative: nor hand-built transformation. (Stripped: cannot
 unify [ue_mate H r aue_elem] [ue_transform H r U].) （已译） *)
Fail Check (eq_refl : ue_mate H r (@aue_elem D H r U) = ue_transform H r U).

(* * ** (2) The Yoneda passage preserves element, not record

 Positive controls: 同构 exists, element survives
 both round trips [eq_refl]. （已译） *)

Check (universal_element_yoneda H r
         : @Isomorphism Sets
             (Build_SetoidObject (AUniversalElement H r)
                (AUniversalElementEquiv H r))
             (ue_yoneda_obj H r)).

Check (ue_yoneda_round_ue H r U).
Check (fun (x : H r) (I : IsIsomorphism (ue_mate H r x)) =>
         ue_yoneda_round_elem H r x I).

(** 本节：Positive control naming sigma setoid changed nothing:
 [ue_yoneda_obj] IS [representability_by_yoneda]'s source, the
 [exists_setoid] instance included. （已译） *)
Check (rby_agrees H r).

(** 本节：Negative: whole record does not survive — [AUniversalElement_of_mate]
 rebuilds factorization data. (Stripped: cannot unify
 [ue_of_yoneda H r (ue_to_yoneda H r U)] [U].) （已译） *)
Fail Check (eq_refl : ue_of_yoneda H r (ue_to_yoneda H r U) = U).

(*
   本节说明 ProbeUniversalElement 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (fun (C : Category) (S : D ⟶ C) (c : C) (a : D)
           (V : AUniversalArrow c S a) => aua_of_hom_round S c V).

Check (fun (C : Category) (S : D ⟶ C) (c : C) (a : D)
           (V : AUniversalElement (HomAfter S c) a) => aue_of_hom_round S c V).

Check (fun (C : Category) (S : D ⟶ C) (c : C) (d d' : D)
           (k : d ~{D}~> d') (u : c ~{C}~> S d) => hom_after_fmap S c d d' k u).

(*
   本节说明 ProbeUniversalElement 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Check (fun (C : Category) (S : D ⟶ C) (c : C) =>
              eq_refl : AUniversalElement (HomAfter S c) r
                          = AUniversalArrow c S r).

(* 相关说明。 （已译） *)

Check (aue_aua_round H r U).
Check (fun V : AUniversalArrow SetsOne H r => aua_aue_round H r V).
Check (fun V : AUniversalArrow SetsOne H r => aue_of_aua_elem H r V).
Check (aua_of_aue_arrow H r U).

(** 本节：Negative: arrow does NOT survive [eq_refl] — [global_element]
 rebuilds it value at [ttt]. (Stripped: cannot unify two
 [universal_arrow] terms.) （已译） *)
Fail Check (fun V : AUniversalArrow SetsOne H r =>
              eq_refl
                : @universal_arrow _ _ SetsOne H r
                    (AUniversalArrow_of_AUniversalElement H r
                       (AUniversalElement_of_AUniversalArrow H r V))
                    = @universal_arrow _ _ SetsOne H r V).

End Probes.

(*
   本节说明Yoneda、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Check (nat_UniversalElement : UniversalElement Endos_Forget).
Check (@eq_refl nat (@ue_elem Endos Endos_Forget nat_UniversalElement)
         : @ue_elem Endos Endos_Forget nat_UniversalElement = O).
Check (nat_Elements_Initial : @Initial (Elements Endos_Forget)).

(** Positive control donor side: [representability_by_yoneda] and
 [Yoneda_Lemma] do exist do apply — at 范畴 whose three
 universes coincide. （已译） *)

Check (fun (C : Category@{Set Set Set}) (F : C^op ⟶ Sets) (c : C) =>
         representability_by_yoneda C F c).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (fun c : Endos =>
              @universal_element_representation Endos Endos_Forget c).

Fail Check (fun c : Endos => @Yoneda_Lemma (Endos^op) Endos_Forget c).

(** 本节：... so Yoneda-composed accessor cannot produce witness that
 direct one does. (Stripped: same universe inconsistency.) （已译） *)

Fail Check (@universal_element_of_representation Endos Endos_Forget NatSucc
              (@represented Endos Endos_Forget nat_succ_Representable)).

(** 本节：Positive control, immediately: direct accessor DOES. This the
 pair makes restriction measured fact about two routes
 rather than claim about one. （已译） *)

Check (@AUniversalElement_of_repr Endos Endos_Forget NatSucc
         (@represented Endos Endos_Forget nat_succ_Representable)
         : AUniversalElement Endos_Forget NatSucc).
