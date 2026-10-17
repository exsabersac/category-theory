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

(** ** (1) The mate computes; the covariant lemma's term is not it

    Positive controls: the action is [eq_refl], and the two agree up to
    [≈]. *)

Check (fun (d : D) (k : r ~{D}~> d) =>
         eq_refl : transform (ue_mate H r (@aue_elem D H r U)) d k
                     = fmap[H] k (@aue_elem D H r U)).

Check (ue_mate_covariant H r (@aue_elem D H r U)).
Check (ue_mate_is_transform H r U).

(** Negative: the covariant Yoneda lemma's mate is not the same TERM.
    (Stripped: cannot unify [(Covariant_Yoneda_Lemma D H r)⁻¹ aue_elem] and
    [ue_mate H r aue_elem].) *)
Fail Check (eq_refl : from (Covariant_Yoneda_Lemma D H r) (@aue_elem D H r U)
                        = ue_mate H r (@aue_elem D H r U)).

(** Negative: nor is the hand-built transformation.  (Stripped: cannot
    unify [ue_mate H r aue_elem] and [ue_transform H r U].) *)
Fail Check (eq_refl : ue_mate H r (@aue_elem D H r U) = ue_transform H r U).

(** ** (2) The Yoneda passage preserves the element, not the record

    Positive controls: the isomorphism exists, and the element survives
    both round trips by [eq_refl]. *)

Check (universal_element_yoneda H r
         : @Isomorphism Sets
             (Build_SetoidObject (AUniversalElement H r)
                (AUniversalElementEquiv H r))
             (ue_yoneda_obj H r)).

Check (ue_yoneda_round_ue H r U).
Check (fun (x : H r) (I : IsIsomorphism (ue_mate H r x)) =>
         ue_yoneda_round_elem H r x I).

(** Positive control that the naming of the sigma setoid changed nothing:
    [ue_yoneda_obj] IS [representability_by_yoneda]'s source, the
    [exists_setoid] instance included. *)
Check (rby_agrees H r).

(** Negative: the whole record does not survive — [AUniversalElement_of_mate]
    rebuilds the factorization data.  (Stripped: cannot unify
    [ue_of_yoneda H r (ue_to_yoneda H r U)] and [U].) *)
Fail Check (eq_refl : ue_of_yoneda H r (ue_to_yoneda H r U) = U).

(** ** (3) The 3(b) passage IS a record-level bijection, and still not a
       renaming

    Positive controls: both round trips close by [eq_refl] on the WHOLE
    record, and the two clauses are literally the same clause. *)

Check (fun (C : Category) (S : D ⟶ C) (c : C) (a : D)
           (V : AUniversalArrow c S a) => aua_of_hom_round S c V).

Check (fun (C : Category) (S : D ⟶ C) (c : C) (a : D)
           (V : AUniversalElement (HomAfter S c) a) => aue_of_hom_round S c V).

Check (fun (C : Category) (S : D ⟶ C) (c : C) (d d' : D)
           (k : d ~{D}~> d') (u : c ~{C}~> S d) => hom_after_fmap S c d d' k u).

(** Negative: the two types are nonetheless distinct, so the passages are
    constructions and not coercions.  (Stripped: cannot unify
    [AUniversalElement (HomAfter S c) r] and [AUniversalArrow c S r].) *)
Fail Check (fun (C : Category) (S : D ⟶ C) (c : C) =>
              eq_refl : AUniversalElement (HomAfter S c) r
                          = AUniversalArrow c S r).

(** ** (4) The 3(a) passage: element on the nose, arrow up to [≈]

    Positive controls. *)

Check (aue_aua_round H r U).
Check (fun V : AUniversalArrow SetsOne H r => aua_aue_round H r V).
Check (fun V : AUniversalArrow SetsOne H r => aue_of_aua_elem H r V).
Check (aua_of_aue_arrow H r U).

(** Negative: the arrow does NOT survive by [eq_refl] — [global_element]
    rebuilds it from its value at [ttt].  (Stripped: cannot unify the two
    [universal_arrow] terms.) *)
Fail Check (fun V : AUniversalArrow SetsOne H r =>
              eq_refl
                : @universal_arrow _ _ SetsOne H r
                    (AUniversalArrow_of_AUniversalElement H r
                       (AUniversalElement_of_AUniversalArrow H r V))
                    = @universal_arrow _ _ SetsOne H r V).

End Probes.

(** ** (5) The Yoneda route's universe restriction

    Positive control, and the whole point of the direct route: at
    [Endos] — whose objects sit strictly above its homs — the general
    class is inhabited, the universal element is [O], and Riehl's initial
    object of the category of elements exists. *)

Check (nat_UniversalElement : UniversalElement Endos_Forget).
Check (@eq_refl nat (@ue_elem Endos Endos_Forget nat_UniversalElement)
         : @ue_elem Endos Endos_Forget nat_UniversalElement = O).
Check (nat_Elements_Initial : @Initial (Elements Endos_Forget)).

(** Positive control on the donor side: [representability_by_yoneda] and
    [Yoneda_Lemma] do exist and do apply — at a category whose three
    universes coincide. *)

Check (fun (C : Category@{Set Set Set}) (F : C^op ⟶ Sets) (c : C) =>
         representability_by_yoneda C F c).

(** Negative: neither can be instantiated at [Endos].  These are UNIVERSE
    INCONSISTENCIES, not unification failures.  Stripped, each reports
    that [Endos] (resp. [Endos^op]) "has type Category@{a b b} while it is
    expected to have type Category@{c c c}", followed by "universe
    inconsistency: Cannot enforce a = b" -- i.e. the donor's identification
    of the object and hom universes is exactly what is refused.  [@] is used
    throughout so that no implicit argument can make a command fail for an
    unrelated reason; the instrument itself was checked separately, and
    note that a naive exhibit such as [Fail Check (@eq_refl nat 0 : 0 = 0)]
    would NOT test it -- [0] is [initial_obj] in [object_scope], so that
    command fails with "No interpretation for number 0" and the [Fail]
    passes for the wrong reason. *)

Fail Check (fun c : Endos =>
              @universal_element_representation Endos Endos_Forget c).

Fail Check (fun c : Endos => @Yoneda_Lemma (Endos^op) Endos_Forget c).

(** ... and so the Yoneda-composed accessor cannot produce the witness that
    the direct one does.  (Stripped: the same universe inconsistency.) *)

Fail Check (@universal_element_of_representation Endos Endos_Forget NatSucc
              (@represented Endos Endos_Forget nat_succ_Representable)).

(** Positive control, immediately: the direct accessor DOES.  This is the
    pair that makes the restriction a measured fact about the two routes
    rather than a claim about one. *)

Check (@AUniversalElement_of_repr Endos Endos_Forget NatSucc
         (@represented Endos Endos_Forget nat_succ_Representable)
         : AUniversalElement Endos_Forget NatSucc).
