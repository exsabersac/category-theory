Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Classes.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Localization.

Generalizable All Variables.

(*
   本文件给出泛构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Set Default Proof Using "All".

(*
   nLab: https://ncatlab.org/nlab/show/reflective+subcategory
   https://ncatlab.org/nlab/show/localization
   https://ncatlab.org/nlab/show/orthogonal+subcategory

   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Universal.

Context {C : Category}.
Context {W : MorphismClass C}.
Context (R : Reflective (C_W W)).
Context {E : Category}.

(* Parse-time abbreviations, matching Localization.v's [Section Inverts], so
 every 伴随-transpose 引理 instance stays same syntactic form
 goal. （已译） *)
Local Notation Su   := (Sub C (C_W W)).
Local Notation Iota := (Incl C (C_W W)).
Local Notation Refl := (reflector R).
Local Notation A    := (reflective_adj R).

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma reflection_unit_naturality {c c' : C} (f : c ~> c') :
  fmap[Iota] (fmap[Refl] f)
    ∘ @Category.Theory.Adjunction.unit Su C Refl Iota A c
    ≈ @Category.Theory.Adjunction.unit Su C Refl Iota A c' ∘ f.
Proof.
  unfold Category.Theory.Adjunction.unit.
  rewrite <- (@to_adj_nat_l Su C Refl Iota A).
  rewrite id_left.
  rewrite <- (@to_adj_nat_r Su C Refl Iota A).
  now rewrite id_right.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma reflection_counit_is_iso (x : Su) :
  IsIsomorphism (@counit Su C Refl Iota A x).
Proof.
  unshelve refine {| two_sided_inverse := _
                   ; is_right_inverse := _
                   ; is_left_inverse := _ |}.
  - exists (@Category.Theory.Adjunction.unit Su C Refl Iota A (Iota x)).
    apply (reflective_full R).
  - apply (@fmap_counit_unit Su C Refl Iota A x).
  - rewrite <- (counit_naturality A).
    apply (@counit_fmap_unit Su C Refl Iota A (Iota x)).
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma reflection_retract : Refl ◯ Iota ≈ Id[Su].
Proof.
  exists (fun x => IsIsoToIso _ (reflection_counit_is_iso x)).
  intros x y f.
  destruct (reflection_counit_is_iso y) as [invy Hry Hly].
  change (fmap[Refl ◯ Iota] f) with (fmap[Refl] (fmap[Iota] f)).
  change (fmap[Id[Su]] f) with f.
  cbn [IsIsoToIso to from two_sided_inverse].
  rewrite <- (id_left (fmap[Refl] (fmap[Iota] f))).
  rewrite <- Hly.
  rewrite <- comp_assoc.
  rewrite (counit_naturality A f).
  now rewrite comp_assoc.
Qed.

Context (G : C ⟶ E).

(* G sends every W-map to an isomorphism (the localizing hypothesis). *)
Context (GW : ∀ (a b : C) (w : a ~> b), W a b w → IsIsomorphism (fmap[G] w)).

(* 相关说明。 （已译） *)
Context (Hunit : ∀ c : C,
           W c (Iota (Refl c))
             (@Category.Theory.Adjunction.unit Su C Refl Iota A c)).

(* Consequently G inverts every reflection unit — exact content the
 factorization 所消耗. （已译） *)
Lemma G_inverts_unit (c : C) :
  IsIsomorphism
    (fmap[G] (@Category.Theory.Adjunction.unit Su C Refl Iota A c)).
Proof. exact (GW _ _ _ (Hunit c)). Qed.

(* Factorization: whiskered 单位 G ∘ η is natural 同构
 G ⟹ (G ◯ Iota) ◯ Refl. Componentwise it is [fmap[G] η_c], invertible by
 [G_inverts_unit]; 融贯性 square is [reflection_unit_naturality]
 transported through G.（已译） *)
Lemma localization_factors : G ≈ (G ◯ Iota) ◯ Refl.
Proof.
  exists (fun c => IsIsoToIso _ (G_inverts_unit c)).
  intros c c' f.
  destruct (G_inverts_unit c') as [ug Hrg Hlg].
  change (fmap[(G ◯ Iota) ◯ Refl] f)
    with (fmap[G] (fmap[Iota] (fmap[Refl] f))).
  cbn [IsIsoToIso to from two_sided_inverse].
  (* The whiskered unit naturality, transported through G. *)
  assert (KEY : fmap[G] (fmap[Iota] (fmap[Refl] f))
                  ∘ fmap[G] (@Category.Theory.Adjunction.unit Su C Refl Iota A c)
                ≈ fmap[G] (@Category.Theory.Adjunction.unit Su C Refl Iota A c')
                  ∘ fmap[G] f).
  { rewrite <- !(@fmap_comp _ _ G).
    apply fmap_respects, (reflection_unit_naturality f). }
  rewrite <- comp_assoc.
  rewrite KEY.
  rewrite comp_assoc.
  rewrite Hlg.
  now rewrite id_left.
Qed.

(* The 普遍性质: G factors through reflector L = Refl, uniquely
 up natural 同构. The witnessing 函子 restriction
 G' := G ◯ Iota. （已译） *)
Theorem localization_universal :
  { G' : Su ⟶ E
  & (G ≈ G' ◯ Refl) *
    (∀ H : Su ⟶ E, G ≈ H ◯ Refl → H ≈ G') }.
Proof.
  exists (G ◯ Iota).
  split.
  - exact localization_factors.
  - intros H HeqG.
    rewrite HeqG.
    rewrite <- fun_equiv_comp_assoc.
    rewrite reflection_retract.
    now rewrite fun_equiv_id_right.
Qed.

End Universal.
