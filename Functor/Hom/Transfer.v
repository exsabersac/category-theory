Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Functor.Hom.

Generalizable All Variables.

(* * * Mac Lane §IV.3's transfer 引理: representable transformations （已译） *)

(*
   本文件给出 hom 形式的伴随/同态。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Transfer.

Context {A : Category}.

(* ** The induced transformation *)

(* Mac Lane's f*: precomposition f, natural second variable
 because 复合 associative. （已译） *)

Program Definition hom_transfer {a b : A} (f : b ~> a) :
  [Hom a ,─] ⟹ [Hom b ,─] := {|
  transform := fun c => {| morphism := fun h => h ∘ f |}
|}.

(* The component's value, at Leibniz equality. Deliberate strictness:
 这是 one file's two uses [=] 态射, it an
 acceptance test rather than mathematical claim. （已译） *)

Example hom_transfer_component {a b : A} (f : b ~> a) (c : A)
        (h : a ~> c) : transform[hom_transfer f] c h = h ∘ f := eq_refl.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example hom_transfer_is_fmap_value {a b : A} (f : b ~> a) (c : A)
        (h : a ~> c) :
  transform[hom_transfer f] c h
    = transform[fmap[Curried_Hom A] (f : a ~{Opposite A}~> b)] c h
  := eq_refl.

Lemma hom_transfer_is_fmap {a b : A} (f : b ~> a) :
  hom_transfer f
    ≈[[A, Sets]] fmap[Curried_Hom A] (f : a ~{Opposite A}~> b).
Proof. intros c h; reflexivity. Qed.

(* 相关说明。 （已译） *)

Lemma hom_transfer_at_id {a b : A} (f : b ~> a) :
  transform[hom_transfer f] a id ≈ f.
Proof. exact (id_left f). Qed.

(* ** Mac Lane's lemma, first half: monic ⟺ epi *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem hom_transfer_monic_iff_epic {a b : A} (f : b ~> a) :
  @Monic ([A, Sets]) _ _ (hom_transfer f) ↔ Epic f.
Proof.
  split.
  - intros Hm.
    constructor; intros c g1 g2 Heq.
    exact (snd (injectivity_is_monic (transform[hom_transfer f] c))
               (sets_functor_monic_pointwise (hom_transfer f) Hm c)
               g1 g2 Heq).
  - intros He.
    apply pointwise_monic_is_monic; intro c.
    apply (fst (injectivity_is_monic (transform[hom_transfer f] c))).
    intros g1 g2 Heq.
    exact (@epic A _ _ f He c g1 g2 Heq).
Defined.

(* ** Mac Lane's lemma, second half: epi ⟺ split monic *)

(*
   本节说明 Transfer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem hom_transfer_epic_iff_section {a b : A} (f : b ~> a) :
  @Epic ([A, Sets]) _ _ (hom_transfer f) ↔ Section f.
Proof.
  split.
  - intros He.
    destruct (epic_implies_surjective
                (transform[hom_transfer f] b)
                (sets_functor_epic_pointwise (hom_transfer f) He b)
                (id[b])) as [s Hs].
    exact {| section := s ; section_comp := Hs |}.
  - intros Hs.
    apply pointwise_epic_is_epic; intro c.
    apply (fst (surjectivity_is_epic (transform[hom_transfer f] c))).
    intro k.
    exists (k ∘ @section A b a f Hs).
    change ((k ∘ @section A b a f Hs) ∘ f ≈ k).
    rewrite <- comp_assoc.
    rewrite (@section_comp A b a f Hs).
    exact (id_right k).
Defined.

(*
   本节说明 Transfer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition epic_of_hom_transfer_monic {a b : A} (f : b ~> a) :
  @Monic ([A, Sets]) _ _ (hom_transfer f) → Epic f :=
  fst (hom_transfer_monic_iff_epic f).

Definition hom_transfer_monic_of_epic {a b : A} (f : b ~> a) :
  Epic f → @Monic ([A, Sets]) _ _ (hom_transfer f) :=
  snd (hom_transfer_monic_iff_epic f).

Definition section_of_hom_transfer_epic {a b : A} (f : b ~> a) :
  @Epic ([A, Sets]) _ _ (hom_transfer f) → Section f :=
  fst (hom_transfer_epic_iff_section f).

Definition hom_transfer_epic_of_section {a b : A} (f : b ~> a) :
  Section f → @Epic ([A, Sets]) _ _ (hom_transfer f) :=
  snd (hom_transfer_epic_iff_section f).

(*
   本节说明 Transfer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma hom_transfer_component_injective_iff {a b : A} (f : b ~> a)
      (c : A) :
  (∀ g1 g2 : a ~> c, g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2)
    ↔ Monic (transform[hom_transfer f] c).
Proof. exact (injectivity_is_monic (transform[hom_transfer f] c)). Defined.

Lemma hom_transfer_component_surjective_iff {a b : A} (f : b ~> a)
      (c : A) :
  (∀ k : b ~> c, ∃ g : a ~> c, g ∘ f ≈ k)%type
    ↔ Epic (transform[hom_transfer f] c).
Proof. exact (surjectivity_is_epic (transform[hom_transfer f] c)). Defined.

End Transfer.
