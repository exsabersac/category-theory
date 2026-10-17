Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Structure.Premonoidal.Monoidal.
Require Import Category.Structure.ZeroObject.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Product.Internal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.

Generalizable All Variables.

(** The fixed-factor product 函子 H × − Mac Lane's induced
 transformation "f × id". （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/product

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FixedProduct.

Context {C : Category}.
Context `{CC : @Cartesian C}.

(** ** The functor H × − *)

(* Object map G ↦ H × G, 态射 map g ↦ [second g]. The two 函子
 laws [second_id] [second_comp] no further 论元. （已译） *)
Program Definition fixed_product_functor (H : C) : C ⟶ C := {|
  fobj := fun G => H × G;
  fmap := fun _ _ g => second g
|}.
Next Obligation. apply second_id. Qed.
Next Obligation. apply second_comp. Qed.

(* The 镜像: fixed factor RIGHT, G ↦ G × K, acting [first].
 It not part exercise; it here because [Binoidal]
 structure below needs both one-variable tensorings. （已译） *)
Program Definition fixed_product_functor_right (K : C) : C ⟶ C := {|
  fobj := fun G => G × K;
  fmap := fun _ _ g => first g
|}.
Next Obligation. apply first_id. Qed.
Next Obligation. apply first_comp. Qed.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary fixed_product_fmap {H x y : C} (g : x ~> y) :
  fmap[fixed_product_functor H] g = second g.
Proof. reflexivity. Qed.

Corollary fixed_product_fmap_right {K x y : C} (g : x ~> y) :
  fmap[fixed_product_functor_right K] g = first g.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Fixed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition fixed_product_transform {H K : C} (f : H ~> K) :
  fixed_product_functor H ⟹ fixed_product_functor K := {|
  transform := fun _ => first f
|}.
Next Obligation. symmetry; apply first_second. Qed.
Next Obligation. apply first_second. Qed.

Corollary fixed_product_first {H K : C} (f : H ~> K) (G : C) :
  transform[fixed_product_transform f] G = first f.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Fixed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem fixed_product_bimap {H x y : C} (g : x ~> y) :
  fmap[fixed_product_functor H] g ≈ bimap[×(C)] (id[H]) g.
Proof.
  simpl; unfold second.
  now rewrite id_left.
Qed.

Theorem fixed_product_transform_bimap {H K : C} (f : H ~> K) (G : C) :
  transform[fixed_product_transform f] G ≈ bimap[×(C)] f (id[G]).
Proof.
  simpl; unfold first.
  now rewrite id_left.
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Fixed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition alt_transform {H K : C} (f : H ~> K) :
  fixed_product_functor H ⟹ fixed_product_functor K := {|
  transform := fun G => split f (id[G])
|}.
Next Obligation. unfork. Qed.
Next Obligation. unfork. Qed.

(*
   本节说明 Fixed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem alt_transform_agrees {H K : C} (f : H ~> K) :
  alt_transform f ≈ fixed_product_transform f.
Proof.
  intro G; simpl.
  symmetry.
  apply (fixed_product_transform_bimap f G).
Qed.

(* * ** A terminal-free binoidal structure any cartesian 范畴 （已译） *)

(*
   本节说明幺半结构、函子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Cartesian_Binoidal : @Binoidal C :=
  @Build_Binoidal C
    (fun x y => x × y)
    (fun K => ToAFunctor (fixed_product_functor_right K))
    (fun H => ToAFunctor (fixed_product_functor H)).

(*
   本节说明函子、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary Cartesian_Binoidal_inj_right (H : C) :
  @inj_right C Cartesian_Binoidal H = fixed_product_functor H.
Proof. reflexivity. Qed.

Corollary Cartesian_Binoidal_inj_left (K : C) :
  @inj_left C Cartesian_Binoidal K = fixed_product_functor_right K.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem fixed_product_transform_faithful {H K : C} (f g : H ~> K) :
  fixed_product_transform f ≈ fixed_product_transform g → f ≈ g.
Proof.
  intro Heq.
  assert (Hprobe : ∀ h : H ~> K, h ≈ (exl ∘ first (z:=H) h) ∘ (id △ id)).
  { intro h.
    rewrite exl_first.
    rewrite <- comp_assoc.
    rewrite exl_fork.
    now rewrite id_right. }
  rewrite (Hprobe f), (Hprobe g).
  now rewrite (Heq H).
Qed.

(* Hence induced transformation 恒等 transformation only
 f itself 恒等: no unlucky choice f can produce a
 degenerate witness. （已译） *)
Corollary fixed_product_transform_reflects_id {H : C} (f : H ~> H) :
  fixed_product_transform f ≈ nat_id → f ≈ id.
Proof.
  intro Heq.
  apply fixed_product_transform_faithful.
  intro G.
  rewrite (Heq G).
  simpl.
  now rewrite first_id, second_id.
Qed.

(* 相关说明。 （已译） *)

Theorem fixed_product_transform_id {H : C} :
  fixed_product_transform (id[H]) ≈ nat_id.
Proof.
  intro G; simpl.
  now rewrite first_id, second_id.
Qed.

Theorem fixed_product_transform_comp {H K L : C} (f : K ~> L) (g : H ~> K) :
  fixed_product_transform (f ∘ g)
    ≈ nat_compose (fixed_product_transform f) (fixed_product_transform g).
Proof.
  intro G; simpl.
  apply first_comp.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition fixed_product_curried : C ⟶ [C, C] := {|
  fobj := fixed_product_functor;
  fmap := fun _ _ f => fixed_product_transform f
|}.
Next Obligation.
  intros f g Hfg G; simpl.
  now rewrite Hfg.
Qed.
Next Obligation. apply fixed_product_transform_id. Qed.
Next Obligation. apply fixed_product_transform_comp. Qed.

End FixedProduct.

(* 相关说明。 （已译） *)

(*
   本节说明函子、笛卡尔、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BinoidalComparison.

Context {C : Category}.
Context `{CC : @Cartesian C}.
Context `{T : @Terminal C}.

Definition Cartesian_Monoidal_Binoidal : @Binoidal C :=
  @Monoidal_Binoidal C (@Cartesian_Monoidal C CC T).

Corollary fixed_product_inj_right_obj (H G : C) :
  (@inj_right C Cartesian_Monoidal_Binoidal H) G = fixed_product_functor H G.
Proof. reflexivity. Qed.

Theorem fixed_product_inj_right_fmap (H : C) {x y : C} (g : x ~> y) :
  fmap[@inj_right C Cartesian_Monoidal_Binoidal H] g
    ≈ fmap[fixed_product_functor H] g.
Proof.
  simpl; unfold second.
  now rewrite id_left.
Qed.

Corollary fixed_product_inj_left_obj (K G : C) :
  (@inj_left C Cartesian_Monoidal_Binoidal K) G
    = fixed_product_functor_right K G.
Proof. reflexivity. Qed.

Theorem fixed_product_inj_left_fmap (K : C) {x y : C} (g : x ~> y) :
  fmap[@inj_left C Cartesian_Monoidal_Binoidal K] g
    ≈ fmap[fixed_product_functor_right K] g.
Proof.
  simpl; unfold first.
  now rewrite id_left.
Qed.

(*
   本节说明 Fixed 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary alt_is_inj_left {H K : C} (f : H ~> K) (G : C) :
  transform[alt_transform f] G
    = fmap[@inj_left C Cartesian_Monoidal_Binoidal G] f.
Proof. reflexivity. Qed.

Corollary alt_is_inj_right (H : C) {x y : C} (g : x ~> y) :
  split (id[H]) g = fmap[@inj_right C Cartesian_Monoidal_Binoidal H] g.
Proof. reflexivity. Qed.

End BinoidalComparison.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)

Definition Grp_fixed_product (H : Grp) : Grp ⟶ Grp :=
  fixed_product_functor H.

Definition Grp_fixed_product_transform {H K : Grp} (f : H ~{Grp}~> K) :
  Grp_fixed_product H ⟹ Grp_fixed_product K :=
  fixed_product_transform f.

(* The 对象 map direct product G ↦ H × G nose. （已译） *)
Corollary Grp_fixed_product_obj (H G : Grp) :
  Grp_fixed_product H G = Grp_product H G.
Proof. reflexivity. Qed.

(** ** Non-vacuity *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Grp_Z2_zero : Z2 ~{Grp}~> Z2 := @zero_mor Grp Grp_Zero Z2 Z2.

(* The zero homomorphism collapses Z/2 onto its unit. *)
Lemma Grp_Z2_zero_const (b : carrier Z2) : grp_map Grp_Z2_zero b ≈ false.
Proof. reflexivity. Qed.

Lemma Grp_Z2_zero_not_injective :
  (∀ a b : carrier Z2, grp_map Grp_Z2_zero a ≈ grp_map Grp_Z2_zero b → a ≈ b)
    → False.
Proof.
  intro Hinj.
  apply Z2_nontrivial.
  apply Hinj.
  reflexivity.
Qed.

Theorem Grp_Z2_zero_not_monic : Monic Grp_Z2_zero → False.
Proof.
  intro Hm.
  apply Grp_Z2_zero_not_injective.
  destruct (Grp_injectivity_is_monic Grp_Z2_zero) as [_ Hback].
  exact (Hback Hm).
Qed.

(* Not split monic, by [sections_are_monic]. *)
Theorem Grp_Z2_zero_not_section : Section Grp_Z2_zero → False.
Proof.
  intro Hs.
  apply Grp_Z2_zero_not_monic.
  now apply sections_are_monic.
Qed.

(* Hence no left inverse. *)
Theorem Grp_Z2_zero_no_left_inverse (g : Z2 ~{Grp}~> Z2) :
  g ∘ Grp_Z2_zero ≈ id → False.
Proof.
  intro Hg.
  apply Grp_Z2_zero_not_section.
  now refine {| section := g |}.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Grp_Z2_zero_not_iso : IsIsomorphism Grp_Z2_zero → False.
Proof.
  intro Hi.
  exact (Grp_Z2_zero_no_left_inverse
           (@two_sided_inverse Grp Z2 Z2 Grp_Z2_zero Hi)
           (@is_left_inverse Grp Z2 Z2 Grp_Z2_zero Hi)).
Qed.

(* 相关说明。 （已译） *)
Example Grp_fixed_product_moves :
  grp_map (transform[Grp_fixed_product_transform Grp_Z2_zero] Z2) (true, true)
    ≈ (false, true).
Proof. split; reflexivity. Qed.

(* And (true, true) is not (false, true). *)
Lemma Grp_Z2_pair_distinct :
  (@equiv _ (grp_setoid (Grp_product Z2 Z2)) (true, true) (false, true))
    → False.
Proof. intros [Hl _]; discriminate. Qed.

(* Put together: the component really does move (true, true). *)
Theorem Grp_fixed_product_component_moves :
  grp_map (transform[Grp_fixed_product_transform Grp_Z2_zero] Z2) (true, true)
    ≈ (true, true) → False.
Proof.
  intro Hfix.
  apply Grp_Z2_pair_distinct.
  rewrite <- Hfix.
  exact Grp_fixed_product_moves.
Qed.

Theorem Grp_fixed_product_transform_not_id :
  Grp_fixed_product_transform Grp_Z2_zero ≈ nat_id → False.
Proof.
  intro Heq.
  apply Z2_nontrivial.
  symmetry.
  exact (fixed_product_transform_reflects_id Grp_Z2_zero Heq true).
Qed.

(* 相关说明。 （已译） *)
Theorem Grp_fixed_product_component_not_monic :
  Monic (transform[Grp_fixed_product_transform Grp_Z2_zero] Z2) → False.
Proof.
  intro Hm.
  apply Grp_Z2_pair_distinct.
  destruct (Grp_injectivity_is_monic
              (transform[Grp_fixed_product_transform Grp_Z2_zero] Z2))
    as [_ Hback].
  apply (Hback Hm).
  split; reflexivity.
Qed.
