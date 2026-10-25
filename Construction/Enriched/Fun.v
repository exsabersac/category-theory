Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Construction.Enriched.
Require Import Category.Construction.Enriched.Natural.
Require Import Category.Construction.Enriched.Compose.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * The ORDINARY category [C, D]_V of K-enriched functors and V-natural
   transformations.

   Objects are the enriched functors C ⟶ D, morphisms are the V-natural
   transformations of Natural.v under their componentwise setoid, the
   identity at F has components eid, and composition is VERTICAL
   composition: at x, the composite of τ after σ is

   ecompose ∘ (τ_x ⨂ σ_x) ∘ λ_I⁻¹

   where λ_I⁻¹ : I ~> I ⨂ I coerces the tensor unit so that the two
   I-sourced components can be tensored and then composed in D.

   Ledger entry 11 (a scope note, not a weakening): this file delivers the
   ordinary category of V-functors, which is exactly this phase's named
   deliverable.  Upgrading it to a genuine V-CATEGORY — with hom-OBJECTS
   ∫_c D(F c, G c) valued in K rather than hom-sets — requires ends in K
   and underlying-category machinery, and is deferred to a later phase
   (ledger 11). 

   --------
   * K-增强函子和 V-自然变换的 ORDINARY 类别 [C, D] _V。

   对象是从 C ⟶ D 的增强函子，态射是 Natural.v 在其分量集合等价下的 V-自然变换，F 的恒等映射的分量为 eid，复合是垂直复合：在 x 点，τ 在 σ 之后的复合为

   ecompose ∘ (τ_x ⨂ σ_x) ∘ λ_I⁻¹

   其中 λ_I⁻¹ : I ~> I ⨂ I 将张量单位强制为可以对两个源自 I 的分量进行张量，然后在 D 中复合。分类账条目 11（一个范围说明，而不是削弱）：此文件提供了普通的 V-函子类别，这正是本阶段命名的交付物。将其升级为真正的 V-范畴 —— 具有以 K 值而非同态集合为值的同态对象 ∫_c D(F c, G c) —— 需要在 K 中的极限以及底层类别的机制，并且推迟到后续阶段（分类账 11）。
*)

(*
   * * A small splitting/cons toolkit in K

   Interchange specializations that peel a composite out of one tensor
   slot, plus right-nested ("cons") forms of the enriched associativity
   law and of the solved triangle identities from
   Structure/Monoidal/Braided/Proofs.v.  All are pure monoidal-category
   facts except [ecompose_assoc_cons], which is the associativity law of
   an enriched category re-bracketed for right-nested rewriting. 

   --------
   * * K 中的小型拆分/cons 工具包

   交换专门化，用于从一个张量槽中剥离复合结构，以及丰富的结合律的右嵌套（“cons”）形式，以及来自 Structure/Monoidal/Braided/Proofs.v 的已解三角形恒等式。所有都是纯单模范畴的定理，除了 [ecompose_assoc_cons]，它是一个丰富范畴的结合律，已重新加括弧以用于右嵌套重写。
*)

Section Toolkit.

Context {K : Category}.
Context `{M : @Monoidal K}.

Lemma tensor_split_left {x y z w v : K}
      (f : y ~> z) (g : x ~> y) (h : w ~> v) :
  (f ∘ g) ⨂ h ≈ (f ⨂ id[v]) ∘ (g ⨂ h).
Proof. now rewrite <- bimap_comp, id_left. Qed.

Lemma tensor_split_right {x y z w v : K}
      (f : y ~> z) (g : x ~> y) (h : w ~> v) :
  (f ∘ g) ⨂ h ≈ (f ⨂ h) ∘ (g ⨂ id[w]).
Proof. now rewrite <- bimap_comp, id_right. Qed.

Lemma tensor_split2_left {x y z w v : K}
      (h : w ~> v) (f : y ~> z) (g : x ~> y) :
  h ⨂ (f ∘ g) ≈ (id[v] ⨂ f) ∘ (h ⨂ g).
Proof. now rewrite <- bimap_comp, id_left. Qed.

Lemma tensor_split2_right {x y z w v : K}
      (h : w ~> v) (f : y ~> z) (g : x ~> y) :
  h ⨂ (f ∘ g) ≈ (h ⨂ f) ∘ (id[w] ⨂ g).
Proof. now rewrite <- bimap_comp, id_right. Qed.

(*
 [triangle_inverse_middle] against a continuation:
 α ∘ ((ρ⁻¹ ⨂ id) ∘ k) ≈ (id ⨂ λ⁻¹) ∘ k. 

 --------
 [triangle_inverse_middle] 反对延续：
 α ∘ ((ρ⁻¹ ⨂ id) ∘ k) ≈ (id ⨂ λ⁻¹) ∘ k。
*)
Lemma triangle_inverse_middle_cons {u v z : K} (k : z ~> (u ⨂ v)%object) :
  tensor_assoc ∘ ((unit_right⁻¹ ⨂ id[v]) ∘ k) ≈ (id[u] ⨂ unit_left⁻¹) ∘ k.
Proof. rewrite comp_assoc; now rewrite triangle_inverse_middle. Qed.

(*
 The associativity law of an enriched category, re-bracketed so that it
 rewrites in right-nested composition chains. 

 --------
 一个增广范畴的结合律，重新加括号，使其可以改写为右嵌套的组合链。
*)
Lemma ecompose_assoc_cons {D : Enriched K} {x y z w : D} {v : K}
      (k : v ~{K}~> ((z ⟿ w) ⨂ (y ⟿ z)) ⨂ (x ⟿ y)) :
  ecompose ∘ ((ecompose ⨂ id) ∘ k)
    ≈ ecompose ∘ ((id ⨂ ecompose) ∘ (tensor_assoc ∘ k)).
Proof.
  rewrite comp_assoc.
  rewrite ecompose_assoc.
  now rewrite <- !comp_assoc.
Qed.

End Toolkit.

(*
   * * Component-level unit and associativity laws

   The vertical composite's unit and associativity laws hold at each
   component for purely typological reasons — no naturality is involved —
   so we prove them once, for arbitrary I-sourced elements of hom-objects
   of any K-category D. 

   --------
   * * 组件级单位律和结合律

   垂直复合的单位律和结合律在每个组件上都成立，这完全是类型学原因——不涉及自然性——因此我们只需对任何 K-范畴 D 的同对象的任意 I-源元素证明一次即可。
*)

Section Vertical.

Context {K : Category}.
Context `{M : @Monoidal K}.
Context {D : Enriched K}.

(*
 eid is a left unit for vertical composition, by eid_left. 

 --------
 eid 是用于垂直组合的左单元，由 eid_left 提供。
*)
Lemma vertical_id_left {x y : D} (f : I ~{K}~> (x ⟿ y)) :
  ecompose ∘ (eid ⨂ f) ∘ unit_left⁻¹ ≈ f.
Proof.
  rewrite <- (bimap_id_right_left eid).
  rewrite !comp_assoc.
  rewrite eid_left.
  rewrite <- comp_assoc.
  rewrite from_unit_left_natural.
  rewrite comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

(*
 eid is a right unit for vertical composition, by eid_right; Kelly's
 λ_I⁻¹ ≈ ρ_I⁻¹ ([unit_identity_from]) converts the coercion. 

 --------
 eid 是垂直组合的右单位，由 eid_right 定义；Kelly 的 λ_I⁻¹ ≈ ρ_I⁻¹（[unit_identity_from]）转换了强制类型转换。
*)
Lemma vertical_id_right {x y : D} (f : I ~{K}~> (x ⟿ y)) :
  ecompose ∘ (f ⨂ eid) ∘ unit_left⁻¹ ≈ f.
Proof.
  rewrite unit_identity_from.
  rewrite <- (bimap_id_left_right eid).
  rewrite !comp_assoc.
  rewrite eid_right.
  rewrite <- comp_assoc.
  rewrite from_unit_right_natural.
  rewrite comp_assoc.
  rewrite iso_to_from.
  now rewrite id_left.
Qed.

(*
 Vertical composition is associative: reassociate with ecompose_assoc,
 slide the associator through the components, and let the unitor
 bookkeeping cancel via the solved triangle identities. 

 --------
 垂直组合是结合的：使用 ecompose_assoc 重新结合，将结合子在各个组成部分间滑动，并让单位子通过已解的三角恒等式取消簿记。
*)
Lemma vertical_assoc {w x y z : D}
      (p : I ~{K}~> (y ⟿ z)) (q : I ~{K}~> (x ⟿ y))
      (r : I ~{K}~> (w ⟿ x)) :
  ecompose ∘ (p ⨂ (ecompose ∘ (q ⨂ r) ∘ unit_left⁻¹)) ∘ unit_left⁻¹
    ≈ ecompose ∘ ((ecompose ∘ (p ⨂ q) ∘ unit_left⁻¹) ⨂ r) ∘ unit_left⁻¹.
Proof.
  rewrite <- !comp_assoc.
  (*
 left side: peel ecompose and the coercion out of the second slot 

 --------
 左侧：剥离、分解第二个槽中的强制
*)
  rewrite (tensor_split2_left p ecompose).
  rewrite (tensor_split2_right p (q ⨂ r)).
  rewrite <- !comp_assoc.
  (*
 (id ⨂ λ_I⁻¹) ∘ λ_I⁻¹ ≈ λ_{I⨂I}⁻¹ ∘ λ_I⁻¹, then solve λ_{I⨂I}⁻¹ for α 

 --------
 (id ⨂ λ_I⁻¹) ∘ λ_I⁻¹ ≈ λ_{I⨂I}⁻¹ ∘ λ_I⁻¹，然后解 λ_{I⨂I}⁻¹ 得到 α
*)
  rewrite from_unit_left_natural.
  rewrite <- triangle_inverse_left.
  rewrite <- !comp_assoc.
  (*
 slide α through the three components and reassociate the composition 

 --------
 将 α 滑过三个组件并重新组合组成部分
*)
  rewrite to_assoc_nat_cons.
  rewrite <- ecompose_assoc_cons.
  (* fuse everything back into the right-hand shape / 将所有部分融合回右侧形状 *)
  rewrite !bimap_fuse_cons.
  rewrite id_right, id_left.
  (* match the bracketing of the right-hand side / 匹配右侧的括号 *)
  now rewrite (comp_assoc ecompose (p ⨂ q) (unit_left⁻¹)).
Qed.

End Vertical.

(* * * The identity V-natural transformation / * * 恒等 V-自然变换 *)

Program Definition EnrichedIdTransform {K : Category} `{M : @Monoidal K}
        {C D : Enriched K} (F : EnrichedFunctor K C D) :
  EnrichedTransform F F := {|
  etransform := fun x => eid
|}.
Next Obligation.
  intros K M C D F x y.
  simpl.
  (*
 Both whiskerings reduce to efmap: split eid out of the tensor, collapse
 ecompose against it via eid_left / eid_right, and cancel the unitors by
 their naturality. 

 --------
 两种搅拌都归结为 efmap：将 eid 从张量中拆分出来，通过 eid_left / eid_right 对其执行 ecompose，并通过它们的自然性消去单位子。
*)
  rewrite <- (bimap_id_right_left eid).
  rewrite <- (bimap_id_left_right eid).
  rewrite !comp_assoc.
  rewrite eid_left, eid_right.
  rewrite <- (to_unit_left_natural (efmap (EnrichedFunctor := F))).
  rewrite <- (to_unit_right_natural (efmap (EnrichedFunctor := F))).
  rewrite <- !comp_assoc.
  rewrite !iso_to_from.
  now rewrite !id_right.
Qed.

(* * * Vertical composition of V-natural transformations / * * V-自然变换的垂直组合 *)

Program Definition EnrichedTransform_vcompose {K : Category} `{M : @Monoidal K}
        {C D : Enriched K} {F G J : EnrichedFunctor K C D}
        (τ : EnrichedTransform G J) (σ : EnrichedTransform F G) :
  EnrichedTransform F J := {|
  etransform := fun x =>
    ecompose ∘ (etransform (EnrichedTransform := τ) x
                  ⨂ etransform (EnrichedTransform := σ) x) ∘ unit_left⁻¹
|}.
Next Obligation.
  (*
 V-naturality of the vertical composite.  Reassociate with
 ecompose_assoc so that σ's component meets efmap F, apply σ's
 enaturality, reassociate back so that τ's component meets efmap G, and
 apply τ's enaturality; the unitor bookkeeping mirrors the ecompose_assoc
 proof pattern via the solved triangle identities. 

 --------
 垂直复合的 V-自然性。使用 ecompose_assoc 重新结合，使 σ 的分量与 efmap F 相遇，应用 σ 的 e-自然性，再重新结合，使 τ 的分量与 efmap G 相遇，并应用 τ 的 e-自然性；单位子计算与通过已解的三角形恒等式的 ecompose_assoc 证明模式相呼应。
*)
  intros K M C D F G J τ σ x y.
  simpl.
  rewrite <- !comp_assoc.
  transitivity
    (ecompose
       ∘ (((ecompose
              ∘ (efmap (EnrichedFunctor := J) (x:=x) (y:=y)
                   ⨂ etransform (EnrichedTransform := τ) x)
              ∘ unit_right⁻¹)
             ⨂ etransform (EnrichedTransform := σ) x)
            ∘ unit_right⁻¹)).
  - (* Left whiskering into the middle form. / 左边的触须伸入中间的形态。 *)
    rewrite (tensor_split_left ecompose).
    rewrite (tensor_split_right
               (etransform (EnrichedTransform := τ) y
                  ⨂ etransform (EnrichedTransform := σ) y)).
    rewrite <- !comp_assoc.
    rewrite ecompose_assoc_cons.
    rewrite <- to_assoc_nat_cons.
    rewrite bimap_fuse_cons.
    rewrite id_left.
    (* α ∘ ((λ_I⁻¹ ⨂ id) ∘ λ⁻¹) ≈ (id ⨂ λ⁻¹) ∘ λ⁻¹ *)
    rewrite unit_identity_from.
    rewrite triangle_inverse_middle_cons.
    rewrite bimap_fuse_cons.
    rewrite id_right.
    (* σ's enaturality, inside the second tensor slot / σ的非自然性，在第二个张量槽内 *)
    rewrite (enaturality (EnrichedTransform := σ) (x:=x) (y:=y)).
    (* peel it back apart around the associator / 在关联器周围把它剥开 *)
    rewrite (tensor_split2_right (etransform (EnrichedTransform := τ) y)
               (ecompose ∘ (efmap (EnrichedFunctor := G) (x:=x) (y:=y)
                              ⨂ etransform (EnrichedTransform := σ) x))).
    rewrite (tensor_split2_left (etransform (EnrichedTransform := τ) y)
               ecompose).
    rewrite <- !comp_assoc.
    (*
 (id ⨂ ρ⁻¹) ∘ λ⁻¹ ≈ λ_{A⨂I}⁻¹ ∘ ρ⁻¹, then solve λ_{A⨂I}⁻¹ for α 

 --------
 (id ⨂ ρ⁻¹) ∘ λ⁻¹ ≈ λ_{A⨂I}⁻¹ ∘ ρ⁻¹，然后对 α 求解 λ_{A⨂I}⁻¹
*)
    rewrite from_unit_left_natural.
    rewrite <- triangle_inverse_left.
    rewrite <- !comp_assoc.
    rewrite to_assoc_nat_cons.
    rewrite <- ecompose_assoc_cons.
    rewrite !bimap_fuse_cons.
    rewrite id_right, id_left.
    (* τ's enaturality, inside the first tensor slot / τ 的非自然性，在第一个张量位置内 *)
    rewrite (enaturality (EnrichedTransform := τ) (x:=x) (y:=y)).
    now rewrite <- !comp_assoc.
  - (* Right whiskering into the middle form: pure unitor bookkeeping. / 直接打入中间形式：纯一元算账。 *)
    symmetry.
    rewrite (tensor_split2_left (efmap (EnrichedFunctor := J) (x:=x) (y:=y))
               ecompose).
    rewrite (tensor_split2_right (efmap (EnrichedFunctor := J) (x:=x) (y:=y))
               (etransform (EnrichedTransform := τ) x
                  ⨂ etransform (EnrichedTransform := σ) x)).
    rewrite <- !comp_assoc.
    (* (id ⨂ λ_I⁻¹) ∘ ρ⁻¹ ≈ (α ∘ (ρ⁻¹ ⨂ id)) ∘ ρ⁻¹ *)
    rewrite <- triangle_inverse_middle.
    rewrite <- !comp_assoc.
    rewrite to_assoc_nat_cons.
    rewrite <- ecompose_assoc_cons.
    rewrite !bimap_fuse_cons.
    rewrite id_right, id_left.
    now rewrite <- !comp_assoc.
Qed.

(** * The functor category [C, D]_V / * 函子范畴 [C, D] _V *)

Program Definition Enriched_Fun {K : Category} `{M : @Monoidal K}
        (C D : Enriched K) : Category := {|
  obj     := EnrichedFunctor K C D;
  hom     := fun F G => EnrichedTransform F G;
  homset  := fun F G => EnrichedTransform_Setoid F G;
  id      := fun F => EnrichedIdTransform F;
  compose := fun F G J τ σ => EnrichedTransform_vcompose τ σ
|}.
Next Obligation.
  (* compose respects the componentwise setoid / compose 尊重按组件的集合等价关系 *)
  intros K M C D F G J.
  proper.
  simpl.
  now rewrite (X x1), (X0 x1).
Qed.
Next Obligation.
  (* id_left, componentwise / id_left，逐组件 *)
  intros K M C D F G σ x.
  simpl.
  apply vertical_id_left.
Qed.
Next Obligation.
  (* id_right, componentwise / id_right，逐组件 *)
  intros K M C D F G σ x.
  simpl.
  apply vertical_id_right.
Qed.
Next Obligation.
  (* comp_assoc, componentwise / 组合关联，逐组件 *)
  intros K M C D F G J L τ σ υ x.
  simpl.
  apply vertical_assoc.
Qed.
Next Obligation.
  (* comp_assoc_sym, componentwise / comp_assoc_sym，按分量 *)
  intros K M C D F G J L τ σ υ x.
  simpl.
  symmetry.
  apply vertical_assoc.
Qed.
