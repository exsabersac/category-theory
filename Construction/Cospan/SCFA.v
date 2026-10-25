Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.

Generalizable All Variables.

(*
   * * Special commutative Frobenius algebras on [CospanCat C HP]

   Every object of [CospanCat C HP] carries a canonical SCFA built
   from the cocartesian structure of [C].  This file discharges the
   axioms of:
   - [Monoid (CospanCat C HP) X]   (with mu, eta from [cospan_scfa_*])
   - [Comonoid (CospanCat C HP) X] (with delta, epsilon)
   - [Frobenius] compatibility
   - [CommutativeFrobenius] (mu/delta commutativity under braid)
   - [SpecialCommutativeFrobenius] (mu ∘ delta ≈ id)
   for each [X : C].

   The proofs reduce — via [mor_as_cospan_compose] and
   [cospan_tensor_mor_as_cospan] — to C-level coproduct identities on
   pushouts of the codiagonal [id ▽ id] and zero. 

   --------
   * * 在  [CospanCat C HP] 上的特殊交换 Frobenius 代数  

   [CospanCat C HP] 的每个对象都携带一个由  [C] 的余笛卡尔结构构建的自然 SCFA。本文件完成以下公理的证明：  
   -  [Monoid (CospanCat C HP) X] （使用来自 [cospan_scfa_*] 的 mu、eta）  
   -  [Comonoid (CospanCat C HP) X] （使用 delta、epsilon）  
   -  [Frobenius] 兼容性  
   -  [CommutativeFrobenius] （mu/delta 在编织下交换性）  
   -  [SpecialCommutativeFrobenius] （mu ∘ delta ≈ id）  
   对每个 [X : C]。  

   通过 [mor_as_cospan_compose] 和 [cospan_tensor_mor_as_cospan]，证明可化简为 C 级余积在 [id ▽ id] 和零的推挤图上的恒等式。
*)

(*
 SCFA = special commutative Frobenius algebra, i.e. the "classical
 structure" of categorical quantum mechanics: a commutative comonoid
 plus cocommutative monoid satisfying the Frobenius law
 [(id ⨂ mu) ∘ (delta ⨂ id) ≈ delta ∘ mu ≈ (mu ⨂ id) ∘ (id ⨂ delta)]
 and the special law [mu ∘ delta ≈ id].  In [CospanCat C HP] each object
 [X] carries the canonical SCFA whose [mu]/[delta] are the fold/cofold
 (codiagonal [id ▽ id]) maps and whose [eta]/[epsilon] are [zero], making
 [Cospan(FinSet)] the prototypical hypergraph category.

 nLab:      https://ncatlab.org/nlab/show/Frobenius+algebra
 nLab:      https://ncatlab.org/nlab/show/classical+structure
 Wikipedia: https://en.wikipedia.org/wiki/Frobenius_algebra 

 --------
 SCFA = 特殊交换弗罗贝nius代数，即范畴量子力学的“经典结构”：一个交换余半群加上满足弗罗贝nius律的余交换半群
 [(id ⨂ mu) ∘ (delta ⨂ id) ≈ delta ∘ mu ≈ (mu ⨂ id) ∘ (id ⨂ delta)]
 和特殊律 [mu ∘ delta ≈ id]。在 [CospanCat C HP] 中，每个对象 [X] 都携带规范的 SCFA，其 [mu] / [delta] 是折叠/反折叠（余对角 [id ▽ id]）映射，其 [eta] / [epsilon] 是 [zero]，使得 [Cospan(FinSet)] 成为典型的超图范畴。

 nLab: https://ncatlab.org/nlab/show/Frobenius+algebra
 nLab: https://ncatlab.org/nlab/show/classical+structure
 Wikipedia: https://en.wikipedia.org/wiki/Frobenius_algebra
*)

Section CospanSCFA.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context (HP : HasPushouts C).

(*
   * ** Identification of the SCFA data with [mor_as_cospan] lifts

   [cospan_scfa_mu X] and [cospan_scfa_eta X] are exactly
   [mor_as_cospan (id ▽ id)] and [mor_as_cospan zero] respectively.
   [cospan_scfa_delta X] and [cospan_scfa_epsilon X] are the
   backwards-cospan variants, lifted via [mor_as_cospan_back]. 

   --------
   * ** 使用 [mor_as_cospan] 提升的 SCFA 数据识别

   [cospan_scfa_mu X] 和 [cospan_scfa_eta X] 分别就是
   [mor_as_cospan (id ▽ id)] 和 [mor_as_cospan zero]。
   [cospan_scfa_delta X] 和 [cospan_scfa_epsilon X] 是
   反余跨变体，通过 [mor_as_cospan_back] 提升。
*)

Lemma cospan_scfa_mu_as_cospan (X : C) :
  cospan_scfa_mu X = mor_as_cospan ((id[X] ▽ id[X]) : (X + X)%object ~{C}~> X).
Proof. reflexivity. Qed.

Lemma cospan_scfa_eta_as_cospan (X : C) :
  cospan_scfa_eta X = mor_as_cospan (zero : 0%object ~{C}~> X).
Proof. reflexivity. Qed.

(*
   * A cospan from [X] to [Y] with apex [X], leg1 = id, leg2 = f : Y → X.
   This is the "backward" direction: a C-morphism [Y → X] reinterpreted
   as a cospan from [X] to [Y]. 

   --------
   * 一个从  [X] 到  [Y] 的余积尖，顶点为  [X] ，腿1 = id，腿2 = f : Y → X。
   这是“向后”的方向：一个 C-态射  [Y → X] 被重新解释为从  [X] 到  [Y] 的余积尖。
*)
Definition mor_as_cospan_back {X Y : C} (f : Y ~> X) : CospanArrow X Y :=
  Build_CospanArrow X id[X] f.

Lemma cospan_scfa_delta_as_back (X : C) :
  cospan_scfa_delta X
  = mor_as_cospan_back ((id[X] ▽ id[X]) : (X + X)%object ~{C}~> X).
Proof. reflexivity. Qed.

Lemma cospan_scfa_epsilon_as_back (X : C) :
  cospan_scfa_epsilon X
  = mor_as_cospan_back (zero : 0%object ~{C}~> X).
Proof. reflexivity. Qed.

(*
   * ** Bridging: composing a backward-cospan on the outside

   [mor_as_cospan_back f : X → Y] has apex X and in1 = id[X].
   Composing it with [g : Z → X] (apex N) gives the pushout of
   [(in2 g : X → N, id[X] : X → X)], whose apex collapses to N. 

   --------
   * ** 桥接：在外部组合一个向后的余跨度

   [mor_as_cospan_back f : X → Y] 的顶点是 X，且 in1 = id [X]。
   将其与 [g : Z → X]（顶点 N）组合得到
   [(in2 g : X → N, id[X] : X → X)] 的推挤，其顶点收缩为 N。
*)

Lemma cospan_compose_mor_as_cospan_back_left
      {X Y Z : C} (f : Y ~> X) (g : CospanArrow Z X) :
  cospan_equiv (cospan_compose HP (mor_as_cospan_back f) g)
               (Build_CospanArrow (cospan_apex g)
                                  (cospan_in1 g)
                                  (cospan_in2 g ∘ f)).
Proof.
  unfold cospan_compose, mor_as_cospan_back; simpl.
  pose (P := pushout (cospan_in2 g) (id[X] : X ~{C}~> X)).
  (*
 The apex P is pushout (in2 g, id[X]); by pushout_id_right_apex it ≅ apex g. 

 --------
 顶点 P 是 pushout（in2 g，id [X]）；通过 pushout_id_right_apex 它 ≅ 顶点 g。
*)
  pose (iso := pushout_id_right_apex HP (cospan_in2 g)).
  (*
 to iso : apex P → apex g, with:
 to iso ∘ pushout_in1 P ≈ id[apex g]
 to iso ∘ pushout_in2 P ≈ cospan_in2 g                                 

 --------
 到同构：apex P → apex g，满足：
 to iso ∘ pushout_in1 P ≈ id [apex g] 
 to iso ∘ pushout_in2 P ≈ cospan_in2 g
*)
  exists iso.
  simpl; split; fold P.
  - (* to iso ∘ (pushout_in1 P ∘ in1 g) ≈ in1 g / to iso ∘ (pushout_in1 P ∘ in1 g) ≈ in1 g *)
    rewrite comp_assoc.
    unfold iso, pushout_id_right_apex; simpl.
    rewrite pushout_med_in1.
    apply id_left.
  - (* to iso ∘ (pushout_in2 P ∘ f) ≈ in2 g ∘ f / to iso ∘ (pushout_in2 P ∘ f) ≈ in2 g ∘ f *)
    rewrite comp_assoc.
    unfold iso, pushout_id_right_apex; simpl.
    rewrite pushout_med_in2.
    reflexivity.
Defined.

(*
   * Note: composing [back_f] on the RIGHT (as inner) of a generic cospan is
   a genuine pushout (not a collapse), so no analogous left-collapse bridge
   exists.  The dual configurations use [back] on the LEFT (outer). 

   --------
   * 注意：在一个通用余跨度的右侧（作为内部）组合 [back_f] 是一个真正的推挤（而非塌缩），因此不存在类似的左侧塌缩桥。 对偶配置在左侧（外部）使用 [back]。
*)

(*
   * ** Tensor of [mor_as_cospan_back]s is again a [mor_as_cospan_back] 

   --------
   * ** [mor_as_cospan_back] 的张量再次是 [mor_as_cospan_back]
*)
Lemma cospan_tensor_mor_as_cospan_back
      {X Y X' Y' : C} (f : Y ~> X) (g : Y' ~> X') :
  cospan_equiv
    (cospan_tensor (mor_as_cospan_back f) (mor_as_cospan_back g))
    (mor_as_cospan_back (cover f g)).
Proof.
  unfold cospan_tensor, mor_as_cospan_back; simpl.
  exists iso_id; simpl; split.
  - rewrite id_left.
    (* cover id id ≈ id / 覆盖 id id ≈ id *)
    apply cover_id.
  - rewrite id_left.
    reflexivity.
Defined.

(*
   * [cospan_id X] is in particular [mor_as_cospan_back id[X]]. 

   --------
   *  [cospan_id X] 特别是在 [mor_as_cospan_back id[X] 中 ].
*)
Lemma cospan_id_as_back (X : C) :
  cospan_equiv (cospan_id X) (mor_as_cospan_back (id[X] : X ~{C}~> X)).
Proof.
  unfold cospan_id, mor_as_cospan_back; simpl.
  exists iso_id; simpl; split; cat.
Defined.

(*
   * [mor_as_cospan_back] respects [≈] on the C-morphism. 

   --------
   * [mor_as_cospan_back] 尊重 [≈] 在 C-态射上。
*)
Lemma mor_as_cospan_back_proper {X Y : C} (f g : Y ~> X) :
  f ≈ g -> cospan_equiv (mor_as_cospan_back f) (mor_as_cospan_back g).
Proof.
  intros Hfg.
  unfold mor_as_cospan_back; simpl.
  exists iso_id; simpl; split.
  - cat.
  - rewrite id_left.
    exact Hfg.
Defined.

(*
   * Composition of two backward cospans corresponds to composition of the
   underlying C-morphisms IN REVERSE ORDER (this is the cospan duality). 

   --------
   * 两个反向余跨的组合对应于其底层 C-态射的逆序组合（这是余跨对偶性）。
*)
Lemma mor_as_cospan_back_compose
      {X Y Z : C} (g : Z ~> Y) (f : Y ~> X) :
  cospan_equiv
    (cospan_compose HP (mor_as_cospan_back g) (mor_as_cospan_back f))
    (mor_as_cospan_back (f ∘ g)).
Proof.
  (*
 Apply cospan_compose_mor_as_cospan_back_left with the inner being back_f
 and back_g as outer. 

 --------
 用 cospan_compose_mor_as_cospan_back_left，内部是 back_f，外部是 back_g。
*)
  apply cospan_compose_mor_as_cospan_back_left.
Defined.

(*
   * ** Bridging: composing forward [mor_as_cospan (to phi)] (iso!) outside
   of a [mor_as_cospan_back g]

   [back_g : X → A] has apex X, in2 = g : A → X.
   [forward (to phi) : A → B] (phi : A ≅ B) has apex B, in1 = to phi.
   Compose: pushout (g : A → X, to phi : A → B) ≅ X via
   [pushout_along_iso_apex] (shared source A). 

   --------
   * ** 桥接：在 [mor_as_cospan_back g] 外部向前组合 [mor_as_cospan (to phi)]（同构！）

   [back_g : X → A] 的顶点为 X，in2 = g : A → X。
   [forward (to phi) : A → B]（phi : A ≅ B） 的顶点为 B，in1 = 到 phi。
   组合：通过 [pushout_along_iso_apex]（共享源 A）推出 (g : A → X, 到 phi : A → B) ≅ X。
*)
Lemma cospan_compose_forward_iso_back
      {X A B : C} (g : A ~> X) (phi : A ≅ B) :
  cospan_equiv
    (cospan_compose HP (mor_as_cospan (to phi))
                       (mor_as_cospan_back g))
    (mor_as_cospan_back (g ∘ from phi)).
Proof.
  unfold cospan_compose, mor_as_cospan, mor_as_cospan_back; simpl.
  pose (P := pushout (g : A ~{C}~> X) (to phi)).
  pose (iso := pushout_along_iso_apex HP g phi).
  (*
 to iso ∘ pushout_in1 P ≈ id[X];  to iso ∘ pushout_in2 P ≈ g ∘ from phi.
 (These come from the [pushout_med] definition inside pushout_along_iso_apex.) 

 --------
 到 iso ∘ pushout_in1 P ≈ id [X]；到 iso ∘ pushout_in2 P ≈ g ∘ 来自 phi。（这些来自 pushout_along_iso_apex 内部的 [pushout_med] 定义。）
*)
  exists iso; simpl; fold P; split.
  - (* pushout_med ∘ (pushout_in1 P ∘ id[X]) ≈ id[X] / pushout_med ∘ (pushout_in1 P ∘ id [X] ) ≈ id [X] *)
    rewrite comp_assoc.
    rewrite id_right.
    unfold iso, pushout_along_iso_apex; simpl.
    apply pushout_med_in1.
  - (* pushout_med ∘ (pushout_in2 P ∘ id[B]) ≈ g ∘ from phi / pushout_med ∘ (pushout_in2 P ∘ id [B] ) ≈ g ∘ 从 phi *)
    rewrite comp_assoc.
    rewrite id_right.
    unfold iso, pushout_along_iso_apex; simpl.
    apply pushout_med_in2.
Defined.

(*
   * ** C-level: codiagonal absorbs cover

   [(id ▽ id) ∘ cover f g ≈ f ▽ g] : the codiagonal absorbs the
   coproduct structure, simplifying both sides of the monoid axioms. 

   --------
   * ** C级：共对角吸收覆盖

   [(id ▽ id) ∘ cover f g ≈ f ▽ g]  ：共对角吸收了余积结构，从而简化了单子公理两边。
*)

Lemma codiag_cover {X Y Z : C} (f : Y ~> X) (g : Z ~> X) :
  ((id[X] ▽ id[X]) : (X + X)%object ~> X) ∘ cover f g ≈ f ▽ g.
Proof.
  apply coprod_ext.
  - rewrite <- comp_assoc.
    rewrite cover_inl.
    rewrite comp_assoc.
    rewrite inl_merge.
    rewrite id_left.
    rewrite inl_merge.
    reflexivity.
  - rewrite <- comp_assoc.
    rewrite cover_inr.
    rewrite comp_assoc.
    rewrite inr_merge.
    rewrite id_left.
    rewrite inr_merge.
    reflexivity.
Qed.

(*
   * ** [Monoid mu_assoc] at the C-level

   Reduces via [codiag_cover] to:
   (id ▽ id) ▽ id ≈ id ▽ (id ▽ id) ∘ to coprod_assoc                  

   --------
   * ** [Monoid mu_assoc] 在 C 级别

   通过 [codiag_cover] 简化为：
   (id ▽ id) ▽ id ≈ id ▽ (id ▽ id) ∘ 到 coprod_assoc
*)

Lemma codiag_assoc {X : C} :
  ((id[X] ▽ id[X]) : (X + X)%object ~> X) ∘ cover (id[X] ▽ id[X]) id[X]
  ≈ (id[X] ▽ id[X]) ∘ cover id[X] (id[X] ▽ id[X])
    ∘ to (@coprod_assoc C H_Coc X X X).
Proof.
  rewrite codiag_cover.
  rewrite <- comp_assoc.
  (*
 Goal: (id ▽ id) ▽ id ≈ (id ▽ id) ∘ (cover id (id ▽ id) ∘ α). 

 --------
 目标: (id ▽ id) ▽ id ≈ (id ▽ id) ∘ (cover id (id ▽ id) ∘ α)。
*)
  apply coprod_ext.
  - apply coprod_ext.
    + (* ∘ (inl ∘ inl) → LHS = id, RHS = (id▽id) ∘ inl = id / ∘ (inl ∘ inl) → 左边 = id, 右边 = (id▽id) ∘ inl = id *)
      rewrite inl_merge, inl_merge.
      symmetry.
      rewrite <- !comp_assoc.
      rewrite assoc_to_inl_inl.
      rewrite cover_inl.
      rewrite id_right.
      rewrite inl_merge.
      reflexivity.
    + (* ∘ (inl ∘ inr) → LHS = id, RHS reduces via assoc_to_inl_inr + cover_inr / ∘ (inl ∘ inr) → 左边 = id，右边通过 assoc_to_inl_inr + cover_inr 化简 *)
      rewrite inl_merge, inr_merge.
      symmetry.
      rewrite <- !comp_assoc.
      rewrite assoc_to_inl_inr.
      rewrite (comp_assoc (cover id[X] (id[X] ▽ id[X])) inr inl).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (id[X] ▽ id[X]) inl).
      rewrite inl_merge.
      rewrite id_right.
      rewrite inr_merge.
      reflexivity.
  - (* ∘ inr → LHS = id, RHS reduces via assoc_to_inr + cover_inr / ∘ inr → 左边 = id，右边通过 assoc_to_inr + cover_inr 化简 *)
    rewrite inr_merge.
    symmetry.
    rewrite <- !comp_assoc.
    rewrite assoc_to_inr.
    rewrite (comp_assoc (cover id[X] (id[X] ▽ id[X])) inr inr).
    rewrite cover_inr.
    rewrite <- (comp_assoc inr (id[X] ▽ id[X]) inr).
    rewrite inr_merge.
    rewrite id_right.
    rewrite inr_merge.
    reflexivity.
Qed.

(*
   * ** C-level identities backing the unit laws

   [mu ∘ bimap eta id ≈ to unit_left] becomes (at C level after
   mor_as_cospan-fusion):
   (id ▽ id) ∘ cover zero id ≈ zero ▽ id     [= to coprod_zero_l]   

   --------
   * ** 支持单位律的 C 级同一性

   [mu ∘ bimap eta id ≈ to unit_left] 在经过 mor_as_cospan-fusion 后（在 C 级）变为：
   (id ▽ id) ∘ cover zero id ≈ zero ▽ id      [= to coprod_zero_l]
*)

Lemma codiag_eta_left {X : C} :
  ((id[X] ▽ id[X]) : (X + X)%object ~> X) ∘ cover (zero : 0%object ~> X) id[X]
  ≈ to (@coprod_zero_l C H_Coc H_Ini X).
Proof.
  apply coprod_ext.
  - rewrite <- comp_assoc.
    rewrite cover_inl.
    rewrite comp_assoc.
    rewrite inl_merge.
    rewrite id_left.
    unfold to, coprod_zero_l; simpl.
    rewrite inl_merge.
    apply (@zero_unique C H_Ini _ _ _).
  - rewrite <- comp_assoc.
    rewrite cover_inr.
    rewrite comp_assoc.
    rewrite inr_merge.
    rewrite id_left.
    unfold to, coprod_zero_l; simpl.
    rewrite inr_merge.
    reflexivity.
Qed.

Lemma codiag_eta_right {X : C} :
  ((id[X] ▽ id[X]) : (X + X)%object ~> X) ∘ cover id[X] (zero : 0%object ~> X)
  ≈ to (@coprod_zero_r C H_Coc H_Ini X).
Proof.
  apply coprod_ext.
  - rewrite <- comp_assoc.
    rewrite cover_inl.
    rewrite comp_assoc.
    rewrite inl_merge.
    rewrite id_left.
    unfold to, coprod_zero_r; simpl.
    rewrite inl_merge.
    reflexivity.
  - rewrite <- comp_assoc.
    rewrite cover_inr.
    rewrite comp_assoc.
    rewrite inr_merge.
    rewrite id_left.
    unfold to, coprod_zero_r; simpl.
    rewrite inr_merge.
    apply (@zero_unique C H_Ini _ _ _).
Qed.

(*
   * ** C-level: codiagonal commutes with paws

   [(id ▽ id) ∘ paws ≈ id ▽ id]  is just [paws_fork]. 

   --------
   * ** C级别：codiagonal 与 paw 共轭

   [(id ▽ id) ∘ paws ≈ id ▽ id] 只是 [paws_fork] 。
*)

Lemma codiag_paws_comm {X : C} :
  ((id[X] ▽ id[X]) : (X + X)%object ~> X) ∘ paws
  ≈ (id[X] ▽ id[X]).
Proof. apply paws_fork. Qed.

(*
   * ** Cospan-level monoid axioms

   Each axiom lifts the corresponding C-level identity through
   [mor_as_cospan_compose] and [cospan_tensor_mor_as_cospan]. 

   --------
   * ** Cospan 级单子公理

   每条公理都将对应的 C 级恒等式通过 [mor_as_cospan_compose] 和 [cospan_tensor_mor_as_cospan] 提升。
*)

(*
   * [cospan_scfa_mu ∘ bimap mu (cospan_id X) ≈ cospan_scfa_mu ∘ bimap id mu ∘ to tensor_assoc]
   in [CospanCat C HP]. 

   --------
   *  [cospan_scfa_mu ∘ bimap mu (cospan_id X) ≈ cospan_scfa_mu ∘ bimap id mu ∘ to tensor_assoc] 
   在 [CospanCat C HP] 。
*)
Lemma cospan_mu_assoc (X : C) :
  cospan_equiv
    (cospan_compose HP (cospan_scfa_mu X)
       (cospan_tensor (cospan_scfa_mu X) (cospan_id X)))
    (cospan_compose HP
       (cospan_compose HP (cospan_scfa_mu X)
          (cospan_tensor (cospan_id X) (cospan_scfa_mu X)))
       (mor_as_cospan (to (@coprod_assoc C H_Coc X X X)))).
Proof.
  unfold cospan_scfa_mu.
  (*
 LHS: cospan_compose (mor_as_cospan (id▽id))
 (cospan_tensor (mor_as_cospan (id▽id)) (cospan_id X)).
 RHS: cospan_compose (cospan_compose (mor_as_cospan (id▽id))
 (cospan_tensor (cospan_id X) (mor_as_cospan (id▽id))))
 (mor_as_cospan α). 

 --------
 左边: cospan_compose (mor_as_cospan (id▽id))
 (cospan_tensor (mor_as_cospan (id▽id)) (cospan_id X))。
 右边: cospan_compose (cospan_compose (mor_as_cospan (id▽id))
 (cospan_tensor (cospan_id X) (mor_as_cospan (id▽id))))
 (mor_as_cospan α)。
*)
  (*
 On LHS replace [cospan_id X] with [mor_as_cospan id[X]], then fuse tensors. 

 --------
 在左侧把 [cospan_id X] 替换为 [mor_as_cospan id[X]，然后融合张量。
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_respects.
      + apply cospan_equiv_refl.
      + apply cospan_equiv_sym, mor_as_cospan_id.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_mor_as_cospan.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply cospan_equiv_sym.
  (* RHS handling. / RHS 处理。 *)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_compose_respects_aux.
      + apply cospan_tensor_respects.
        * apply cospan_equiv_sym, mor_as_cospan_id.
        * apply cospan_equiv_refl.
      + apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_compose_respects_aux.
      + apply cospan_tensor_mor_as_cospan.
      + apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply mor_as_cospan_compose. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  symmetry.
  apply codiag_assoc.
Defined.

(*
   * Cospan-level [mu ∘ bimap eta id ≈ to unit_left]. 

   --------
   * Cospan-水平 [mu ∘ bimap eta id ≈ to unit_left] .
*)
Lemma cospan_mu_unit_left (X : C) :
  cospan_equiv
    (cospan_compose HP (cospan_scfa_mu X)
       (cospan_tensor (cospan_scfa_eta X) (cospan_id X)))
    (mor_as_cospan (to (@coprod_zero_l C H_Coc H_Ini X))).
Proof.
  unfold cospan_scfa_mu, cospan_scfa_eta.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_respects.
      + apply cospan_equiv_refl.
      + apply cospan_equiv_sym, mor_as_cospan_id.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_mor_as_cospan.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  apply codiag_eta_left.
Defined.

(*
   * Cospan-level [mu ∘ bimap id eta ≈ to unit_right]. 

   --------
   * Cospan-水平 [mu ∘ bimap id eta ≈ to unit_right] .
*)
Lemma cospan_mu_unit_right (X : C) :
  cospan_equiv
    (cospan_compose HP (cospan_scfa_mu X)
       (cospan_tensor (cospan_id X) (cospan_scfa_eta X)))
    (mor_as_cospan (to (@coprod_zero_r C H_Coc H_Ini X))).
Proof.
  unfold cospan_scfa_mu, cospan_scfa_eta.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_respects.
      + apply cospan_equiv_sym, mor_as_cospan_id.
      + apply cospan_equiv_refl.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_mor_as_cospan.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  apply codiag_eta_right.
Defined.

(*
   * ** Cospan-level comonoid axioms (duals of the monoid axioms)

   Each δ-axiom decomposes into the same C-level codiagonal identity as
   the corresponding μ-axiom, via [mor_as_cospan_back_compose] +
   [cospan_tensor_mor_as_cospan_back] + [cospan_compose_mor_iso_left]. 

   --------
   * ** 共跨层级余单元公理（单元公理的对偶）

   每个 δ 公理通过 [mor_as_cospan_back_compose] + [cospan_tensor_mor_as_cospan_back] + [cospan_compose_mor_iso_left] 分解为与相应 μ 公理相同的 C 层级余对角恒等式。
*)

(*
   * [bimap delta id ∘ delta ≈ from tensor_assoc ∘ bimap id delta ∘ delta]. 

   --------
   *  [bimap delta id ∘ delta ≈ from tensor_assoc ∘ bimap id delta ∘ delta] .
*)
Lemma cospan_delta_coassoc (X : C) :
  cospan_equiv
    (cospan_compose HP
       (cospan_tensor (cospan_scfa_delta X) (cospan_id X))
       (cospan_scfa_delta X))
    (cospan_compose HP
       (cospan_compose HP
          (mor_as_cospan (from (@coprod_assoc C H_Coc X X X)))
          (cospan_tensor (cospan_id X) (cospan_scfa_delta X)))
       (cospan_scfa_delta X)).
Proof.
  unfold cospan_scfa_delta.
  (*
 LHS: compose (cospan_tensor (back (id▽id)) (cospan_id X)) (back (id▽id))
 ≈ compose (back (cover (id▽id) id)) (back (id▽id))      [tensor_back + id_as_back]
 ≈ back ((id▽id) ∘ cover (id▽id) id)                     [back_compose]                

 --------
 LHS：组合（cospan_tensor（back（id▽id））（cospan_id X））（back（id▽id））
 ≈ 组合（back（cover（id▽id） id））（back（id▽id））       [tensor_back + id_as_back] 
 ≈ back（（id▽id） ∘ cover（id▽id） id）                      [back_compose]
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_equiv_trans with
        (g := cospan_tensor (mor_as_cospan_back (id[X] ▽ id[X]))
                            (mor_as_cospan_back id[X])).
      + apply cospan_tensor_respects.
        * apply cospan_equiv_refl.
        * apply cospan_id_as_back.
      + apply cospan_tensor_mor_as_cospan_back. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_back_compose. }
  apply cospan_equiv_sym.
  (* RHS handling / RHS 处理 *)
  (*
 By cospan_compose_assoc:  compose (compose A B) C ≈ compose A (compose B C). 

 --------
 通过 cospan_compose_assoc： compose (compose A B) C ≈ compose A (compose B C)。
*)
  eapply cospan_equiv_trans.
  { apply cospan_equiv_sym.
    apply (cospan_compose_assoc HP
             (mor_as_cospan (from (@coprod_assoc C H_Coc X X X)))
             (cospan_tensor (cospan_id X) (Build_CospanArrow X id[X] (id[X] ▽ id[X])))
             (Build_CospanArrow X id[X] (id[X] ▽ id[X]))). }
  (*
 Inner compose: tensor (cospan_id X) (back (id▽id)) ∘ back (id▽id)
 ≈ compose (back (cover id (id▽id))) (back (id▽id))   [tensor + id_as_back]
 ≈ back ((id▽id) ∘ cover id (id▽id))                  [back_compose]                  

 --------
 内部组合：张量 (cospan_id X) (back (id▽id)) ∘ back (id▽id)
 ≈ 组合 (back (cover id (id▽id))) (back (id▽id))    [tensor + id_as_back]
 ≈ back ((id▽id) ∘ cover id (id▽id))                   [back_compose]
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_refl.
      + apply cospan_equiv_trans with
          (g := cospan_tensor (mor_as_cospan_back id[X])
                              (mor_as_cospan_back (id[X] ▽ id[X]))).
        * apply cospan_tensor_respects.
          ++ apply cospan_id_as_back.
          ++ apply cospan_equiv_refl.
        * apply cospan_tensor_mor_as_cospan_back.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply mor_as_cospan_back_compose.
    - apply cospan_equiv_refl. }
  (*
 Now: compose (mor_as_cospan (from α)) (back ((id▽id) ∘ cover id (id▽id))).
 Apply cospan_compose_mor_iso_left with phi = iso_sym coprod_assoc, since
 [to (iso_sym α) = from α] (definitionally). 

 --------
 现在：组合 (mor_as_cospan (来自 α)) (回 ((id▽id) ∘ 覆盖 id (id▽id)))。
 使用 cospan_compose_mor_iso_left 并且 phi = iso_sym coprod_assoc，因为 [to (iso_sym α) = from α]（按定义）。
*)
  eapply cospan_equiv_trans.
  { apply (cospan_compose_mor_iso_left HP
              (mor_as_cospan_back (id[X] ▽ id[X] ∘ cover id[X] (id[X] ▽ id[X])))
              (iso_sym (@coprod_assoc C H_Coc X X X))). }
  (*
 Resulting cospan: Build_CospanArrow X id ((id▽id) ∘ cover id (id▽id) ∘ from phi)
 where from phi = to α. 

 --------
 生成的余跨：Build_CospanArrow X id ((id▽id) ∘ cover id (id▽id) ∘ from phi)
 其中 from phi = to α。
*)
  apply cospan_equiv_sym.
  (*
 LHS-after-reduction (target): mor_as_cospan_back ((id▽id) ∘ cover (id▽id) id) 

 --------
 约简后的左侧 (目标)：mor_as_cospan_back ((id▽id) ∘ cover (id▽id) id)
*)
  unfold mor_as_cospan_back.
  exists iso_id; simpl; split.
  - cat.
  - rewrite id_left.
    apply codiag_assoc.
Defined.

(*
   * [bimap epsilon id ∘ delta ≈ from unit_left]. 

   --------
   *  [bimap epsilon id ∘ delta ≈ from unit_left] .
*)
Lemma cospan_delta_counit_left (X : C) :
  cospan_equiv
    (cospan_compose HP
       (cospan_tensor (cospan_scfa_epsilon X) (cospan_id X))
       (cospan_scfa_delta X))
    (mor_as_cospan (from (@coprod_zero_l C H_Coc H_Ini X))).
Proof.
  unfold cospan_scfa_delta, cospan_scfa_epsilon.
  (*
 LHS: compose (cospan_tensor (back zero) (cospan_id X)) (back (id▽id)) 

 --------
 左边: 组合 (cospan_tensor (back zero) (cospan_id X)) (back (id▽id))
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_equiv_trans with
        (g := cospan_tensor (mor_as_cospan_back zero)
                            (mor_as_cospan_back id[X])).
      + apply cospan_tensor_respects.
        * apply cospan_equiv_refl.
        * apply cospan_id_as_back.
      + apply cospan_tensor_mor_as_cospan_back. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_back_compose. }
  (*
 Now: back ((id▽id) ∘ cover zero id) = back (to coprod_zero_l)  [codiag_eta_left]. 

 --------
 现在: back ((id▽id) ∘ cover zero id) = back (to coprod_zero_l)   [codiag_eta_left] .
*)
  unfold mor_as_cospan, mor_as_cospan_back; simpl.
  (*
 Goal (cospan_equiv f g):
 f = Build_CospanArrow X id[X] ((id▽id) ∘ cover zero id)   apex X,
 in1 = id[X], in2 = (id▽id) ∘ cover zero id = to coprod_zero_l;
 g = mor_as_cospan (from coprod_zero_l)                     apex 0+X,
 in1 = from coprod_zero_l, in2 = id[X].
 The two apexes are X and 0+X, so the witnessing iso phi must have type
 X ≅ 0+X (not X ≅ X); cospan_equiv asks for
 to phi ∘ in1 f ≈ in1 g   and   to phi ∘ in2 f ≈ in2 g. 

 --------
 目标 (cospan_equiv f g):
 f = 构建余笼弧 X id [X]  ((id▽id) ∘ cover zero id)   顶点 X,
 in1 = id [X] , in2 = (id▽id) ∘ cover zero id = 对应 coprod_zero_l;
 g = 将 morphism 转换为余笼 (from coprod_zero_l)                     顶点 0+X,
 in1 = from coprod_zero_l, in2 = id [X] .
 两个顶点是 X 和 0+X，所以见证同构 phi 必须类型为
 X ≅ 0+X（而不是 X ≅ X）；cospan_equiv 要求
 to phi ∘ in1 f ≈ in1 g   并且   to phi ∘ in2 f ≈ in2 g。
*)
  (*
 Take phi = iso_sym coprod_zero_l : X ≅ 0+X, so [to phi = from coprod_zero_l].
 Then to phi ∘ id[X] = from coprod_zero_l = in1 g ✓, and
 to phi ∘ to coprod_zero_l = from coprod_zero_l ∘ to coprod_zero_l = id[X] = in2 g ✓
 (the latter by [iso_from_to], after [codiag_eta_left] rewrites in2 f). 

 --------
 取 phi = iso_sym coprod_zero_l : X ≅ 0+X，那么 [to phi = from coprod_zero_l] 。然后 phi ∘ id [X] = from coprod_zero_l = in1 g ✓，并且 phi ∘ to coprod_zero_l = from coprod_zero_l ∘ to coprod_zero_l = id [X] = in2 g ✓（后者由 [iso_from_to]，在 [codiag_eta_left] 重写 in2 f 之后）。
*)
  exists (iso_sym (@coprod_zero_l C H_Coc H_Ini X)).
  simpl; split.
  - rewrite id_right.
    reflexivity.
  - (* from coprod_zero_l ∘ ((id▽id) ∘ cover zero id) ≈ id / 由 coprod_zero_l ∘ ((id▽id) ∘ cover zero id) ≈ id *)
    rewrite codiag_eta_left.
    apply (iso_from_to (@coprod_zero_l C H_Coc H_Ini X)).
Defined.

(*
   * [bimap id epsilon ∘ delta ≈ from unit_right]. 

   --------
   *  [bimap id epsilon ∘ delta ≈ from unit_right] .
*)
Lemma cospan_delta_counit_right (X : C) :
  cospan_equiv
    (cospan_compose HP
       (cospan_tensor (cospan_id X) (cospan_scfa_epsilon X))
       (cospan_scfa_delta X))
    (mor_as_cospan (from (@coprod_zero_r C H_Coc H_Ini X))).
Proof.
  unfold cospan_scfa_delta, cospan_scfa_epsilon.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_equiv_trans with
        (g := cospan_tensor (mor_as_cospan_back id[X])
                            (mor_as_cospan_back zero)).
      + apply cospan_tensor_respects.
        * apply cospan_id_as_back.
        * apply cospan_equiv_refl.
      + apply cospan_tensor_mor_as_cospan_back. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_back_compose. }
  unfold mor_as_cospan, mor_as_cospan_back; simpl.
  exists (iso_sym (@coprod_zero_r C H_Coc H_Ini X)).
  simpl; split.
  - rewrite id_right.
    reflexivity.
  - rewrite codiag_eta_right.
    apply (iso_from_to (@coprod_zero_r C H_Coc H_Ini X)).
Defined.

(*
   * ** [Monoid (CospanCat C HP) X] for every X 

   --------
   * **  [Monoid (CospanCat C HP) X] 对每个 X
*)

Program Definition cospan_monoid (X : C) :
  @Monoid (CospanCat C HP) (Cospan_Monoidal HP) X := {|
  mu  := cospan_scfa_mu X ;
  eta := cospan_scfa_eta X
|}.
Next Obligation.
  apply cospan_mu_assoc.
Defined.
Next Obligation.
  apply cospan_mu_unit_left.
Defined.
Next Obligation.
  apply cospan_mu_unit_right.
Defined.

(*
   * ** Pushout of the codiagonal with itself collapses

   The pushout [pushout (id ▽ id) (id ▽ id)] has apex canonically X,
   because any cocone [(p, q)] over this span satisfies [p ≈ q]
   (by [merge_inv]: [p ∘ (id ▽ id) ≈ q ∘ (id ▽ id)] gives
   [p ▽ p ≈ q ▽ q] hence [p ≈ q]).

   In particular, in the abstract pushout [P = pushout (id▽id) (id▽id)],
   [pushout_in1 P ≈ pushout_in2 P]. 

   --------
   * ** 对角线自身的推拉图坍塌

   推拉图  [pushout (id ▽ id) (id ▽ id)] 的顶点规范地为 X，
   因为任何覆盖该跨度的余锥  [(p, q)] 都满足  [p ≈ q] 
   （根据  [merge_inv] ：  [p ∘ (id ▽ id) ≈ q ∘ (id ▽ id)] 给出
   [p ▽ p ≈ q ▽ q] 因此  [p ≈ q] ）。

   特别地，在抽象推拉图  [P = pushout (id▽id) (id▽id)] 中，
   [pushout_in1 P ≈ pushout_in2 P] 。
*)

Lemma pushout_codiag_legs_eq (X : C) :
  let P := pushout (id[X] ▽ id[X] : (X + X)%object ~> X)
                   (id[X] ▽ id[X] : (X + X)%object ~> X)
  in pushout_in1 P ≈ pushout_in2 P.
Proof.
  intros P.
  pose proof (pushout_commutes P) as PC.
  (*
 PC : pushout_in1 P ∘ (id▽id) ≈ pushout_in2 P ∘ (id▽id).
 Compute pushout_in1 P ∘ (id▽id) = pushout_in1 P ∘ inl ▽ pushout_in1 P ∘ inr
 via merge_comp (back/forward).  Actually:
 p ∘ (f ▽ g) = (p ∘ f) ▽ (p ∘ g) by merge_comp.
 So PC becomes (pushout_in1 P ∘ id) ▽ (pushout_in1 P ∘ id)
 ≈ (pushout_in2 P ∘ id) ▽ (pushout_in2 P ∘ id).
 i.e. pushout_in1 P ▽ pushout_in1 P ≈ pushout_in2 P ▽ pushout_in2 P.
 By merge_inv: pushout_in1 P ≈ pushout_in2 P. 

 --------
 PC : pushout_in1 P ∘ (id▽id) ≈ pushout_in2 P ∘ (id▽id)。
 计算 pushout_in1 P ∘ (id▽id) = pushout_in1 P ∘ inl ▽ pushout_in1 P ∘ inr
 通过 merge_comp（反/正）。实际上：
 p ∘ (f ▽ g) = (p ∘ f) ▽ (p ∘ g) 根据 merge_comp。
 因此 PC 变为 (pushout_in1 P ∘ id) ▽ (pushout_in1 P ∘ id)
 ≈ (pushout_in2 P ∘ id) ▽ (pushout_in2 P ∘ id)。
 即 pushout_in1 P ▽ pushout_in1 P ≈ pushout_in2 P ▽ pushout_in2 P。
 根据 merge_inv：pushout_in1 P ≈ pushout_in2 P。
*)
  (*
 p ▽ p ≈ q ▽ q from PC by merge_comp:
 PC : pushout_in1 P ∘ (id ▽ id) ≈ pushout_in2 P ∘ (id ▽ id)
 LHS = (pushout_in1 P ∘ id) ▽ (pushout_in1 P ∘ id) = p ▽ p
 RHS = (pushout_in2 P ∘ id) ▽ (pushout_in2 P ∘ id) = q ▽ q             

 --------
 p ▽ p ≈ q ▽ q 来自 PC 通过 merge_comp:
 PC : pushout_in1 P ∘ (id ▽ id) ≈ pushout_in2 P ∘ (id ▽ id)
 左边 = (pushout_in1 P ∘ id) ▽ (pushout_in1 P ∘ id) = p ▽ p
 右边 = (pushout_in2 P ∘ id) ▽ (pushout_in2 P ∘ id) = q ▽ q
*)
  assert (Heq : (pushout_in1 P ∘ id[X]) ▽ (pushout_in1 P ∘ id[X])
              ≈ (pushout_in2 P ∘ id[X]) ▽ (pushout_in2 P ∘ id[X])).
  { rewrite (merge_comp id[X] id[X] (pushout_in1 P)).
    rewrite (merge_comp id[X] id[X] (pushout_in2 P)).
    exact PC. }
  rewrite !id_right in Heq.
  apply (fst (fst (merge_inv _ _ _ _) Heq)).
Qed.

(*
   * [pushout_apex (pushout (id▽id) (id▽id)) ≅ X], with both pushout legs
   becoming the identity under the iso. 

   --------
   * [pushout_apex (pushout (id▽id) (id▽id)) ≅ X]，两个推出腿在同构下都变为恒等映射。
*)

Lemma pushout_codiag_apex (X : C) :
  pushout_apex (pushout (id[X] ▽ id[X] : (X + X)%object ~> X)
                        (id[X] ▽ id[X])) ≅ X.
Proof.
  set (P := pushout (id[X] ▽ id[X] : (X + X)%object ~> X) (id[X] ▽ id[X])).
  assert (HC : id[X] ∘ (id[X] ▽ id[X]) ≈ id[X] ∘ (id[X] ▽ id[X])) by reflexivity.
  pose (m := pushout_med P HC).
  assert (Hm1 : m ∘ pushout_in1 P ≈ id[X]) by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 P ≈ id[X]) by (apply pushout_med_in2).
  pose (Hleg := pushout_codiag_legs_eq X).
  fold P in Hleg.
  refine {| to := m; from := pushout_in1 P;
            iso_to_from := _; iso_from_to := _ |}.
  - exact Hm1.
  - (* pushout_in1 P ∘ m ≈ id[P]: use pushout_med_eq with cocone (pushout_in1 P, pushout_in2 P). / pushout_in1 P ∘ m ≈ id [P] ：使用 cocone (pushout_in1 P, pushout_in2 P) 的 pushout_med_eq。 *)
    apply (pushout_med_eq P (pushout_commutes P) (pushout_in1 P ∘ m) id[pushout_apex P]).
    + rewrite <- comp_assoc, Hm1. cat.
    + rewrite <- comp_assoc, Hm2.
      rewrite Hleg. cat.
    + cat.
    + cat.
Defined.

(*
   * ** Commutativity axioms

   [mu ∘ braid ≈ mu] : both forward, fuses via [mor_as_cospan_compose].
   [braid ∘ delta ≈ delta] : forward outer, back inner, uses
   [cospan_compose_forward_iso_back]. 

   --------
   * ** 交换律公理

   [mu ∘ braid ≈ mu] ：两者都向前，通过 [mor_as_cospan_compose] 融合。
   [braid ∘ delta ≈ delta] ：向前外部，向后内部，使用 [cospan_compose_forward_iso_back]。
*)

Lemma cospan_mu_commutative (X : C) :
  cospan_equiv
    (cospan_compose HP (cospan_scfa_mu X)
       (mor_as_cospan (paws : (X + X)%object ~{C}~> (X + X)%object)))
    (cospan_scfa_mu X).
Proof.
  unfold cospan_scfa_mu.
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  apply codiag_paws_comm.
Defined.

Lemma cospan_delta_cocommutative (X : C) :
  cospan_equiv
    (cospan_compose HP
       (mor_as_cospan (paws : (X + X)%object ~{C}~> (X + X)%object))
       (cospan_scfa_delta X))
    (cospan_scfa_delta X).
Proof.
  unfold cospan_scfa_delta.
  (*
 compose (mor_as_cospan (to coprod_comm)) (back (id▽id))
 ≈ back ((id▽id) ∘ from coprod_comm)                  [forward_iso_back]
 ≈ back ((id▽id) ∘ paws)                               [from coprod_comm = paws]
 ≈ back (id▽id)                                        [codiag_paws_comm]    

 --------
 compose（mor_as_cospan（to coprod_comm））（back（id▽id））
 ≈ back（（id▽id）∘ from coprod_comm）                   [forward_iso_back] 
 ≈ back（（id▽id）∘ paws）                                [from coprod_comm = paws] 
 ≈ back（id▽id）                                         [codiag_paws_comm]
*)
  eapply cospan_equiv_trans.
  { apply (cospan_compose_forward_iso_back (id[X] ▽ id[X])
             (@coprod_comm C H_Coc X X)). }
  apply mor_as_cospan_back_proper.
  apply codiag_paws_comm.
Defined.

(*
   * ** Frobenius pushout apex calculation

   The Frobenius law decomposes (after [bimap], [tensor_assoc] reductions)
   to a pushout of [cover id (id▽id) ∘ to α] against [cover (id▽id) id],
   both [(X+X)+X → X+X].  This pushout's apex collapses to X by an
   argument analogous to specialness: the pushout's commutativity relation
   forces [pushout_in1 ≈ pushout_in2] via [coprod_ext]. 

   --------
   * ** Frobenius 推出顶点计算

   Frobenius 定律（在 [bimap]、[tensor_assoc] 约简之后）分解为 [cover id (id▽id) ∘ to α] 对 [cover (id▽id) id] 的推出，两者都是 [(X+X)+X → X+X]。这个推出的顶点通过类似于特殊性的论证坍缩为 X：推出的交换关系通过 [coprod_ext] 强制 [pushout_in1 ≈ pushout_in2]。
*)

Lemma frob_pushout_legs_eq (X : C) :
  let P := pushout
             ((cover id[X] (id[X] ▽ id[X]) ∘ to (@coprod_assoc C H_Coc X X X))
                : ((X + X) + X)%object ~> (X + X)%object)
             (cover (id[X] ▽ id[X]) id[X])
  in pushout_in1 P ≈ pushout_in2 P.
Proof.
  intros P.
  pose proof (pushout_commutes P) as PC.
  (*
 From PC, prove three sub-equations via coprod_ext on the (X+X)+X domain. 

 --------
 从 PC，使用 coprod_ext 在 (X+X)+X 域上证明三个子方程。
*)
  assert (Eq1 : pushout_in1 P ∘ inl ≈ pushout_in2 P ∘ inl).
  { (* PC ∘ (inl ∘ inl) gives this after reduction. / PC ∘ (inl ∘ inl) 在归约后得到这个。 *)
    assert (H : (pushout_in1 P ∘ (cover id[X] (id[X] ▽ id[X])
                                  ∘ to coprod_assoc)) ∘ (inl ∘ inl)
              ≈ (pushout_in2 P ∘ cover (id[X] ▽ id[X]) id[X]) ∘ (inl ∘ inl))
      by (rewrite PC; reflexivity).
    rewrite <- !comp_assoc in H.
    rewrite assoc_to_inl_inl in H.
    rewrite cover_inl in H.
    rewrite id_right in H.
    rewrite (comp_assoc (cover (id[X] ▽ id[X]) id[X]) inl inl) in H.
    rewrite cover_inl in H.
    rewrite <- (comp_assoc inl (id[X] ▽ id[X]) inl) in H.
    rewrite inl_merge in H.
    rewrite id_right in H.
    exact H. }
  assert (Eq3 : pushout_in1 P ∘ inr ≈ pushout_in2 P ∘ inr).
  { assert (H : (pushout_in1 P ∘ (cover id[X] (id[X] ▽ id[X])
                                  ∘ to coprod_assoc)) ∘ inr
              ≈ (pushout_in2 P ∘ cover (id[X] ▽ id[X]) id[X]) ∘ inr)
      by (rewrite PC; reflexivity).
    rewrite <- !comp_assoc in H.
    rewrite assoc_to_inr in H.
    rewrite (comp_assoc (cover id[X] (id[X] ▽ id[X])) inr inr) in H.
    rewrite cover_inr in H.
    rewrite <- (comp_assoc inr (id[X] ▽ id[X]) inr) in H.
    rewrite inr_merge in H.
    rewrite id_right in H.
    rewrite cover_inr in H.
    rewrite id_right in H.
    exact H. }
  apply coprod_ext; assumption.
Qed.

(*
   * Companion lemma: [pushout_in1 P ∘ inl ≈ pushout_in1 P ∘ inr], derived
   from the additional cross constraint [pushout_in1 ∘ inr ≈ pushout_in2 ∘ inl]
   obtained by post-composing [pushout_commutes] with [inl ∘ inr]. 

   --------
   * 伴随引理：[pushout_in1 P ∘ inl ≈ pushout_in1 P ∘ inr]，来源于附加的交叉约束[pushout_in1 ∘ inr ≈ pushout_in2 ∘ inl]，该约束是通过将[pushout_commutes]与[inl ∘ inr]后合成得到的。
*)

Lemma frob_pushout_in1_collapse (X : C) :
  let P := pushout
             ((cover id[X] (id[X] ▽ id[X]) ∘ to (@coprod_assoc C H_Coc X X X))
                : ((X + X) + X)%object ~> (X + X)%object)
             (cover (id[X] ▽ id[X]) id[X])
  in pushout_in1 P ∘ (inl ∘ (id[X] ▽ id[X] : (X + X)%object ~> X))
     ≈ pushout_in1 P.
Proof.
  intros P.
  pose proof (pushout_commutes P) as PC.
  assert (Cross : pushout_in1 P ∘ inr ≈ pushout_in2 P ∘ inl).
  { assert (H : (pushout_in1 P ∘ (cover id[X] (id[X] ▽ id[X])
                                  ∘ to coprod_assoc)) ∘ (inl ∘ inr)
              ≈ (pushout_in2 P ∘ cover (id[X] ▽ id[X]) id[X]) ∘ (inl ∘ inr))
      by (rewrite PC; reflexivity).
    rewrite <- !comp_assoc in H.
    rewrite assoc_to_inl_inr in H.
    rewrite (comp_assoc (cover id[X] (id[X] ▽ id[X])) inr inl) in H.
    rewrite cover_inr in H.
    rewrite <- (comp_assoc inr (id[X] ▽ id[X]) inl) in H.
    rewrite inl_merge in H.
    rewrite id_right in H.
    rewrite (comp_assoc (cover (id[X] ▽ id[X]) id[X]) inl inr) in H.
    rewrite cover_inl in H.
    rewrite <- (comp_assoc inl (id[X] ▽ id[X]) inr) in H.
    rewrite inr_merge in H.
    rewrite id_right in H.
    exact H. }
  assert (Hleg : pushout_in1 P ≈ pushout_in2 P).
  { unfold P. apply frob_pushout_legs_eq. }
  apply coprod_ext.
  - rewrite <- !comp_assoc.
    rewrite inl_merge.
    rewrite id_right.
    reflexivity.
  - rewrite <- !comp_assoc.
    rewrite inr_merge.
    rewrite id_right.
    rewrite Cross.
    apply (compose_respects _ _ Hleg inl inl).
    reflexivity.
Qed.

(** Apex iso for the Frobenius pushout. / Frobenius 推出（pushout）的 Apex iso。 *)
Lemma frob_pushout_apex (X : C) :
  pushout_apex (pushout
    ((cover id[X] (id[X] ▽ id[X]) ∘ to (@coprod_assoc C H_Coc X X X))
       : ((X + X) + X)%object ~> (X + X)%object)
    (cover (id[X] ▽ id[X]) id[X])) ≅ X.
Proof.
  set (P := pushout ((cover id[X] (id[X] ▽ id[X]) ∘ to (@coprod_assoc C H_Coc X X X))
                       : ((X + X) + X)%object ~> (X + X)%object)
                    (cover (id[X] ▽ id[X]) id[X])).
  (*
 Mediator P → X using the (id▽id, id▽id) cocone.
 Hcomm: (id▽id) ∘ (cover id (id▽id) ∘ to α) ≈ (id▽id) ∘ cover (id▽id) id
 LHS: by codiag_cover, = (id ▽ (id▽id)) ∘ to α
 RHS: by codiag_cover, = (id▽id) ▽ id
 These are equal by codiag_assoc (after rewrites). 

 --------
 使用 (id▽id, id▽id) 上锥的中介者 P → X。
 Hcomm: (id▽id) ∘ (cover id (id▽id) ∘ to α) ≈ (id▽id) ∘ cover (id▽id) id
 左边: 通过 codiag_cover，= (id ▽ (id▽id)) ∘ to α
 右边: 通过 codiag_cover，= (id▽id) ▽ id
 通过 codiag_assoc（在重写之后）它们相等。
*)
  assert (HC : (id[X] ▽ id[X]) ∘ (cover id[X] (id[X] ▽ id[X]) ∘ to coprod_assoc)
              ≈ (id[X] ▽ id[X]) ∘ cover (id[X] ▽ id[X]) id[X]).
  { rewrite comp_assoc. symmetry. apply codiag_assoc. }
  pose (m := pushout_med P HC).
  assert (Hm1 : m ∘ pushout_in1 P ≈ id[X] ▽ id[X]) by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 P ≈ id[X] ▽ id[X]) by (apply pushout_med_in2).
  pose (Hleg := frob_pushout_legs_eq X).
  fold P in Hleg.
  refine {| to := m; from := pushout_in1 P ∘ inl;
            iso_to_from := _; iso_from_to := _ |}.
  - (* m ∘ (pushout_in1 P ∘ inl) ≈ id[X] / m ∘ (pushout_in1 P ∘ inl) ≈ id [X] *)
    rewrite comp_assoc.
    rewrite Hm1.
    apply inl_merge.
  - (* (pushout_in1 P ∘ inl) ∘ m ≈ id[P]: use pushout_med_eq. / (pushout_in1 P ∘ inl) ∘ m ≈ id [P] ：使用 pushout_med_eq。 *)
    apply (pushout_med_eq P (pushout_commutes P)
                          ((pushout_in1 P ∘ inl) ∘ m) id[pushout_apex P]).
    + (* ((pushout_in1 P ∘ inl) ∘ m) ∘ pushout_in1 P ≈ pushout_in1 P Step: rewrite <- comp_assoc twice (the m and inl): pushout_in1 P ∘ inl ∘ (m ∘ pushout_in1 P) = pushout_in1 P ∘ inl ∘ (id▽id) Then expand by coprod_ext: ∘ inl gives pushout_in1 ∘ inl ∘ id = pushout_in1 ∘ inl. ∘ inr gives pushout_in1 ∘ inl ∘ id = pushout_in1 ∘ inl ≈ pushout_in1 ∘ inr (by Hleg). So overall ≈ pushout_in1 P. / ((pushout_in1 P ∘ inl) ∘ m) ∘ pushout_in1 P ≈ pushout_in1 P 步骤：两次重写 <- comp_assoc（针对 m 和 inl）： pushout_in1 P ∘ inl ∘ (m ∘ pushout_in1 P) = pushout_in1 P ∘ inl ∘ (id▽id) 然后通过 coprod_ext 展开：∘ inl 给出 pushout_in1 ∘ inl ∘ id = pushout_in1 ∘ inl。 ∘ inr 给出 pushout_in1 ∘ inl ∘ id = pushout_in1 ∘ inl ≈ pushout_in1 ∘ inr（根据 Hleg）。 因此整体 ≈ pushout_in1 P。 *)
      rewrite <- !comp_assoc.
      rewrite Hm1.
      assert (Hcoll : pushout_in1 P ∘ (inl ∘ (id[X] ▽ id[X])) ≈ pushout_in1 P).
      { unfold P. apply frob_pushout_in1_collapse. }
      exact Hcoll.
    + (* ((pushout_in1 P ∘ inl) ∘ m) ∘ pushout_in2 P ≈ pushout_in2 P / ((pushout_in1 P ∘ inl) ∘ m) ∘ pushout_in2 P ≈ pushout_in2 P *)
      rewrite <- !comp_assoc.
      rewrite Hm2.
      assert (Hcoll : pushout_in1 P ∘ (inl ∘ (id[X] ▽ id[X])) ≈ pushout_in1 P).
      { unfold P. apply frob_pushout_in1_collapse. }
      rewrite Hcoll.
      exact Hleg.
    + cat.
    + cat.
Defined.

(** Mirror version: pushout for [frob_law_right]. / 镜像版本：[frob_law_right] 的推送版本。 *)

Lemma frob_pushout_legs_eq_R (X : C) :
  let P := pushout
             ((cover (id[X] ▽ id[X]) id[X] ∘ from (@coprod_assoc C H_Coc X X X))
                : (X + (X + X))%object ~> (X + X)%object)
             (cover id[X] (id[X] ▽ id[X]))
  in pushout_in1 P ≈ pushout_in2 P.
Proof.
  intros P.
  pose proof (pushout_commutes P) as PC.
  (*
 PC ∘ inl: gives pushout_in1 ∘ inl ≈ pushout_in2 ∘ inl. 

 --------
 PC ∘ inl: 给出 pushout_in1 ∘ inl ≈ pushout_in2 ∘ inl。
*)
  assert (Eq1 : pushout_in1 P ∘ inl ≈ pushout_in2 P ∘ inl).
  { assert (H : (pushout_in1 P ∘ (cover (id[X] ▽ id[X]) id[X] ∘ from coprod_assoc)) ∘ inl
              ≈ (pushout_in2 P ∘ cover id[X] (id[X] ▽ id[X])) ∘ inl)
      by (rewrite PC; reflexivity).
    rewrite <- !comp_assoc in H.
    rewrite assoc_from_inl in H.
    rewrite (comp_assoc (cover (id[X] ▽ id[X]) id[X]) inl inl) in H.
    rewrite cover_inl in H.
    rewrite <- (comp_assoc inl (id[X] ▽ id[X]) inl) in H.
    rewrite inl_merge in H.
    rewrite id_right in H.
    rewrite cover_inl in H.
    rewrite id_right in H.
    exact H. }
  (*
 PC ∘ (inr ∘ inr): gives pushout_in1 ∘ inr ≈ pushout_in2 ∘ inr. 

 --------
 PC ∘ (inr ∘ inr)：得到 pushout_in1 ∘ inr ≈ pushout_in2 ∘ inr。
*)
  assert (Eq3 : pushout_in1 P ∘ inr ≈ pushout_in2 P ∘ inr).
  { assert (H : (pushout_in1 P ∘ (cover (id[X] ▽ id[X]) id[X] ∘ from coprod_assoc)) ∘ (inr ∘ inr)
              ≈ (pushout_in2 P ∘ cover id[X] (id[X] ▽ id[X])) ∘ (inr ∘ inr))
      by (rewrite PC; reflexivity).
    rewrite <- !comp_assoc in H.
    rewrite assoc_from_inr_inr in H.
    rewrite cover_inr in H.
    rewrite id_right in H.
    rewrite (comp_assoc (cover id[X] (id[X] ▽ id[X])) inr inr) in H.
    rewrite cover_inr in H.
    rewrite <- (comp_assoc inr (id[X] ▽ id[X]) inr) in H.
    rewrite inr_merge in H.
    rewrite id_right in H.
    exact H. }
  apply coprod_ext; assumption.
Qed.

Lemma frob_pushout_in2_collapse_R (X : C) :
  let P := pushout
             ((cover (id[X] ▽ id[X]) id[X] ∘ from (@coprod_assoc C H_Coc X X X))
                : (X + (X + X))%object ~> (X + X)%object)
             (cover id[X] (id[X] ▽ id[X]))
  in pushout_in2 P ∘ (inl ∘ (id[X] ▽ id[X] : (X + X)%object ~> X))
     ≈ pushout_in2 P.
Proof.
  intros P.
  pose proof (pushout_commutes P) as PC.
  (*
 Cross constraint: PC ∘ (inr ∘ inl) gives pushout_in1 ∘ inl ≈ pushout_in2 ∘ inr. 

 --------
 交叉约束：PC ∘ (inr ∘ inl) 等于 pushout_in1 ∘ inl ≈ pushout_in2 ∘ inr。
*)
  assert (Cross : pushout_in1 P ∘ inl ≈ pushout_in2 P ∘ inr).
  { assert (H : (pushout_in1 P ∘ (cover (id[X] ▽ id[X]) id[X] ∘ from coprod_assoc)) ∘ (inr ∘ inl)
              ≈ (pushout_in2 P ∘ cover id[X] (id[X] ▽ id[X])) ∘ (inr ∘ inl))
      by (rewrite PC; reflexivity).
    rewrite <- !comp_assoc in H.
    rewrite assoc_from_inr_inl in H.
    rewrite (comp_assoc (cover (id[X] ▽ id[X]) id[X]) inl inr) in H.
    rewrite cover_inl in H.
    rewrite <- (comp_assoc inl (id[X] ▽ id[X]) inr) in H.
    rewrite inr_merge in H.
    rewrite id_right in H.
    rewrite (comp_assoc (cover id[X] (id[X] ▽ id[X])) inr inl) in H.
    rewrite cover_inr in H.
    rewrite <- (comp_assoc inr (id[X] ▽ id[X]) inl) in H.
    rewrite inl_merge in H.
    rewrite id_right in H.
    exact H. }
  assert (Hleg : pushout_in1 P ≈ pushout_in2 P).
  { unfold P. apply frob_pushout_legs_eq_R. }
  apply coprod_ext.
  - rewrite <- !comp_assoc.
    rewrite inl_merge.
    rewrite id_right.
    reflexivity.
  - rewrite <- !comp_assoc.
    rewrite inr_merge.
    rewrite id_right.
    rewrite <- Cross.
    symmetry.
    rewrite Hleg at 1.
    reflexivity.
Qed.

Lemma frob_pushout_apex_R (X : C) :
  pushout_apex (pushout
    ((cover (id[X] ▽ id[X]) id[X] ∘ from (@coprod_assoc C H_Coc X X X))
       : (X + (X + X))%object ~> (X + X)%object)
    (cover id[X] (id[X] ▽ id[X]))) ≅ X.
Proof.
  set (P := pushout
              ((cover (id[X] ▽ id[X]) id[X] ∘ from (@coprod_assoc C H_Coc X X X))
                 : (X + (X + X))%object ~> (X + X)%object)
              (cover id[X] (id[X] ▽ id[X]))).
  (*
 Cocone (id▽id, id▽id) over the span:
 Hcomm: (id▽id) ∘ (cover (id▽id) id ∘ from α) ≈ (id▽id) ∘ cover id (id▽id)
 LHS: by codiag_cover, (id▽id) ∘ cover (id▽id) id ∘ from α
 = ((id▽id) ▽ id) ∘ from α.
 RHS: by codiag_cover, = id ▽ (id▽id).
 Need: ((id▽id) ▽ id) ∘ from α ≈ id ▽ (id▽id).
 This is codiag_assoc rewritten using iso_to/from cancellation. 

 --------
 在跨度上的余锥 Cocone (id▽id, id▽id)：
 Hcomm: (id▽id) ∘ (cover (id▽id) id ∘ from α) ≈ (id▽id) ∘ cover id (id▽id)
 左侧：根据 codiag_cover，(id▽id) ∘ cover (id▽id) id ∘ from α
 = ((id▽id) ▽ id) ∘ from α。
 右侧：根据 codiag_cover，= id ▽ (id▽id)。
 需要：((id▽id) ▽ id) ∘ from α ≈ id ▽ (id▽id)。
 这是使用 iso_to/from 消去法重写的 codiag_assoc。
*)
  assert (HC : (id[X] ▽ id[X]) ∘ (cover (id[X] ▽ id[X]) id[X] ∘ from coprod_assoc)
              ≈ (id[X] ▽ id[X]) ∘ cover id[X] (id[X] ▽ id[X])).
  { rewrite comp_assoc.
    rewrite codiag_cover.
    (*
 Now need: ((id▽id) ▽ id) ∘ from α ≈ (id▽id) ∘ cover id (id▽id) 

 --------
 现在需要：((id▽id) ▽ id) ∘ 从 α ≈ (id▽id) ∘ 覆盖 id (id▽id)
*)
    pose proof (@codiag_assoc X) as Ha.
    (*
 Ha: (id▽id) ∘ cover (id▽id) id ≈ (id▽id) ∘ cover id (id▽id) ∘ to α 

 --------
 Ha: (id▽id) ∘ cover (id▽id) id ≈ (id▽id) ∘ cover id (id▽id) ∘ to α
*)
    rewrite codiag_cover in Ha.
    (*
 Ha: (id▽id) ▽ id ≈ (id▽id) ∘ cover id (id▽id) ∘ to α 

 --------
 Ha: (id▽id) ▽ id ≈ (id▽id) ∘ cover id (id▽id) ∘ 到 α
*)
    rewrite Ha.
    rewrite <- !comp_assoc.
    rewrite iso_to_from.
    rewrite id_right.
    reflexivity. }
  pose (m := pushout_med P HC).
  assert (Hm1 : m ∘ pushout_in1 P ≈ id[X] ▽ id[X]) by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 P ≈ id[X] ▽ id[X]) by (apply pushout_med_in2).
  pose proof (frob_pushout_legs_eq_R X) as Hleg.
  cbn beta zeta in Hleg.
  fold P in Hleg.
  refine {| to := m; from := pushout_in2 P ∘ inl;
            iso_to_from := _; iso_from_to := _ |}.
  - (* m ∘ (pushout_in2 P ∘ inl) ≈ id[X] / m ∘ (pushout_in2 P ∘ inl) ≈ id [X] *)
    rewrite comp_assoc.
    rewrite Hm2.
    apply inl_merge.
  - (* (pushout_in2 P ∘ inl) ∘ m ≈ id[P] / (pushout_in2 P ∘ inl) ∘ m ≈ id [P] *)
    apply (pushout_med_eq P (pushout_commutes P)
                          ((pushout_in2 P ∘ inl) ∘ m) id[pushout_apex P]).
    + rewrite <- !comp_assoc.
      rewrite Hm1.
      assert (Hcoll : pushout_in2 P ∘ (inl ∘ (id[X] ▽ id[X])) ≈ pushout_in2 P).
      { unfold P. apply frob_pushout_in2_collapse_R. }
      rewrite Hcoll.
      symmetry. exact Hleg.
    + rewrite <- !comp_assoc.
      rewrite Hm2.
      assert (Hcoll : pushout_in2 P ∘ (inl ∘ (id[X] ▽ id[X])) ≈ pushout_in2 P).
      { unfold P. apply frob_pushout_in2_collapse_R. }
      exact Hcoll.
    + cat.
    + cat.
Defined.

(*
   * ** Frobenius laws

   LHS = [bimap mu id ∘ from α ∘ bimap id delta] and
   RHS = [delta ∘ mu], where both reduce to the cospan with apex X and
   legs (id ▽ id, id ▽ id). 

   --------
   * ** Frobenius 定律

   左边 = [bimap mu id ∘ from α ∘ bimap id delta]
   右边 = [delta ∘ mu]，二者都化简为顶点为 X 且边为 (id ▽ id, id ▽ id) 的余跨度。
*)

Lemma cospan_frob_law_left (X : C) :
  cospan_equiv
    (cospan_compose HP
       (cospan_tensor (cospan_scfa_mu X) (cospan_id X))
       (cospan_compose HP
          (mor_as_cospan (from (@coprod_assoc C H_Coc X X X)))
          (cospan_tensor (cospan_id X) (cospan_scfa_delta X))))
    (cospan_compose HP (cospan_scfa_delta X) (cospan_scfa_mu X)).
Proof.
  unfold cospan_scfa_mu, cospan_scfa_delta.
  (*
 LHS: convert each bimap (cospan_id) to (mor_as_cospan_back id), then fuse tensors. 

 --------
 左边：将每个双映射（cospan_id）转换为（mor_as_cospan_back id），然后融合张量。
*)
  (*
 Inner of LHS: cospan_tensor (cospan_id X) (back (id▽id)) ≈ back (cover id (id▽id)). 

 --------
 左侧内部：cospan_tensor (cospan_id X) (back (id▽id)) ≈ back (cover id (id▽id))。
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_trans with
          (g := cospan_tensor (mor_as_cospan_back id[X])
                              (mor_as_cospan_back (id[X] ▽ id[X]))).
        * apply cospan_tensor_respects.
          ++ apply cospan_id_as_back.
          ++ apply cospan_equiv_refl.
        * apply cospan_tensor_mor_as_cospan_back.
      + apply cospan_equiv_refl.
    - apply cospan_equiv_refl. }
  (*
 Now: compose (compose (mor_as_cospan (from α)) (back (cover id (id▽id)))) tensor.
 Apply cospan_compose_forward_iso_back to inner compose. 

 --------
 现在：组合 (组合 (mor_as_cospan (from α)) (back (cover id (id▽id)))) 张量。
 应用 cospan_compose_forward_iso_back 到内部组合。
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply (cospan_compose_forward_iso_back (cover id[X] (id[X] ▽ id[X]))
              (iso_sym (@coprod_assoc C H_Coc X X X))).
    - apply cospan_equiv_refl. }
  (*
 Now: compose (back (cover id (id▽id) ∘ to coprod_assoc)) (cospan_tensor mu cospan_id).
 Reduce outer tensor: cospan_tensor (mor_as_cospan (id▽id)) (cospan_id X)
 ≈ mor_as_cospan (cover (id▽id) id). 

 --------
 现在：组合 (back (cover id (id▽id) ∘ to coprod_assoc)) (cospan_tensor mu cospan_id)。
 简化外部张量：cospan_tensor (mor_as_cospan (id▽id)) (cospan_id X)
 ≈ mor_as_cospan (cover (id▽id) id)。
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_equiv_trans with
        (g := cospan_tensor (mor_as_cospan (id[X] ▽ id[X]))
                            (mor_as_cospan id[X])).
      + apply cospan_tensor_respects.
        * apply cospan_equiv_refl.
        * apply cospan_equiv_sym, mor_as_cospan_id.
      + apply cospan_tensor_mor_as_cospan. }
  (*
 Now: compose (back (cover id (id▽id) ∘ to coprod_assoc))
 (mor_as_cospan (cover (id▽id) id))
 The outer is "back", inner is "forward".  This is a genuine pushout
 (the Frobenius pushout). 

 --------
 现在：组合 (back (cover id (id▽id) ∘ to coprod_assoc))
 (mor_as_cospan (cover (id▽id) id))
 外层是“back”，内层是“forward”。这是一个真正的推突
 （Frobenius 推突）。
*)
  apply cospan_equiv_sym.
  (*
 RHS = compose (back (id▽id)) (mor_as_cospan (id▽id)).
 By cospan_compose_mor_as_cospan_back_left (with outer = back (id▽id), inner = mor_as_cospan (id▽id)):
 ≈ Build_CospanArrow X (in1 inner) (in2 inner ∘ (id▽id))
 = Build_CospanArrow X (id▽id) (id ∘ (id▽id))
 = Build_CospanArrow X (id▽id) (id▽id)                              

 --------
 RHS = 组成 (back (id▽id)) (mor_as_cospan (id▽id))。
 由 cospan_compose_mor_as_cospan_back_left（外部 = back (id▽id)，内部 = mor_as_cospan (id▽id)）：
 ≈ Build_CospanArrow X (in1 内部) (in2 内部 ∘ (id▽id))
 = Build_CospanArrow X (id▽id) (id ∘ (id▽id))
 = Build_CospanArrow X (id▽id) (id▽id)
*)
  eapply cospan_equiv_trans.
  { apply (cospan_compose_mor_as_cospan_back_left (id[X] ▽ id[X])
             (mor_as_cospan (id[X] ▽ id[X]))). }
  apply cospan_equiv_sym.
  unfold cospan_compose, mor_as_cospan, mor_as_cospan_back; simpl.
  (*
 LHS apex: pushout (cover id (id▽id) ∘ to α) (cover (id▽id) id) ≅ X (via frob_pushout_apex).
 LHS legs (after iso): pushout_in1 P ∘ id[X+X] = pushout_in1 P, pushout_in2 P ∘ id[X+X] = pushout_in2 P.
 RHS: apex X, in1 = id▽id (from in1 inner of cospan_compose_back_left =
 cospan_in1 (mor_as_cospan (id▽id)) = id▽id),
 in2 = id ∘ (id▽id) = id▽id. 

 --------
 左侧顶点：推出 (cover id (id▽id) ∘ to α) (cover (id▽id) id) ≅ X (通过 frob_pushout_apex)。
 左侧边（经过同构后）：pushout_in1 P ∘ id [X+X]  = pushout_in1 P，pushout_in2 P ∘ id [X+X]  = pushout_in2 P。
 右侧：顶点 X，in1 = id▽id（来自 cospan_compose_back_left 的 in1 内部 = cospan_in1 (mor_as_cospan (id▽id)) = id▽id），
 in2 = id ∘ (id▽id) = id▽id。
*)
  set (P := pushout
              ((cover id[X] (id[X] ▽ id[X]) ∘ to (@coprod_assoc C H_Coc X X X))
                 : ((X + X) + X)%object ~> (X + X)%object)
              (cover (id[X] ▽ id[X]) id[X])).
  exists (frob_pushout_apex X); simpl; fold P; split.
  - (* to (frob_pushout_apex X) ∘ (pushout_in1 P ∘ id[X+X]) ≈ id[X] ▽ id[X] / 转到 (frob_pushout_apex X) ∘ (pushout_in1 P ∘ id [X+X] ) ≈ id [X] ▽ id [X] *)
    rewrite id_right.
    unfold frob_pushout_apex; simpl.
    apply pushout_med_in1.
  - rewrite id_right.
    unfold frob_pushout_apex; simpl.
    rewrite pushout_med_in2.
    rewrite id_left.
    reflexivity.
Defined.

(*
   * Mirror of [cospan_frob_law_left]:
   [bimap id mu ∘ to α ∘ bimap delta id ≈ delta ∘ mu]. 

   --------
   * [cospan_frob_law_left] 的镜子：
   [bimap id mu ∘ to α ∘ bimap delta id ≈ delta ∘ mu] 。
*)
Lemma cospan_frob_law_right (X : C) :
  cospan_equiv
    (cospan_compose HP
       (cospan_tensor (cospan_id X) (cospan_scfa_mu X))
       (cospan_compose HP
          (mor_as_cospan (to (@coprod_assoc C H_Coc X X X)))
          (cospan_tensor (cospan_scfa_delta X) (cospan_id X))))
    (cospan_compose HP (cospan_scfa_delta X) (cospan_scfa_mu X)).
Proof.
  unfold cospan_scfa_mu, cospan_scfa_delta.
  (*
 Inner of LHS: cospan_tensor (back (id▽id)) (cospan_id X)
 ≈ back (cover (id▽id) id). 

 --------
 左侧内部：cospan_tensor（back（id▽id））（cospan_id X）
 ≈ back（cover（id▽id）id）。
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_trans with
          (g := cospan_tensor (mor_as_cospan_back (id[X] ▽ id[X]))
                              (mor_as_cospan_back id[X])).
        * apply cospan_tensor_respects.
          ++ apply cospan_equiv_refl.
          ++ apply cospan_id_as_back.
        * apply cospan_tensor_mor_as_cospan_back.
      + apply cospan_equiv_refl.
    - apply cospan_equiv_refl. }
  (*
 Now inner is compose (mor_as_cospan (to α)) (back (cover (id▽id) id)).
 Apply cospan_compose_forward_iso_back with g = cover (id▽id) id, phi = coprod_assoc. 

 --------
 现在 inner 是 compose (mor_as_cospan (to α)) (back (cover (id▽id) id))。
 应用 cospan_compose_forward_iso_back，令 g = cover (id▽id) id，phi = coprod_assoc。
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply (cospan_compose_forward_iso_back (cover (id[X] ▽ id[X]) id[X])
              (@coprod_assoc C H_Coc X X X)).
    - apply cospan_equiv_refl. }
  (*
 Now: compose (back (cover (id▽id) id ∘ from coprod_assoc))
 (cospan_tensor (cospan_id X) μ).
 Outer tensor: cospan_tensor (cospan_id X) μ
 ≈ mor_as_cospan (cover id (id▽id)). 

 --------
 现在：组合 (back (cover (id▽id) id ∘ from coprod_assoc))
 (cospan_tensor (cospan_id X) μ)。
 外张量：cospan_tensor (cospan_id X) μ
 ≈ mor_as_cospan (cover id (id▽id))。
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_equiv_trans with
        (g := cospan_tensor (mor_as_cospan id[X])
                            (mor_as_cospan (id[X] ▽ id[X]))).
      + apply cospan_tensor_respects.
        * apply cospan_equiv_sym, mor_as_cospan_id.
        * apply cospan_equiv_refl.
      + apply cospan_tensor_mor_as_cospan. }
  apply cospan_equiv_sym.
  (*
 RHS = compose (back (id▽id)) (mor_as_cospan (id▽id)). 

 --------
 RHS = 组合 (后退 (id▽id)) (mor_as_cospan (id▽id)).
*)
  eapply cospan_equiv_trans.
  { apply (cospan_compose_mor_as_cospan_back_left (id[X] ▽ id[X])
             (mor_as_cospan (id[X] ▽ id[X]))). }
  apply cospan_equiv_sym.
  unfold cospan_compose, mor_as_cospan, mor_as_cospan_back; simpl.
  set (P := pushout
              ((cover (id[X] ▽ id[X]) id[X] ∘ from (@coprod_assoc C H_Coc X X X))
                 : (X + (X + X))%object ~> (X + X)%object)
              (cover id[X] (id[X] ▽ id[X]))).
  exists (frob_pushout_apex_R X); simpl; fold P; split.
  - rewrite comp_assoc.
    rewrite id_right.
    unfold frob_pushout_apex_R; simpl.
    apply pushout_med_in1.
  - rewrite comp_assoc.
    rewrite id_right.
    unfold frob_pushout_apex_R; simpl.
    rewrite pushout_med_in2.
    rewrite id_left.
    reflexivity.
Defined.

(*
   * ** Specialness: μ ∘ δ ≈ id

   [μ ∘ δ : X → X] via [cospan_compose μ δ].  Inner = δ = back (id▽id),
   outer = μ = forward (id▽id).  The pushout [pushout (id▽id) (id▽id)]
   collapses via [pushout_codiag_apex]. 

   --------
   * ** 特殊性: μ ∘ δ ≈ id

   [μ ∘ δ : X → X]  通过  [cospan_compose μ δ] 。 内部 = δ = 回退 (id▽id)，
   外部 = μ = 前进 (id▽id)。 推出  [pushout (id▽id) (id▽id)] 
   通过  [pushout_codiag_apex] 折叠。
*)

Lemma cospan_mu_delta_id (X : C) :
  cospan_equiv
    (cospan_compose HP (cospan_scfa_mu X) (cospan_scfa_delta X))
    (cospan_id X).
Proof.
  unfold cospan_scfa_mu, cospan_scfa_delta.
  unfold cospan_compose, cospan_id, mor_as_cospan; simpl.
  set (P := pushout ((id[X] ▽ id[X]) : (X + X)%object ~{C}~> X)
                    ((id[X] ▽ id[X]) : (X + X)%object ~{C}~> X)).
  exists (pushout_codiag_apex X).
  simpl; fold P; split.
  - (* to iso ∘ (pushout_in1 P ∘ id[X]) ≈ id[X] / 到 iso ∘ (pushout_in1 P ∘ id [X] ) ≈ id [X] *)
    rewrite comp_assoc.
    rewrite id_right.
    unfold pushout_codiag_apex; simpl.
    apply pushout_med_in1.
  - (* to iso ∘ (pushout_in2 P ∘ id[X]) ≈ id[X] / 到 iso ∘ (pushout_in2 P ∘ id [X] ) ≈ id [X] *)
    rewrite comp_assoc.
    rewrite id_right.
    unfold pushout_codiag_apex; simpl.
    apply pushout_med_in2.
Defined.

(*
   * ** [Comonoid (CospanCat C HP) X] for every X 

   --------
   * **  [Comonoid (CospanCat C HP) X] 对每个 X
*)

Program Definition cospan_comonoid (X : C) :
  @Comonoid (CospanCat C HP) (Cospan_Monoidal HP) X := {|
  delta   := cospan_scfa_delta X ;
  epsilon := cospan_scfa_epsilon X
|}.
Next Obligation.
  apply cospan_delta_coassoc.
Defined.
Next Obligation.
  apply cospan_delta_counit_left.
Defined.
Next Obligation.
  apply cospan_delta_counit_right.
Defined.

(*
   * ** [Frobenius (CospanCat C HP) X] for every X 

   --------
   * **  [Frobenius (CospanCat C HP) X] 对每个 X
*)

Program Definition cospan_frobenius (X : C) :
  @Frobenius (CospanCat C HP) (Cospan_Monoidal HP) X := {|
  frob_monoid   := cospan_monoid X ;
  frob_comonoid := cospan_comonoid X
|}.
Next Obligation.
  eapply cospan_equiv_trans.
  { apply cospan_equiv_sym. apply cospan_compose_assoc. }
  apply (cospan_frob_law_left X).
Defined.
Next Obligation.
  eapply cospan_equiv_trans.
  { apply cospan_equiv_sym. apply cospan_compose_assoc. }
  apply (cospan_frob_law_right X).
Defined.

(*
   * ** [CommutativeFrobenius (CospanCat C HP) X] for every X 

   --------
   * **  [CommutativeFrobenius (CospanCat C HP) X] 对每个 X
*)

Program Definition cospan_commutative_frobenius (X : C) :
  @CommutativeFrobenius (CospanCat C HP) (Cospan_SymmetricMonoidal HP) X := {|
  cfrob_frobenius := cospan_frobenius X
|}.
Next Obligation.
  apply cospan_mu_commutative.
Defined.
Next Obligation.
  apply cospan_delta_cocommutative.
Defined.

(*
   * ** [SpecialCommutativeFrobenius (CospanCat C HP) X] for every X 

   --------
   * **  [SpecialCommutativeFrobenius (CospanCat C HP) X] 对每个 X
*)

Program Definition cospan_scfa (X : CospanCat C HP) :
  @SpecialCommutativeFrobenius (CospanCat C HP) (Cospan_SymmetricMonoidal HP) X := {|
  scfa_commutative := cospan_commutative_frobenius X
|}.
Next Obligation.
  apply cospan_mu_delta_id.
Defined.

End CospanSCFA.
