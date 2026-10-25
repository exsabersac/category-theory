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
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.
Require Import Category.Construction.Cospan.SCFA.

Generalizable All Variables.

(*
   * * [Hypergraph (CospanCat C HP)] : the full hypergraph instance

   Building on [cospan_scfa] from [SCFA.v], we discharge the eight
   coherence axioms of the [Hypergraph] class.

   The four UNIT axioms ([scfa_unit_{mu/eta/delta/epsilon}]) follow by
   initiality: every morphism out of [0] is unique, so any cospan with
   apex containing [0] or [0+0] is canonically determined.

   The four TENSOR axioms ([scfa_tensor_{mu/eta/delta/epsilon}]) reduce
   to C-level identities relating the codiagonal/zero structure of
   [X+Y] to the same structure on [X] and [Y] composed through the
   middle-swap [mid_swap X Y].

   This is the concrete hypergraph-category instance for cospans: when
   [C] is cocartesian with an initial object, [CospanCat C HP] is a
   hypergraph category with [I = 0], [tensor = coproduct], and the
   per-object SCFA given by the codiagonal [id ▽ id] and the zero map.

   nLab:      https://ncatlab.org/nlab/show/hypergraph+category
   Wikipedia: no dedicated article (the underlying special commutative
   Frobenius algebra is covered at
   https://en.wikipedia.org/wiki/Frobenius_algebra)
   Reference: Fong & Spivak, Hypergraph Categories, J. Pure Appl. Algebra
   223(11):4746-4777, 2019 (arXiv:1806.08304), hypergraph
   category = Def 4.1.1; Fong, Decorated Cospans
   (arXiv:1502.00872), Theorem 3.5 (the cospan category is a
   symmetric monoidal hypergraph category). 

   --------
   * *  [Hypergraph (CospanCat C HP)] ：完整的超图实例

   在 [SCFA.v] 的 [cospan_scfa] 基础上，我们验证了 [Hypergraph] 类的八条相干公理。

   四条 UNIT 公理（[scfa_unit_{mu/eta/delta/epsilon}]）由初始性得出：每个从 [0] 出发的态射都是唯一的，因此任何顶点包含 [0] 或 [0+0] 的共尖图都是典型确定的。

   四条 TENSOR 公理（[scfa_tensor_{mu/eta/delta/epsilon}]）归结为 C 级的恒等式，将 [X+Y] 的共对角/零结构与通过中间交换 [mid_swap X Y] 组合的 [X] 和 [Y] 的相同结构联系起来。这是针对共span的具体超图范畴实例：当 [C] 是带有初始对象的余笛卡儿范畴时，[CospanCat C HP] 是一个带有 [I = 0]、[tensor = coproduct] 以及由共对角映射 [id ▽ id] 和零映射给出的每对象SCFA的超图范畴。

   nLab: https://ncatlab.org/nlab/show/hypergraph+category
   维基百科: 没有专门的文章（基础的特殊交换弗罗贝nius代数在 https://en.wikipedia.org/wiki/Frobenius_algebra) 中有所介绍）
   参考文献: Fong & Spivak, Hypergraph Categories, J. Pure Appl. Algebra 223(11):4746-4777, 2019 (arXiv:1806.08304), 超图范畴 = 定义 4.1.1; Fong, Decorated Cospans (arXiv:1502.00872), 定理 3.5 (共span范畴是一个对称幺范畴超图范畴)
*)

Section CospanHypergraphInstance.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context (HP : HasPushouts C).

(** ** Unit coherence (cheaper) / ** 单位一致性（更便宜） *)

(*
   * [scfa_mu (scfa I) ≈ to unit_left] : at the cospan level, both
   [mor_as_cospan (id▽id : 0+0 → 0)] and [mor_as_cospan (to coprod_zero_l)]
   are equal because all morphisms with codomain [0] are equal by
   initiality. 

   --------
   *  [scfa_mu (scfa I) ≈ to unit_left] ：在余跨度层面，[mor_as_cospan (id▽id : 0+0 → 0)] 和 [mor_as_cospan (to coprod_zero_l)] 是相等的，因为所有以 [0] 为陪域的态射由于初始性而相等。
*)
Lemma cospan_scfa_unit_mu :
  cospan_equiv
    (cospan_scfa_mu (@Cospan_unit_obj C H_Ini))
    (mor_as_cospan (to (@coprod_zero_l C H_Coc H_Ini
                          (@Cospan_unit_obj C H_Ini)))).
Proof.
  unfold cospan_scfa_mu, Cospan_unit_obj.
  apply mor_as_cospan_proper.
  (*
 (id ▽ id : 0+0 → 0) ≈ (to coprod_zero_l : 0+0 → 0) = (zero ▽ id) 

 --------
 (id ▽ id : 0+0 → 0) ≈ (to coprod_zero_l : 0+0 → 0) = (zero ▽ id)
*)
  unfold to, coprod_zero_l; simpl.
  apply (snd (merge_inv _ _ _ _)).
  split.
  - apply (@zero_unique C H_Ini _ _ _).
  - reflexivity.
Defined.

(*
   * [scfa_eta (scfa I) ≈ id[I]] : both are morphisms in/out of 0; trivial. 

   --------
   *  [scfa_eta (scfa I) ≈ id[I] ]：两者都是从/到 0 的态射；平凡。
*)
Lemma cospan_scfa_unit_eta :
  cospan_equiv
    (cospan_scfa_eta (@Cospan_unit_obj C H_Ini))
    (cospan_id (@Cospan_unit_obj C H_Ini)).
Proof.
  unfold cospan_scfa_eta, Cospan_unit_obj.
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_proper.
    apply (@zero_unique C H_Ini _ _ id[initial_obj]). }
  apply mor_as_cospan_id.
Defined.

(*
   * [scfa_delta (scfa I) ≈ from unit_left] : analogous to mu, but with
   backward cospans. 

   --------
   * [scfa_delta (scfa I) ≈ from unit_left]：类似于 mu，但使用反向余跨度。
*)
Lemma cospan_scfa_unit_delta :
  cospan_equiv
    (cospan_scfa_delta (@Cospan_unit_obj C H_Ini))
    (mor_as_cospan (from (@coprod_zero_l C H_Coc H_Ini
                            (@Cospan_unit_obj C H_Ini)))).
Proof.
  unfold cospan_scfa_delta, Cospan_unit_obj, mor_as_cospan; simpl.
  (*
 Build_CospanArrow 0 id (id▽id : 0+0 → 0)
 vs Build_CospanArrow (0+0) (from coprod_zero_l) id.
 Apex iso: phi = iso_sym coprod_zero_l : 0 ≅ 0+0.
 to phi = from coprod_zero_l ✓.
 to phi ∘ (id▽id) ≈ id[0+0] by initiality (0+0 → 0+0 from 0 source). 

 --------
 Build_CospanArrow 0 id (id▽id : 0+0 → 0)
 与 Build_CospanArrow (0+0) (from coprod_zero_l) id。
 顶点同构: phi = iso_sym coprod_zero_l : 0 ≅ 0+0。
 到 phi = from coprod_zero_l ✓。
 到 phi ∘ (id▽id) ≈ id [0+0] 通过初始性 (0+0 → 0+0 来自 0 源)。
*)
  exists (iso_sym (@coprod_zero_l C H_Coc H_Ini (@Cospan_unit_obj C H_Ini))).
  simpl; split.
  - apply id_right.
  - (* from coprod_zero_l ∘ (id ▽ id) ≈ id[0+0] By coprod_ext: ∘ inl gives inr ≈ inl in 0 → 0+0 (initiality); ∘ inr gives inr ≈ inr (reflexivity). / 从 coprod_zero_l ∘ (id ▽ id) ≈ id [0+0] 依据 coprod_ext：∘ inl 得 inr ≈ inl 在 0 → 0+0（初始性）； ∘ inr 得 inr ≈ inr（自反性）。 *)
    apply coprod_ext.
    + rewrite <- comp_assoc.
      rewrite inl_merge.
      rewrite id_right.
      rewrite id_left.
      apply (@zero_unique C H_Ini _ _ _).
    + rewrite <- comp_assoc.
      rewrite inr_merge.
      rewrite id_right.
      rewrite id_left.
      unfold from, coprod_zero_l; simpl.
      reflexivity.
Defined.

(** [scfa_epsilon (scfa I) ≈ id[I]]. / [scfa_epsilon (scfa I) ≈ id[I] ]. *)
Lemma cospan_scfa_unit_epsilon :
  cospan_equiv
    (cospan_scfa_epsilon (@Cospan_unit_obj C H_Ini))
    (cospan_id (@Cospan_unit_obj C H_Ini)).
Proof.
  unfold cospan_scfa_epsilon, Cospan_unit_obj, cospan_id; simpl.
  (*
 Build_CospanArrow 0 id zero vs Build_CospanArrow 0 id id.
 Use iso_id, but show zero ≈ id at 0 → 0 by initiality. 

 --------
 Build_CospanArrow 0 id zero 与 Build_CospanArrow 0 id id。
 使用 iso_id，但通过初始性展示 zero ≈ id 在 0 → 0 上。
*)
  exists iso_id; simpl; split.
  - cat.
  - rewrite id_left.
    apply (@zero_unique C H_Ini _ _ _).
Defined.

(*
   * ** Tensor coherence: [scfa_tensor_eta]

   Both [scfa_eta (X⨂Y)] and [canonical_tensor_eta (scfa X) (scfa Y)]
   reduce to [mor_as_cospan zero : 0 → X+Y] after lifting through
   [mor_as_cospan_compose] and [cospan_tensor_mor_as_cospan]. 

   --------
   * ** 张量相干性: [scfa_tensor_eta] 

   [scfa_eta (X⨂Y)] 和 [canonical_tensor_eta (scfa X) (scfa Y)] 
   在通过 [mor_as_cospan_compose] 和 [cospan_tensor_mor_as_cospan] 提升后
   都化简为 [mor_as_cospan zero : 0 → X+Y] 。
*)

Lemma cospan_scfa_tensor_eta (X Y : C) :
  cospan_equiv
    (cospan_scfa_eta (X + Y))
    (cospan_compose HP
       (cospan_tensor (cospan_scfa_eta X) (cospan_scfa_eta Y))
       (mor_as_cospan (from (@coprod_zero_l C H_Coc H_Ini
                               (@Cospan_unit_obj C H_Ini))))).
Proof.
  unfold cospan_scfa_eta, Cospan_tensor_obj.
  (*
 RHS: cospan_tensor (mor_as_cospan zero) (mor_as_cospan zero)
 ≈ mor_as_cospan (cover zero zero).
 Then compose with mor_as_cospan (from coprod_zero_l)
 ≈ mor_as_cospan ((cover zero zero) ∘ from coprod_zero_l). 

 --------
 右侧：cospan_tensor（mor_as_cospan zero）（mor_as_cospan zero）
 ≈ mor_as_cospan（cover zero zero）。
 然后与 mor_as_cospan（from coprod_zero_l）组合
 ≈ mor_as_cospan（（cover zero zero）∘ from coprod_zero_l）。
*)
  apply cospan_equiv_sym.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_tensor_mor_as_cospan. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  (*
 C-level: (cover zero zero : 0+0 → X+Y) ∘ (from coprod_zero_l : 0 → 0+0) ≈ zero 

 --------
 C级: (cover zero zero : 0+0 → X+Y) ∘ (from coprod_zero_l : 0 → 0+0) ≈ zero
*)
  (*
 from coprod_zero_l = inr : 0 → 0+0.  cover zero zero ∘ inr = inr ∘ zero = zero. 

 --------
 来自 coprod_zero_l = inr : 0 → 0+0。 cover zero zero ∘ inr = inr ∘ zero = zero。
*)
  unfold from, coprod_zero_l; simpl.
  rewrite cover_inr.
  apply (@zero_unique C H_Ini _ _ _).
Defined.

(*
   * ** Tensor coherence: [scfa_tensor_epsilon]

   [scfa_epsilon (X⨂Y) ≈ canonical_tensor_epsilon] :
   both reduce to [mor_as_cospan_back (zero : 0 → X+Y)]. 

   --------
   * ** 张量相干性：[scfa_tensor_epsilon] 

   [scfa_epsilon (X⨂Y) ≈ canonical_tensor_epsilon] ：
   都简化为 [mor_as_cospan_back (zero : 0 → X+Y)] 。
*)

Lemma cospan_scfa_tensor_epsilon (X Y : C) :
  cospan_equiv
    (cospan_scfa_epsilon (X + Y))
    (cospan_compose HP
       (mor_as_cospan (to (@coprod_zero_l C H_Coc H_Ini
                             (@Cospan_unit_obj C H_Ini))))
       (cospan_tensor (cospan_scfa_epsilon X) (cospan_scfa_epsilon Y))).
Proof.
  unfold cospan_scfa_epsilon, Cospan_tensor_obj.
  apply cospan_equiv_sym.
  (*
 Inner: cospan_tensor (back zero_X) (back zero_Y) ≈ back (cover zero_X zero_Y). 

 --------
 内部：cospan_tensor（back zero_X）（back zero_Y）≈ back（cover zero_X zero_Y）。
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_mor_as_cospan_back.
    - apply cospan_equiv_refl. }
  (*
 Now: compose (mor_as_cospan (to coprod_zero_l)) (back (cover zero zero)).
 Apply cospan_compose_forward_iso_back with g = cover zero zero, phi = coprod_zero_l. 

 --------
 现在：compose (mor_as_cospan (to coprod_zero_l)) (back (cover zero zero))。
 应用 cospan_compose_forward_iso_back，参数 g = cover zero zero，phi = coprod_zero_l。
*)
  eapply cospan_equiv_trans.
  { apply (cospan_compose_forward_iso_back HP
              (cover (zero : 0 ~{C}~> X) (zero : 0 ~{C}~> Y))
              (@coprod_zero_l C H_Coc H_Ini 0%object)). }
  (*
 Result: mor_as_cospan_back ((cover zero zero) ∘ from coprod_zero_l).
 LHS target: mor_as_cospan_back (zero : 0 → X+Y).
 Need: (cover zero zero) ∘ from coprod_zero_l ≈ zero in C. 

 --------
 结果：mor_as_cospan_back ((cover zero zero) ∘ from coprod_zero_l)。
 左边目标：mor_as_cospan_back (zero : 0 → X+Y)。
 需求：(cover zero zero) ∘ from coprod_zero_l ≈ 在 C 中的零。
*)
  apply mor_as_cospan_back_proper.
  unfold from, coprod_zero_l; simpl.
  rewrite cover_inr.
  symmetry.
  apply (@zero_unique C H_Ini _ _ _).
Defined.

(*
   * ** C-level identity for [scfa_tensor_mu]

   The codiagonal on [(X+Y) + (X+Y)] factors through the middle-swap
   composite and the per-component codiagonals. 

   --------
   * ** [scfa_tensor_mu] 的 C 级同一性

   [(X+Y) + (X+Y)] 上的余对角通过中间交换复合和每个分量的余对角进行分解。
*)

Lemma codiag_through_mid_swap (X Y : C) :
  ((id[X + Y] ▽ id[X + Y]) : ((X + Y) + (X + Y))%object ~> (X + Y))
  ≈ cover (id[X] ▽ id[X]) (id[Y] ▽ id[Y])
      ∘ from (@coprod_assoc C H_Coc X X (Y + Y))
      ∘ cover id[X] (to (@coprod_assoc C H_Coc X Y Y))
      ∘ cover id[X] (cover (paws : (Y + X)%object ~{C}~> (X + Y)%object) id[Y])
      ∘ cover id[X] (from (@coprod_assoc C H_Coc Y X Y))
      ∘ to (@coprod_assoc C H_Coc X Y (X + Y)).
Proof.
  apply coprod_ext.
  - apply coprod_ext.
    + (* X.first leg via (inl ∘ inl); both sides → inl / X.第一部分通过 (inl ∘ inl); 双方 → inl *)
      rewrite <- !comp_assoc.
      rewrite assoc_to_inl_inl.
      rewrite cover_inl, id_right.
      rewrite cover_inl, id_right.
      rewrite cover_inl, id_right.
      rewrite assoc_from_inl.
      rewrite (comp_assoc (cover (id[X] ▽ id[X]) (id[Y] ▽ id[Y])) inl inl).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl (id[X] ▽ id[X]) inl).
      rewrite inl_merge, id_right.
      rewrite (comp_assoc (id[X+Y] ▽ id[X+Y]) inl inl).
      rewrite inl_merge, id_left.
      reflexivity.
    + (* Y.first leg via (inl ∘ inr); both sides → inr / Y.第一条路径通过 (inl ∘ inr)；两边 → inr *)
      rewrite <- !comp_assoc.
      rewrite assoc_to_inl_inr.
      rewrite (comp_assoc (cover id[X] (from coprod_assoc)) inr inl).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (from coprod_assoc) inl).
      rewrite assoc_from_inl.
      rewrite (comp_assoc (cover id[X] (cover paws id[Y])) inr (inl ∘ inl)).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (cover paws id[Y]) (inl ∘ inl)).
      rewrite (comp_assoc (cover paws id[Y]) inl inl).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl paws inl).
      rewrite paws_inl.
      rewrite (comp_assoc (cover id[X] (to coprod_assoc)) inr (inl ∘ inr)).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (to coprod_assoc) (inl ∘ inr)).
      rewrite assoc_to_inl_inr.
      rewrite (comp_assoc (from coprod_assoc) inr (inr ∘ inl)).
      rewrite (comp_assoc (from coprod_assoc ∘ inr) inr inl).
      rewrite <- (comp_assoc (from coprod_assoc) inr inr).
      rewrite assoc_from_inr_inr.
      rewrite (comp_assoc (cover (id[X] ▽ id[X]) (id[Y] ▽ id[Y])) inr inl).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (id[Y] ▽ id[Y]) inl).
      rewrite inl_merge, id_right.
      rewrite (comp_assoc (id[X+Y] ▽ id[X+Y]) inl inr).
      rewrite inl_merge, id_left.
      reflexivity.
  - apply coprod_ext.
    + (* X.second leg via (inr ∘ inl); both sides → inl / X.second 通过 (inr ∘ inl) 实现; 两边 → inl *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (to coprod_assoc) inr inl).
      rewrite assoc_to_inr.
      rewrite <- (comp_assoc inr inr inl).
      rewrite (comp_assoc (cover id[X] (from coprod_assoc)) inr (inr ∘ inl)).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (from coprod_assoc) (inr ∘ inl)).
      rewrite assoc_from_inr_inl.
      rewrite (comp_assoc (cover id[X] (cover paws id[Y])) inr (inl ∘ inr)).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (cover paws id[Y]) (inl ∘ inr)).
      rewrite (comp_assoc (cover paws id[Y]) inl inr).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl paws inr).
      rewrite paws_inr.
      rewrite (comp_assoc (cover id[X] (to coprod_assoc)) inr (inl ∘ inl)).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (to coprod_assoc) (inl ∘ inl)).
      rewrite assoc_to_inl_inl.
      rewrite assoc_from_inr_inl.
      rewrite (comp_assoc (cover (id[X] ▽ id[X]) (id[Y] ▽ id[Y])) inl inr).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl (id[X] ▽ id[X]) inr).
      rewrite inr_merge, id_right.
      rewrite (comp_assoc (id[X+Y] ▽ id[X+Y]) inr inl).
      rewrite inr_merge, id_left.
      reflexivity.
    + (* Y.second leg via (inr ∘ inr); both sides → inr / Y.second 通过 (inr ∘ inr); 双方 → inr *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (to coprod_assoc) inr inr).
      rewrite assoc_to_inr.
      rewrite <- (comp_assoc inr inr inr).
      rewrite (comp_assoc (cover id[X] (from coprod_assoc)) inr (inr ∘ inr)).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (from coprod_assoc) (inr ∘ inr)).
      rewrite assoc_from_inr_inr.
      rewrite (comp_assoc (cover id[X] (cover paws id[Y])) inr inr).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (cover paws id[Y]) inr).
      rewrite cover_inr.
      rewrite id_right.
      rewrite (comp_assoc (cover id[X] (to coprod_assoc)) inr inr).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (to coprod_assoc) inr).
      rewrite assoc_to_inr.
      rewrite (comp_assoc (from coprod_assoc) inr (inr ∘ inr)).
      rewrite (comp_assoc (from coprod_assoc ∘ inr) inr inr).
      rewrite <- (comp_assoc (from coprod_assoc) inr inr).
      rewrite assoc_from_inr_inr.
      rewrite (comp_assoc (cover (id[X] ▽ id[X]) (id[Y] ▽ id[Y])) inr inr).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (id[Y] ▽ id[Y]) inr).
      rewrite inr_merge, id_right.
      rewrite (comp_assoc (id[X+Y] ▽ id[X+Y]) inr inr).
      rewrite inr_merge, id_left.
      reflexivity.
Qed.

(*
   * ** Cospan-level [scfa_tensor_mu]

   Reduces [bimap mu_X mu_Y ∘ mid_swap X Y] (at the cospan level) to
   [mor_as_cospan ((cover (id▽id_X) (id▽id_Y)) ∘ mid_swap_C)], which by
   [codiag_through_mid_swap] equals [mor_as_cospan (id▽id_{X+Y})] =
   [scfa_mu (X+Y)]. 

   --------
   * ** Cospan级别 [scfa_tensor_mu] 

   将 Cospan级别的 [bimap mu_X mu_Y ∘ mid_swap X Y] 降低到
   [mor_as_cospan ((cover (id▽id_X) (id▽id_Y)) ∘ mid_swap_C)] ，根据
   [codiag_through_mid_swap] 等于 [mor_as_cospan (id▽id_{X+Y})] =
   [scfa_mu (X+Y)] 。
*)

(*
   * Tactical hint: any [cospan_tensor (cospan_id _) (mor_as_cospan g)]
   reduces to [mor_as_cospan (cover id g)] via id_as_back + tensor compatibility.
   This bundles two steps. 

   --------
   * 战术提示：任何 [cospan_tensor (cospan_id _) (mor_as_cospan g)]  
   都可以通过 id_as_back + 张量兼容性 简化为 [mor_as_cospan (cover id g)]。  
   这捆绑了两个步骤。
*)

Lemma cospan_tensor_id_left_as_cospan {A B X : C}
  (g : A ~> B) :
  cospan_equiv
    (cospan_tensor (cospan_id X) (mor_as_cospan g))
    (mor_as_cospan (cover id[X] g)).
Proof.
  eapply cospan_equiv_trans.
  { apply cospan_tensor_respects.
    - apply cospan_equiv_sym, mor_as_cospan_id.
    - apply cospan_equiv_refl. }
  apply cospan_tensor_mor_as_cospan.
Defined.

(*
   * ** C-level mid-swap composite

   The C-morphism [(X+Y)+(X+Y) → (X+X)+(Y+Y)] that the Hypergraph
   [mid_swap] reduces to when [tensor = coproduct], expressed without
   [bimap]/[cover] sugar (i.e., directly as a [cover]-of-isos chain). 

   --------
   * ** C 级中间交换复合

   当  [tensor = coproduct] 时，超图 [mid_swap] 简化为的 C-态射 [(X+Y)+(X+Y) → (X+X)+(Y+Y)] ，以不含 [bimap] / [cover] 的方式表示（即直接作为 [cover]-of-isos 链）。
*)

Definition mid_swap_C (X Y : C) :
  ((X + Y) + (X + Y))%object ~> ((X + X) + (Y + Y))%object :=
  from (@coprod_assoc C H_Coc X X (Y + Y))
    ∘ cover id[X] (to (@coprod_assoc C H_Coc X Y Y))
    ∘ cover id[X] (cover (paws : (Y + X)%object ~{C}~> (X + Y)%object) id[Y])
    ∘ cover id[X] (from (@coprod_assoc C H_Coc Y X Y))
    ∘ to (@coprod_assoc C H_Coc X Y (X + Y)).

(*
   * Restate [codiag_through_mid_swap] in terms of [mid_swap_C]. 

   --------
   * 用 [mid_swap_C] 的形式重述 [codiag_through_mid_swap] 。
*)
Lemma codiag_via_mid_swap_C (X Y : C) :
  ((id[X + Y] ▽ id[X + Y]) : ((X + Y) + (X + Y))%object ~> (X + Y))
  ≈ cover (id[X] ▽ id[X]) (id[Y] ▽ id[Y]) ∘ mid_swap_C X Y.
Proof.
  unfold mid_swap_C.
  rewrite !comp_assoc.
  apply codiag_through_mid_swap.
Qed.

(*
   * ** Cospan-level mid_swap reduces to [mor_as_cospan mid_swap_C]

   The [Hypergraph] class's [mid_swap X Y] is built from cospan
   [tensor_assoc], [bimap], and [braid].  In [CospanCat C HP],
   [tensor_assoc] is [mor_iso_lift] of [coprod_assoc] (so [to] is
   [mor_as_cospan (to coprod_assoc)] and [from] is [mor_as_cospan
   (from coprod_assoc)]), [bimap] is [cospan_tensor], and [braid] is
   [mor_as_cospan paws].  The whole expression therefore reduces, by
   iterated [cospan_tensor_id_left_as_cospan] /
   [cospan_tensor_mor_as_cospan] / [mor_as_cospan_compose], to
   [mor_as_cospan (mid_swap_C X Y)]. 

   --------
   * ** Cospan级别的 mid_swap 简化为 [mor_as_cospan mid_swap_C] 

   [Hypergraph] 类的 [mid_swap X Y] 是由 cospan [tensor_assoc]、[bimap] 和 [braid] 构建的。在 [CospanCat C HP] 中，[tensor_assoc] 是 [coprod_assoc] 的 [mor_iso_lift]（所以 [to] 是 [mor_as_cospan (to coprod_assoc)] 且 [from] 是 [mor_as_cospan (来自 coprod_assoc)]），[bimap] 是 [cospan_tensor]，[braid] 是 [mor_as_cospan paws]。因此整个表达式经由反复的 [cospan_tensor_id_left_as_cospan] / [cospan_tensor_mor_as_cospan] / [mor_as_cospan_compose] 简化为 [mor_as_cospan (mid_swap_C X Y)]。
*)

Lemma cospan_mid_swap_as_mor (X Y : C) :
  cospan_equiv
    (@mid_swap (CospanCat C HP) (Cospan_SymmetricMonoidal HP) X Y)
    (mor_as_cospan (mid_swap_C X Y)).
Proof.
  unfold mid_swap, mid_swap_C; simpl.
  (*
 The expression is left-associated: ((((e1 ∘ e2) ∘ e3) ∘ e4) ∘ e5)
 where, with cospan_compose g f convention,
 e1 = α⁻¹              (mor_as_cospan)
 e2 = bimap id (to α)  → rewrite to mor_as_cospan via tensor_id_left
 e3 = bimap id (bimap paws id)  → 2-stage reduction
 e4 = bimap id (α⁻¹)   → rewrite via tensor_id_left
 e5 = to α             (mor_as_cospan)
 At depth k from outer, [f] is e_{5-k} and [g] is the prefix. 

 --------
 这个表达式是左关联的：((((e1 ∘ e2) ∘ e3) ∘ e4) ∘ e5)
 其中，根据 cospan_compose g f 的约定，
 e1 = α⁻¹              （mor_as_cospan）
 e2 = bimap id (to α)  → 通过 tensor_id_left 重写为 mor_as_cospan
 e3 = bimap id (bimap paws id)  → 两阶段归约
 e4 = bimap id (α⁻¹)   → 通过 tensor_id_left 重写
 e5 = to α             （mor_as_cospan）
 从外层深度 k 处，[f] 是 e_{5-k}，[g] 是前缀。
*)
  (*
 Stage A: reduce e2, e3, e4 each to mor_as_cospan. 

 --------
 阶段A：将 e2、e3、e4 每个都减少到 mor_as_cospan。
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.                          (* e5 unchanged / e5 不变 *)
    - apply cospan_compose_respects_aux.
      + apply cospan_tensor_id_left_as_cospan.          (* e4 *)
      + apply cospan_compose_respects_aux.
        * apply cospan_tensor_respects.
          { apply cospan_equiv_refl. }
          { apply cospan_tensor_mor_as_cospan. }        (* e3 inner *)
        * apply cospan_compose_respects_aux.
          { apply cospan_tensor_id_left_as_cospan. }    (* e2 *)
          { apply cospan_equiv_refl. } }                (* e1 unchanged / e1 未改变 *)
  (*
 After Stage A, e3 has shape  cospan_tensor (cospan_id X) (mor_as_cospan (cover paws id))
 which is still a tensor; apply tensor_id_left to fully reduce it. 

 --------
 在阶段 A 之后，e3 的形状为 cospan_tensor (cospan_id X) (mor_as_cospan (cover paws id))，它仍然是一个张量；应用 tensor_id_left 来完全化简它。
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_refl.
      + apply cospan_compose_respects_aux.
        * apply cospan_tensor_id_left_as_cospan.        (* e3 final *)
        * apply cospan_equiv_refl. }
  (*
 Now all 5 pieces are mor_as_cospan; fuse left-to-right.
 Composite shape:  (((e1' ∘ e2') ∘ e3') ∘ e4') ∘ e5'  (all mor_as_cospan).
 Fuse outermost first (peel f off and into the prefix). 

 --------
 现在所有5个部分都是 mor_as_cospan；从左到右融合。
 复合形状：(((e1' ∘ e2') ∘ e3') ∘ e4') ∘ e5'（全部为 mor_as_cospan）。
 先融合最外层（将 f 剥离并放入前缀）。
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_refl.
      + apply cospan_compose_respects_aux.
        * apply cospan_equiv_refl.
        * apply mor_as_cospan_compose. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_refl.
      + apply mor_as_cospan_compose. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply mor_as_cospan_compose. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  reflexivity.
Defined.

(*
   * ** Cospan-level [scfa_tensor_mu]

   Both sides reduce to [mor_as_cospan (id▽id : (X+Y)+(X+Y) → X+Y)]
   via [codiag_through_mid_swap]: the RHS fuses to [mor_as_cospan
   (cover (id▽id_X) (id▽id_Y) ∘ mid_swap_C X Y)], which by the
   C-identity equals [mor_as_cospan (id▽id)]. 

   --------
   * ** Cospan 级别  [scfa_tensor_mu] 

   双方通过  [codiag_through_mid_swap] 简化为  [mor_as_cospan (id▽id : (X+Y)+(X+Y) → X+Y)] ：右边融合为 [mor_as_cospan
   (cover (id▽id_X) (id▽id_Y) ∘ mid_swap_C X Y)]，根据 C-恒等式等于  [mor_as_cospan (id▽id)] 。
*)

Lemma cospan_scfa_tensor_mu (X Y : C) :
  cospan_equiv
    (cospan_scfa_mu (X + Y))
    (cospan_compose HP
       (cospan_tensor (cospan_scfa_mu X) (cospan_scfa_mu Y))
       (@mid_swap (CospanCat C HP) (Cospan_SymmetricMonoidal HP) X Y)).
Proof.
  (*
 RHS: cospan_tensor (mor_as_cospan (id▽id_X)) (mor_as_cospan (id▽id_Y))
 ≈ mor_as_cospan (cover (id▽id_X) (id▽id_Y))                       

 --------
 右侧: cospan_tensor (mor_as_cospan (id▽id_X)) (mor_as_cospan (id▽id_Y))
 ≈ mor_as_cospan (cover (id▽id_X) (id▽id_Y))
*)
  apply cospan_equiv_sym.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_mid_swap_as_mor.
    - apply cospan_tensor_mor_as_cospan. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  (*
 C-level: (cover (id▽id_X) (id▽id_Y)) ∘ mid_swap_C X Y ≈ id▽id_{X+Y} 

 --------
 C级别: (cover (id▽id_X) (id▽id_Y)) ∘ mid_swap_C X Y ≈ id▽id_{X+Y}
*)
  symmetry.
  apply codiag_via_mid_swap_C.
Defined.

(*
   * ** Cospan-level [scfa_tensor_delta]

   Dual to [tensor_mu]: both sides reduce to [mor_as_cospan_back
   (id▽id : (X+Y)+(X+Y) → X+Y)] (backward cospans).  The bridge uses
   [cospan_tensor_mor_as_cospan_back] for the inner tensor, then
   [mid_swap_inv] is bridged as [mor_as_cospan_back] of an inverse-iso
   composite, after which [mor_as_cospan_back_compose] fuses. 

   --------
   * ** Cospan级别 [scfa_tensor_delta]

   与 [tensor_mu] 对偶：两边都约化为 [mor_as_cospan_back
   (id▽id : (X+Y)+(X+Y) → X+Y)]（反向Cospan）。桥使用
   [cospan_tensor_mor_as_cospan_back] 作为内部张量，然后
   [mid_swap_inv] 通过一个逆同构复合桥接为 [mor_as_cospan_back]，之后 [mor_as_cospan_back_compose] 融合。
*)

(*
   * A [mor_as_cospan] of [to phi] for an iso [phi] is cospan-equivalent
   to a [mor_as_cospan_back] of [from phi].  Both express the same
   span shape via the iso [phi]. 

   --------
   * 对于一个同构 [phi]，[mor_as_cospan] 的 [to phi] 与 [from phi] 的 [mor_as_cospan_back] 是余跨等价的。两者通过同构 [phi] 表达相同的跨形状。
*)
Lemma mor_as_cospan_to_iso_as_back {X Y : C} (phi : X ≅ Y) :
  cospan_equiv
    (mor_as_cospan (to phi))
    (mor_as_cospan_back (from phi : Y ~> X)).
Proof.
  unfold mor_as_cospan, mor_as_cospan_back; simpl.
  exists (iso_sym phi); simpl; split.
  - apply iso_from_to.
  - rewrite id_right. reflexivity.
Defined.

(*
   * [mid_swap_C] is an iso in [C] (built as a composite of coproduct
   isos and [paws]).  Its inverse is the analogous backwards composite. 

   --------
   *  [mid_swap_C] 是 [C] 中的一个同构（构建为余积同构和 [paws] 的复合体）。它的逆是类似的反向复合。
*)
Definition mid_swap_C_inv (X Y : C) :
  ((X + X) + (Y + Y))%object ~> ((X + Y) + (X + Y))%object :=
  from (@coprod_assoc C H_Coc X Y (X + Y))
    ∘ cover id[X] (to (@coprod_assoc C H_Coc Y X Y))
    ∘ cover id[X] (cover (paws : (X + Y)%object ~{C}~> (Y + X)%object) id[Y])
    ∘ cover id[X] (from (@coprod_assoc C H_Coc X Y Y))
    ∘ to (@coprod_assoc C H_Coc X X (Y + Y)).

(*
   * [mid_swap_inv] in [CospanCat C HP] reduces to [mor_as_cospan
   (mid_swap_C_inv X Y)]: same chain of bridging steps as for
   [mid_swap]. 

   --------
   *  [mid_swap_inv] 在 [CospanCat C HP] 中化简为 [mor_as_cospan (mid_swap_C_inv X Y)]：与 [mid_swap] 相同的桥接步骤链。
*)
Lemma cospan_mid_swap_inv_as_mor (X Y : C) :
  cospan_equiv
    (@mid_swap_inv (CospanCat C HP) (Cospan_SymmetricMonoidal HP) X Y)
    (mor_as_cospan (mid_swap_C_inv X Y)).
Proof.
  unfold mid_swap_inv, mid_swap_C_inv; simpl.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_compose_respects_aux.
      + apply cospan_tensor_id_left_as_cospan.
      + apply cospan_compose_respects_aux.
        * apply cospan_tensor_respects.
          { apply cospan_equiv_refl. }
          { apply cospan_tensor_mor_as_cospan. }
        * apply cospan_compose_respects_aux.
          { apply cospan_tensor_id_left_as_cospan. }
          { apply cospan_equiv_refl. } }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_refl.
      + apply cospan_compose_respects_aux.
        * apply cospan_tensor_id_left_as_cospan.
        * apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_refl.
      + apply cospan_compose_respects_aux.
        * apply cospan_equiv_refl.
        * apply mor_as_cospan_compose. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_compose_respects_aux.
      + apply cospan_equiv_refl.
      + apply mor_as_cospan_compose. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply mor_as_cospan_compose. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  reflexivity.
Defined.

(*
   * Composing [mid_swap_C_inv] before [mid_swap_C] cancels (in C).

   The five-stage cancellation chain (after full right-associativity):
   [to α₄ ∘ from α₅], then [cover id (from α₃) ∘ cover id (to α₆)],
   [cover id (cover paws id) ∘ cover id (cover paws id)],
   [cover id (to α₂) ∘ cover id (from α₇)], and finally
   [from α₁ ∘ to α₈]. 

   --------
   * 在  [mid_swap_C]  之前组合  [mid_swap_C_inv]  会被取消（在 C 中）。

   五阶段取消链（完全右结合之后）：
   [to α₄ ∘ from α₅] ，然后  [cover id (from α₃) ∘ cover id (to α₆)] ，
   [cover id (cover paws id) ∘ cover id (cover paws id)] ，
   [cover id (to α₂) ∘ cover id (from α₇)] ，最后
   [from α₁ ∘ to α₈] 。
*)
Lemma mid_swap_C_inv_left (X Y : C) :
  mid_swap_C X Y ∘ mid_swap_C_inv X Y ≈ id.
Proof.
  unfold mid_swap_C, mid_swap_C_inv.
  rewrite <- !comp_assoc.
  (*
 Stage 1: to α(X,Y,X+Y) ∘ from α(X,Y,X+Y) = id 

 --------
 阶段 1：到 α(X,Y,X+Y) ∘ 从 α(X,Y,X+Y) = 恒等
*)
  rewrite (comp_assoc (to coprod_assoc) (from coprod_assoc)).
  rewrite iso_to_from, id_left.
  (*
 Stage 2: cover id (from α(Y,X,Y)) ∘ cover id (to α(Y,X,Y)) = id 

 --------
 阶段 2：cover id（从 α(Y,X,Y)）∘ cover id（到 α(Y,X,Y)）= id
*)
  rewrite (comp_assoc (cover id[X] (from coprod_assoc))
                      (cover id[X] (to coprod_assoc))).
  rewrite cover_comp, id_left, iso_from_to, cover_id, id_left.
  (*
 Stage 3: cover id (cover paws id) ∘ cover id (cover paws id) = id 

 --------
 阶段 3：遮盖 id（遮盖爪子 id）∘ 遮盖 id（遮盖爪子 id）= id
*)
  rewrite (comp_assoc (cover id[X] (cover paws id[Y]))
                      (cover id[X] (cover paws id[Y]))).
  rewrite cover_comp, id_left.
  rewrite cover_comp, paws_invol, id_left.
  rewrite cover_id, cover_id, id_left.
  (*
 Stage 4: cover id (to α(X,Y,Y)) ∘ cover id (from α(X,Y,Y)) = id 

 --------
 阶段 4：cover id（到 α(X,Y,Y)）∘ cover id（从 α(X,Y,Y)）= id
*)
  rewrite (comp_assoc (cover id[X] (to coprod_assoc))
                      (cover id[X] (from coprod_assoc))).
  rewrite cover_comp, id_left, iso_to_from, cover_id, id_left.
  (*
 Stage 5: from α(X,X,Y+Y) ∘ to α(X,X,Y+Y) = id 

 --------
 阶段 5：从 α(X,X,Y+Y) ∘ 到 α(X,X,Y+Y) = id
*)
  apply iso_from_to.
Qed.

(*
   * Reverse cancellation: [mid_swap_C_inv ∘ mid_swap_C ≈ id].

   Five stages of cancellation, dual to [mid_swap_C_inv_left]:
   (1) to α(X,X,Y+Y) ∘ from α(X,X,Y+Y) = id
   (2) cover id (from α(X,Y,Y)) ∘ cover id (to α(X,Y,Y)) = id
   (3) cover id (cover paws id) ∘ cover id (cover paws id) = id
   (4) cover id (to α(Y,X,Y)) ∘ cover id (from α(Y,X,Y)) = id
   (5) from α(X,Y,X+Y) ∘ to α(X,Y,X+Y) = id 

   --------
   * 反向消去：[mid_swap_C_inv ∘ mid_swap_C ≈ id]。

   五个消去阶段，对应 [mid_swap_C_inv_left]：
   (1) 至 α(X,X,Y+Y) ∘ 从 α(X,X,Y+Y) = id
   (2) 覆盖 id（从 α(X,Y,Y)）∘ 覆盖 id（至 α(X,Y,Y)）= id
   (3) 覆盖 id（覆盖爪 id）∘ 覆盖 id（覆盖爪 id）= id
   (4) 覆盖 id（至 α(Y,X,Y)）∘ 覆盖 id（从 α(Y,X,Y)）= id
   (5) 从 α(X,Y,X+Y) ∘ 至 α(X,Y,X+Y) = id
*)
Lemma mid_swap_C_inv_right (X Y : C) :
  mid_swap_C_inv X Y ∘ mid_swap_C X Y ≈ id.
Proof.
  unfold mid_swap_C, mid_swap_C_inv.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to coprod_assoc) (from coprod_assoc)).
  rewrite iso_to_from, id_left.
  rewrite (comp_assoc (cover id[X] (from coprod_assoc))
                      (cover id[X] (to coprod_assoc))).
  rewrite cover_comp, id_left, iso_from_to, cover_id, id_left.
  rewrite (comp_assoc (cover id[X] (cover paws id[Y]))
                      (cover id[X] (cover paws id[Y]))).
  rewrite cover_comp, id_left.
  rewrite cover_comp, paws_invol, id_left.
  rewrite cover_id, cover_id, id_left.
  rewrite (comp_assoc (cover id[X] (to coprod_assoc))
                      (cover id[X] (from coprod_assoc))).
  rewrite cover_comp, id_left, iso_to_from, cover_id, id_left.
  apply iso_from_to.
Qed.

Lemma cospan_scfa_tensor_delta (X Y : C) :
  cospan_equiv
    (cospan_scfa_delta (X + Y))
    (cospan_compose HP
       (@mid_swap_inv (CospanCat C HP) (Cospan_SymmetricMonoidal HP) X Y)
       (cospan_tensor (cospan_scfa_delta X) (cospan_scfa_delta Y))).
Proof.
  (*
 Build the iso phi : (X+X)+(Y+Y) ≅ (X+Y)+(X+Y) with
 to phi   := mid_swap_C_inv X Y
 from phi := mid_swap_C X Y.
 Then [mor_as_cospan mid_swap_C_inv ≈ mor_as_cospan_to phi].
 [cospan_compose_forward_iso_back] collapses the composite to a
 single [mor_as_cospan_back] whose underlying C-morphism is
 [(cover (id▽id_X)(id▽id_Y)) ∘ from phi = m1 ∘ mid_swap_C],
 which by [codiag_via_mid_swap_C] equals [id▽id_{X+Y}].         

 --------
 构建同构 phi : (X+X)+(Y+Y) ≅ (X+Y)+(X+Y)，其中
 to phi   := mid_swap_C_inv X Y
 from phi := mid_swap_C X Y。
 然后 [mor_as_cospan mid_swap_C_inv ≈ mor_as_cospan_to phi] 。
 [cospan_compose_forward_iso_back] 将复合缩减为一个单一的 [mor_as_cospan_back]，其底层 C-态射为 [(cover (id▽id_X)(id▽id_Y)) ∘ from phi = m1 ∘ mid_swap_C] ，
 根据 [codiag_via_mid_swap_C] 等于 [id▽id_{X+Y}] 。
*)
  apply cospan_equiv_sym.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_tensor_mor_as_cospan_back.
    - apply cospan_mid_swap_inv_as_mor. }
  (*
 Goal:
 cospan_compose (mor_as_cospan (mid_swap_C_inv X Y))
 (mor_as_cospan_back (cover (id▽id_X)(id▽id_Y)))
 ≈ cospan_scfa_delta (X+Y).                                   

 --------
 目标：
 cospan_compose (mor_as_cospan (mid_swap_C_inv X Y))
 (mor_as_cospan_back (cover (id▽id_X)(id▽id_Y)))
 ≈ cospan_scfa_delta (X+Y).
*)
  (* Build the iso. / 构建 ISO 文件。 *)
  unshelve epose (phi :=
    @Build_Isomorphism C _ _
      (mid_swap_C_inv X Y) (mid_swap_C X Y) _ _).
  2: { apply mid_swap_C_inv_left. }
  { apply mid_swap_C_inv_right. }
  (*
 Rewrite (mor_as_cospan (mid_swap_C_inv X Y)) = (mor_as_cospan (to phi)). 

 --------
 重写 (mor_as_cospan (mid_swap_C_inv X Y)) = (mor_as_cospan (to phi)).
*)
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply (mor_as_cospan_proper (mid_swap_C_inv X Y) (to phi)).
      reflexivity. }
  eapply cospan_equiv_trans.
  { apply (cospan_compose_forward_iso_back HP
              (cover (id[X] ▽ id[X] : (X + X)%object ~> X)
                     (id[Y] ▽ id[Y] : (Y + Y)%object ~> Y))
              phi). }
  (*
 Now: mor_as_cospan_back (cover (id▽id_X)(id▽id_Y) ∘ from phi)
 = mor_as_cospan_back (cover ... ∘ mid_swap_C X Y).
 Apply codiag_via_mid_swap_C symmetrically. 

 --------
 现在：mor_as_cospan_back (cover (id▽id_X)(id▽id_Y) ∘ from phi) = mor_as_cospan_back (cover ... ∘ mid_swap_C X Y)。对称地应用 codiag_via_mid_swap_C。
*)
  apply mor_as_cospan_back_proper.
  symmetry.
  apply codiag_via_mid_swap_C.
Defined.

End CospanHypergraphInstance.

(*
   * * The [Hypergraph (CospanCat C HP)] instance

   Assembling the eight axioms ([4 unit] + [4 tensor]) into the full
   [Hypergraph] class.  The SCFA on every object is [cospan_scfa]; the
   tensor coherence is [cospan_scfa_tensor_{mu,eta,delta,epsilon}]; the
   unit coherence is [cospan_scfa_unit_{mu,eta,delta,epsilon}]. 

   --------
   * * [Hypergraph (CospanCat C HP)] 实例

   将八条公理 ([4 unit] + [4 tensor]) 组装成完整的
   [Hypergraph] 类。每个对象上的 SCFA 是 [cospan_scfa]；
   张量相干性是 [cospan_scfa_tensor_{mu,eta,delta,epsilon}]；
   单位相干性是 [cospan_scfa_unit_{mu,eta,delta,epsilon}]。
*)

Section CospanHypergraph.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context (HP : HasPushouts C).

#[export] Program Instance Cospan_Hypergraph
  : @Hypergraph (CospanCat C HP) (Cospan_SymmetricMonoidal HP) := {|
  scfa                := cospan_scfa HP ;
  scfa_tensor_mu      := cospan_scfa_tensor_mu HP ;
  scfa_tensor_eta     := cospan_scfa_tensor_eta HP ;
  scfa_tensor_delta   := cospan_scfa_tensor_delta HP ;
  scfa_tensor_epsilon := cospan_scfa_tensor_epsilon HP ;
  scfa_unit_mu        := cospan_scfa_unit_mu ;
  scfa_unit_eta       := cospan_scfa_unit_eta ;
  scfa_unit_delta     := cospan_scfa_unit_delta ;
  scfa_unit_epsilon   := cospan_scfa_unit_epsilon
|}.

End CospanHypergraph.
