Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.Symmetric.

Generalizable All Variables.

Section RelevanceMonoidal.

Context {C : Category}.

(*
 nLab: https://ncatlab.org/nlab/show/relevance+monoidal+category
 Wikipedia: (no dedicated article; see Symmetric monoidal category and
 Relevance logic / structural rule of contraction)

 A relevance (relevant) monoidal category is a symmetric monoidal category
 equipped with a natural diagonal (copying/contraction) map

 ∆x : x ~> x ⨂ x

 satisfying coherence laws that make every object a cocommutative
 cosemigroup — coassociative and cocommutative comultiplication, but with
 no counit x ~> I. Modelling-wise this is the categorical counterpart of
 relevance logic: a substructural logic with the contraction rule (copying,
 the diagonal) but without weakening (projection/deletion, which would be a
 counit). Adding both diagonals and projections would make the category
 cartesian; adding projections alone would make it semicartesian.

 The axioms below follow Kosta Došen and Zoran Petrić, "Relevant Categories
 and Partial Functions" (2007), arXiv:math/0504133, in this library's
 notation:

 naturality:    (f ⨂ f) ∘ ∆x ≈ ∆y ∘ f             (f : x ~> y)
 unit:          ∆I ≈ unit_left⁻¹                   (I ≅ I ⨂ I)
 coassoc:       id ⨂ ∆ ∘ ∆ ≈ α ∘ ∆ ⨂ id ∘ ∆
 cocomm:        braid ∘ ∆ ≈ ∆                       (σ_{x,x} ∘ ∆ = ∆)
 tensor-compat: ∆(x ⨂ y) ≈ braid2 ∘ (∆ ⨂ ∆)

 where braid2 is the middle-four interchange iso permuting the inner two
 factors of (x ⨂ y) ⨂ (z ⨂ w) to (x ⨂ z) ⨂ (y ⨂ w). 

 --------
 nLab：https://ncatlab.org/nlab/show/relevance+monoidal+category
 Wikipedia：（没有专门的条目；请参见对称幺半群范畴和相关逻辑/收缩的结构规则）

 相关（relevant）幺半群范畴是一个对称幺半群范畴，配备了一个自然的对角线（复制/收缩）映射

 ∆x : x ~> x ⨂ x

 满足使每个对象成为余交换余半群的相干律——余结合且余交换的余乘法，但没有余单位 x ~> I。在建模方面，这是相关逻辑的范畴对应物：一种带有收缩规则（复制，即对角线）但没有削弱规则（投影/删除，即余单位）的子结构逻辑。添加对角线和投影将使范畴成为笛卡尔范畴；仅添加投影将使其成为半笛卡尔范畴。以下公理遵循 Kosta Došen 和 Zoran Petrić 的《Relevant Categories and Partial Functions》(2007)，arXiv:math/0504133，在本库的符号表示如下：

 自然性:    (f ⨂ f) ∘ ∆x ≈ ∆y ∘ f             (f : x ~> y)
 单位:      ∆I ≈ unit_left⁻¹                   (I ≅ I ⨂ I)
 余结合性:  id ⨂ ∆ ∘ ∆ ≈ α ∘ ∆ ⨂ id ∘ ∆
 余交换性:  braid ∘ ∆ ≈ ∆                       (σ_{x,x} ∘ ∆ = ∆)
 张量兼容性: ∆(x ⨂ y) ≈ braid2 ∘ (∆ ⨂ ∆)

 其中 braid2 是中间四元素交换同构，将 (x ⨂ y) ⨂ (z ⨂ w) 的内部两个因子置换为 (x ⨂ z) ⨂ (y ⨂ w)。
*)

Class RelevanceMonoidal := {
  (* The underlying symmetric monoidal structure (braiding + symmetry). / 基础的对称单体范畴结构（编织 + 对称）。 *)
  relevance_is_symmetric : @SymmetricMonoidal C;

  (* The diagonal / copying map ∆x : x ~> x ⨂ x (the contraction rule). / 对角线 / 复制映射 ∆x : x ~> x ⨂ x（收缩规则）。 *)
  diagonal {x} : x ~> x ⨂ x;
  (*
 Naturality: (f ⨂ f) ∘ ∆x ≈ ∆y ∘ f, so ∆ is a natural transformation
 from the identity functor to the squaring functor x ↦ x ⨂ x. 

 --------
 自然性: (f ⨂ f) ∘ ∆x ≈ ∆y ∘ f，因此 ∆ 是从恒等函子到平方函子 x ↦ x ⨂ x 的自然变换。
*)
  diagonal_natural : natural (@diagonal);

  (* Unit: the diagonal at the monoidal unit is the canonical iso I ≅ I ⨂ I, here unit_left⁻¹ : I ~> I ⨂ I. / 单元：单元的对角线是规范同构 I ≅ I ⨂ I，这里 unit_left⁻¹ : I ~> I ⨂ I。 *)
  diagonal_unit : @diagonal I ≈ unit_left⁻¹;

  (* Coassociativity: copying-then-copying-the-left equals copying-then-copying-the-right, modulo the associator. / 共结合性：先复制再复制左边等于先复制再复制右边，模结合子。 *)
  diagonal_tensor_assoc {x} :
   id ⨂ diagonal ∘ diagonal ≈ tensor_assoc ∘ diagonal ⨂ id ∘ @diagonal x;

  (* Cocommutativity / symmetry compatibility: swapping the two copies leaves the diagonal unchanged, σ_{x,x} ∘ ∆x ≈ ∆x. / 余交换性 / 对称性兼容性：交换两个副本不会改变对角线，σ_{x,x} ∘ ∆x ≈ ∆x。 *)
  braid_diagonal {x} :
    braid ∘ diagonal ≈ @diagonal x;

  (*
 The middle-four interchange iso (a definitional abbreviation, not an
 axiom): permutes the inner factors of (x ⨂ y) ⨂ (z ⨂ w) into
 (x ⨂ z) ⨂ (y ⨂ w), built from the associator and braiding. 

 --------
 中间四交换 iso（一个定义性的缩写，而不是公理）：将 (x ⨂ y) ⨂ (z ⨂ w) 的内部因子置换为 (x ⨂ z) ⨂ (y ⨂ w)，由结合子和编织构成。
*)
  braid2 {x y z w} : (x ⨂ y) ⨂ (z ⨂ w) ~> (x ⨂ z) ⨂ (y ⨂ w) :=
    tensor_assoc⁻¹
      ∘ id ⨂ (tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc⁻¹)
      ∘ tensor_assoc;

  (*
 Tensor compatibility: copying a tensor is copying each factor then
 regrouping via braid2, ∆(x ⨂ y) ≈ braid2 ∘ (∆x ⨂ ∆y). 

 --------
 张量兼容性：复制一个张量就是复制每个因子，然后通过 braid2 重新组合，∆(x ⨂ y) ≈ braid2 ∘ (∆x ⨂ ∆y)。
*)
  diagonal_braid2 {x y} :
    @diagonal (x ⨂ y) ≈ braid2 ∘ diagonal ⨂ diagonal
}.
#[export] Existing Instance relevance_is_symmetric.

Coercion relevance_is_symmetric : RelevanceMonoidal >-> SymmetricMonoidal.

Context `{RelevanceMonoidal}.

(* The middle-four interchange braid2 is natural in all four arguments; this is what makes the tensor-compatibility axiom diagonal_braid2 coherent. / 中间四元交换braid2在四个参数中都是自然的；这正是使张量兼容公理diagonal_braid2一致的原因。 *)
Lemma braid2_natural : natural (@braid2 _).
Proof.
  unfold braid2; simpl; intros; normal.
  rewrite from_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  normal.
  comp_right.
  comp_left.
  normal.
  bimap_left.
  rewrite to_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  comp_left.
  comp_right.
  normal.
  bimap_right.
  spose (braid_natural _ _ h _ _ i) as X.
  normal; assumption.
Qed.

Notation "∆ x" := (@diagonal _ x)
  (at level 9, format "∆ x") : morphism_scope.

(*
 The fork (split) combinator: copy x with the diagonal, then run f and g on
 the two copies, ⟨f, g⟩ = (f ⨂ g) ∘ ∆x. In a cartesian category this is the
 pairing map; here the diagonal supplies the copying without a counit. 

 --------
 叉（分裂）组合子：使用对角线复制 x，然后在两个副本上运行 f 和 g，⟨f, g⟩ = (f ⨂ g) ∘ ∆x。在笛卡尔范畴中，这是配对映射；在这里，对角线提供了无需余元的复制。
*)
Definition fork {x y z} (f : x ~> y) (g : x ~> z) :
  x ~> y ⨂ z := f ⨂ g ∘ ∆x.

#[export] Program Instance fork_respects {x y z : C} :
  Proper (equiv ==> equiv ==> equiv) (@fork x y z).
Next Obligation.
  proper.
  unfold fork.
  rewrites.
  reflexivity.
Qed.

End RelevanceMonoidal.

Notation "∆ x" := (@diagonal _ _ x)
  (at level 9, format "∆ x") : morphism_scope.
