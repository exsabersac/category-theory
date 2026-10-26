Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Export Category.Structure.Monoidal.Relevance.
Require Export Category.Structure.Monoidal.Semicartesian.

Generalizable All Variables.

Section CartesianMonoidal.

Context {C : Category}.

(*
 nLab: https://ncatlab.org/nlab/show/cartesian+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Cartesian_monoidal_category

 A cartesian monoidal category is a monoidal category whose tensor is the
 categorical product and whose unit is a terminal object. In this library's
 notation that means

 x ⨂ y   is the product  x × y,
 I       is the terminal object  1,

 with the associator, unitors and braiding all induced by the universal
 property of products. We do not assume products outright; instead we
 characterise the same structure from the two halves that, combined, force
 the tensor to be a product: a coherent diagonal (RelevanceMonoidal,
 copying) and a terminal unit (SemicartesianMonoidal, discarding). The two
 proj_*_diagonal laws below are exactly the missing compatibility that makes
 the result cartesian — this is Fox's theorem (Fox 1976), stated on nLab as:
 a symmetric monoidal category with natural diagonals ∆ and augmentations e
 is cartesian iff proj_left ∘ ∆ ≈ id and proj_right ∘ ∆ ≈ id, where
 proj_left = unit_right ∘ id ⨂ eliminate and proj_right = unit_left ∘
 eliminate ⨂ id (see Semicartesian.v).

 Wikipedia: “Cartesian monoidal categories have a number of special and
 important properties, such as the existence of diagonal maps (Δ) x : x → x
 ⨂ x and augmentations (e) x : x → I for any object x. In applications to
 computer science we can think of (Δ) as 'duplicating data' and (e) as
 'deleting' data. These maps make any object into a comonoid. In fact, any
 object in a cartesian monoidal category becomes a comonoid in a unique way.

 Moreover, one can show (e.g. Heunen-Vicary 12, p. 84) that any symmetric
 monoidal category equipped with suitably well-behaved diagonals and
 augmentations must in fact be cartesian monoidal.” 

 --------
 nLab：https://ncatlab.org/nlab/show/cartesian+monoidal+category
 Wikipedia：https://en.wikipedia.org/wiki/Cartesian_monoidal_category

 笛卡尔幺半范畴是一个幺半范畴，其张量为范畴积，单位对象为终对象。在这个库的表示法中，这意味着

 x ⨂ y 是积 x × y，
 I 是终对象 1，通过结合子、单位子和交错性，它们都由乘积的普遍性质引出。我们并不直接假设存在乘积；相反，我们从两部分来刻画相同的结构，这两部分结合起来，会强制张量成为乘积：一个相容的对角线（RelevanceMonoidal，复制）和一个终单位（SemicartesianMonoidal，丢弃）。下面的两个 proj_*_diagonal 法则正是使结果成为笛卡尔的缺失兼容性——这是 Fox 的定理（Fox 1976），在 nLab 上陈述为：具有自然对角线 ∆ 和增强 e 的对称单体范畴，当且仅当 proj_left ∘ ∆ ≈ id 且 proj_right ∘ ∆ ≈ id 时是笛卡尔的，其中 proj_left = unit_right ∘ id ⨂ eliminate，proj_right = unit_left ∘ eliminate ⨂ id（参见 Semicartesian.v）。维基百科：“笛卡尔幺半群范畴具有许多特殊且重要的性质，例如存在对角映射 (Δ)_x: x → x ⨂ x 和增广映射 (e)_x: x → I 对于任意对象 x。在计算机科学的应用中，我们可以将 (Δ) 看作“复制数据”，将 (e) 看作“删除数据”。这些映射使得任何对象成为余半群。事实上，笛卡尔幺半群范畴中的任何对象都以唯一的方式成为余半群。

 此外，可以证明（例如 Heunen-Vicary 12, 第 84 页）任何具有适当良好行为的对角映射和增广映射的对称幺半群范畴实际上必须是笛卡尔幺半群范畴。”
*)

Class CartesianMonoidal := {
  cartesian_is_relevance     : @RelevanceMonoidal C;
  cartesian_is_semicartesian : @SemicartesianMonoidal C _;

  (*
 Fox's coherence: copying then discarding one copy is the identity. These
 two laws are precisely what upgrades the relevance + semicartesian data to
 a genuine product (tensor = ×), per the nLab characterisation above. 

 --------
 狐狸的一致性：复制然后丢弃一份副本就是恒等。这两个定律正是将相关性 + 半笛卡尔数据升级为真正的积（张量 = ×）的关键，正如上述 nLab 的描述所示。
*)
  proj_left_diagonal  {x} : proj_left  ∘ diagonal ≈ id[x];
  proj_right_diagonal {x} : proj_right ∘ diagonal ≈ id[x];

  (*
 Unit/braiding coherence λ ∘ σ ≈ ρ and ρ ∘ σ ≈ λ at the unit. In a
 symmetric monoidal category these are derivable from Mac Lane's coherence
 theorem rather than minimal; they are kept as explicit fields here because
 this library's SymmetricMonoidal does not expose that derivation, and
 downstream proofs (e.g. Heunen_Vicary/Proofs.v, Group/Proofs.v) rewrite with
 them directly. 

 --------
 在单位处，单元/编织相干 λ ∘ σ ≈ ρ 和 ρ ∘ σ ≈ λ。在对称幺半群范畴中，这些是可以从 Mac Lane 的相干定理推导出来的，而不是最小的；这里将它们保留为显式字段是因为该库的 SymmetricMonoidal 并未暴露该推导，并且下游证明（例如 Heunen_Vicary/Proofs.v，Group/Proofs.v）直接使用它们进行重写。
*)
  unit_left_braid  {x} : unit_left  ∘ @braid _ _ x I ≈ unit_right;
  unit_right_braid {x} : unit_right ∘ @braid _ _ I x ≈ unit_left
}.
#[export] Existing Instance cartesian_is_semicartesian.
#[export] Existing Instance cartesian_is_relevance.

Coercion cartesian_is_relevance : CartesianMonoidal >-> RelevanceMonoidal.
Coercion cartesian_is_semicartesian : CartesianMonoidal >-> SemicartesianMonoidal.

End CartesianMonoidal.
