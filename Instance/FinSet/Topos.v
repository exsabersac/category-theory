Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(*
   * * FinSet is an elementary topos

   This is the campaign's genuine elementary-topos WITNESS: skeletal
   FinSet carries every component of [Structure/Topos.v] — terminal
   object, binary products, pullbacks, exponentials, and a subobject
   classifier — with ALL data computable (the codecs of
   [Instance/FinSet/{Product,Closed,Classifier}.v] are structural
   fixpoints, so closed instances reduce by [eq_refl]) and no universe
   subtleties: every object is a [nat].  The Sets story is deliberately
   the cross-universe THEOREM file ([Instance/Sets/Classifier.v]); the
   honest, universe-clean witness lives here. 

   --------
   * * FinSet 是一个初等拓扑

   这是该活动真正的初等拓扑证据：骨架
   FinSet 包含  [Structure/Topos.v]  的每个组成部分——终对象、二元积、拉回、指数对象和子对象分类器——且所有数据都是可计算的（[Instance/FinSet/{Product,Closed,Classifier}.v] 的编解码器是结构性不动点，因此闭合实例通过 [eq_refl] 简化）且不存在宇宙的细微差别：每个对象都是 [nat] 。Sets 的故事故意作为跨宇宙定理文件（[Instance/Sets/Classifier.v]）；诚实、无宇宙污染的证据就在这里。
*)

(*
 Deliberately a plain Definition, NOT an Existing Instance: the five
 topos_* projections are Existing Instances, and the component
 structures (FinSet_Terminal, FinSet_Cartesian, ...) are already
 registered directly, so registering the bundle too would give
 typeclass search two convergent resolution paths for each component.
 Consumers pass FinSet_Topos explicitly, as the Examples below do. 

 --------
 故意给出一个简单的定义，而不是现有实例：五个 topos_* 投影是现有实例，并且组件结构（FinSet_Terminal、FinSet_Cartesian 等）已经直接注册，因此注册整个捆绑也会让类型类搜索在每个组件上有两个收敛的解析路径。使用者会像下面的示例一样显式传递 FinSet_Topos。
*)
Definition FinSet_Topos : ElementaryTopos FinSet := {|
  topos_terminal   := FinSet_Terminal;
  topos_cartesian  := FinSet_Cartesian;
  topos_pullbacks  := FinSet_Pullbacks;
  topos_closed     := FinSet_Closed;
  topos_classifier := FinSet_Classifier
|}.

(*
   * ** Sanity checks: the topos data COMPUTES

   The power object of the 2-element set is Ω ^ 2 = 2 ^ 2 = the
   4-element set, by [eq_refl] — the exponential codec of
   [Instance/FinSet/Closed.v] is a closed nat power. 

   --------
   * ** 理智检查：拓扑数据 计算

   2 元集合的幂对象是 Ω ^ 2 = 2 ^ 2 = 4 元集合，通过 [eq_refl] — [Instance/FinSet/Closed.v] 的指数编码是封闭的自然幂。
*)

Example FinSet_Pow_two : @Pow FinSet FinSet_Topos 2%nat = 4%nat := eq_refl.

Example FinSet_Pow_zero : @Pow FinSet FinSet_Topos 0%nat = 1%nat := eq_refl.

(** The truth point evaluates to [fin_true] on the sole element of 1. / 真值点在唯一元素 1 上的值为 [fin_true]。 *)

Example FinSet_truth_computes :
  @truth FinSet FinSet_Terminal FinSet_Classifier Fin.F1 = fin_true
  := eq_refl.

(*
   * The characteristic morphism of the point [truth : 1 ~> 2] itself:
   it classifies the subobject {true} ⊆ Ω, so it is the identity
   predicate on truth values — [fin_true ↦ fin_true],
   [fin_false ↦ fin_false] — and both cases reduce by [eq_refl],
   because [char] of [Instance/FinSet/Classifier.v] is a boolean
   search over the (here one-element) domain. 

   --------
   * 点 [truth : 1 ~> 2] 自身的特征态射：它对子对象 {true} ⊆ Ω 进行分类，因此它是对真值的恒等谓词 — [fin_true ↦ fin_true], [fin_false ↦ fin_false] — 并且两种情况都通过 [eq_refl] 简化，因为 [char] 的 [Instance/FinSet/Classifier.v] 是在（这里为单元素）域上的布尔搜索。
*)

Definition point_true : 1%nat ~{FinSet}~> 2%nat := fun _ => fin_true.

Lemma point_true_monic : Monic point_true.
Proof.
  apply finset_monic_iff_injective; intros a b _.
  exact (eq_trans (fin1_unique a) (eq_sym (fin1_unique b))).
Qed.

Example FinSet_char_at_true :
  char point_true point_true_monic fin_true = fin_true := eq_refl.

Example FinSet_char_at_false :
  char point_true point_true_monic fin_false = fin_false := eq_refl.

(*
   * Membership at the power object: [eval : Pow 2 × 2 ~> Ω] applied to
   the code 2 of the “negation” subset-of-truth-values (the digit
   string [fin_false, fin_true]) at the element [fin_true] yields
   [fin_false], by [eq_refl] — the computability claim is real all the
   way through the derived combinators. 

   --------
   * 在幂对象的成员资格：将 [eval : Pow 2 × 2 ~> Ω] 应用于 “否定” 真值子集（数字字符串 [fin_false, fin_true]）的代码 2，在元素 [fin_true] 上得到 [fin_false]，通过 [eq_refl] — 可计算性声明在整个派生组合子中都是真实的。
*)

Example FinSet_Pow_membership :
  @eval FinSet FinSet_Cartesian FinSet_Closed 2%nat
        (@Ω FinSet FinSet_Terminal FinSet_Classifier)
    (fin_pair (Fin.FS (Fin.FS Fin.F1) : Fin.t 4) fin_true)
    = fin_false := eq_refl.
