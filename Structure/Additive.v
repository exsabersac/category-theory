Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Preadditive.

Generalizable All Variables.

(** * Additive categories / * 加法范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/additive+category
 Wikipedia: https://en.wikipedia.org/wiki/Additive_category

 An additive category is a preadditive category — one enriched in abelian
 groups — with a zero object and all binary biproducts.  The library's
 [Preadditive] class records only commutative-monoid enrichment
 (CMon-enrichment), so the abelian-group half of the classical definition
 is completed here: [Additive] packages a zero object, a preadditive
 structure, a chosen biproduct for every pair of objects, and an additive
 inverse [pneg] turning each hom commutative monoid into an abelian group
 ([padd_pneg]).

 The group axioms alone yield the familiar calculus of negation:
 cancellation ([padd_cancel_right]), uniqueness of inverses
 ([pneg_unique]), involutivity ([pneg_pneg]), preservation of zero
 ([pneg_pzero]), and compatibility of negation with composition on either
 side ([compose_pneg_left], [compose_pneg_right]), extending the
 bilinearity of composition from addition to subtraction.  Subtraction
 [psub] is sugar for adding the negation; it joins `+` and `0` in
 [addition_scope].
 The bare Ab-enriched notion — group homs with bilinear composition
 and NO zero object or biproducts — is Structure/AbCategory.v's
 [AbEnriched]; every [Additive] category is an instance of it. 

 --------
 nLab: https://ncatlab.org/nlab/show/additive+category
 Wikipedia: https://en.wikipedia.org/wiki/Additive_category

 加法范畴是一个预加范畴——一个在阿贝尔群中富涵的范畴——具有零对象和所有二元二积。该库的[Preadditive]类仅记录交换幺半群富涵（CMon富涵），因此经典定义中的阿贝尔群部分在这里得以补全：[Additive] 封装了一个零对象、一个预加结构、每对对象的选定二积，以及一个加法逆[pneg]，将每个同态交换幺半群转为阿贝尔群（[padd_pneg]）。仅凭群公理就产生了熟悉的取反演算：消去律 ([padd_cancel_right])、逆元的唯一性 ([pneg_unique])、自反性 ([pneg_pneg])、零元的保持 ([pneg_pzero])，以及取反与任一侧组合的兼容性 ([compose_pneg_left], [compose_pneg_right])，将组合的双线性从加法扩展到减法。减法 [psub] 是加上取反的简便表示；它在 [addition_scope] 中将 `+` 和 `0` 连接起来。最基本的 Ab-增强概念——具有双线性组合的群同态且没有零对象或二积对象——是 Structure/AbCategory.v 的 [AbEnriched]；每个 [Additive] 类别都是它的一个实例。
*)

Class Additive (C : Category) := {
  additive_zero : @ZeroObject C;
  additive_preadditive : @Preadditive C;
  additive_biproducts : @HasBiproducts C additive_zero;

  (*
 Each hom-setoid upgrades from a commutative monoid to an abelian
 group: every morphism has an additive inverse. 

 --------
 每个同态集合从交换幺半群升级为阿贝尔群：每个态射都有一个加法逆元。
*)
  pneg {x y : C} : (x ~> y) -> (x ~> y);

  pneg_respects {x y : C} :
    Proper (equiv ==> equiv) (@pneg x y);

  padd_pneg {x y : C} (f : x ~> y) :
    padd f (pneg f) ≈ pzero
}.

(*
 The structural fields are registered as conditional instances in the
 manner of Structure/Monoidal/Markov.v and Structure/Regular.v: they fire
 only under an [Additive C] hypothesis, and registering them lets the
 additive notations, the zero-morphism lemmas, and the biproduct
 accessors resolve in any additive context. 

 --------
 结构字段以条件实例的方式注册，类似于 Structure/Monoidal/Markov.v 和 Structure/Regular.v：它们仅在 [Additive C] 假设下触发，注册它们可以让加法符号、零态射引理以及二重积访问器在任何加法上下文中得到解析。
*)
#[export] Existing Instance additive_zero.
#[export] Existing Instance additive_preadditive.
#[export] Existing Instance additive_biproducts.
#[export] Existing Instance pneg_respects.

Section AdditiveLaws.

Context {C : Category}.
Context `{A : @Additive C}.

(*
 Negation is a left inverse as well, by commutativity of addition. 

 --------
 根据加法的交换律，取反也是一个左逆元。
*)
Lemma pneg_padd {x y : C} (f : x ~> y) :
  padd (pneg f) f ≈ pzero.
Proof.
  rewrite padd_comm.
  apply padd_pneg.
Qed.

(*
 Right cancellation: adding [pneg h] on the right and reassociating
 strips the common summand. 

 --------
 右消去：在右侧添加 [pneg h] 并重新结合，会去掉公共的加数。
*)
Lemma padd_cancel_right {x y : C} (f g h : x ~> y) :
  padd f h ≈ padd g h -> f ≈ g.
Proof.
  intros H.
  rewrite <- (padd_zero_right f).
  rewrite <- (padd_pneg h).
  rewrite <- padd_assoc.
  rewrite H.
  rewrite padd_assoc.
  rewrite padd_pneg.
  apply padd_zero_right.
Qed.

(*
 Inverses are unique: any right inverse of f is [pneg f]. 

 --------
 逆元是唯一的：f 的任何右逆都是 [pneg f]。
*)
Lemma pneg_unique {x y : C} (f g : x ~> y) :
  padd f g ≈ pzero -> g ≈ pneg f.
Proof.
  intros H.
  apply (padd_cancel_right _ _ f).
  rewrite pneg_padd.
  rewrite padd_comm.
  exact H.
Qed.

(* Negation is involutive, by uniqueness of inverses. / 否定是自反的，由逆元的唯一性决定。 *)
Lemma pneg_pneg {x y : C} (f : x ~> y) :
  pneg (pneg f) ≈ f.
Proof.
  symmetry.
  apply pneg_unique.
  apply pneg_padd.
Qed.

(* The zero morphism is its own inverse. / 零同态是它自己的逆。 *)
Lemma pneg_pzero {x y : C} :
  pneg (@pzero C _ x y) ≈ pzero.
Proof.
  symmetry.
  apply pneg_unique.
  apply padd_zero_left.
Qed.

(*
 Postcomposition commutes with negation: h ∘ pneg f is an additive
 inverse of h ∘ f, since composition distributes over the addition and
 absorbs the zero. 

 --------
 后组合与取反可交换：h ∘ pneg f 是 h ∘ f 的加法逆元，因为组合在加法上分配并且吸收零。
*)
Lemma compose_pneg_left {x y z : C} (h : y ~> z) (f : x ~> y) :
  h ∘ pneg f ≈ pneg (h ∘ f).
Proof.
  apply pneg_unique.
  rewrite <- compose_padd_left.
  rewrite padd_pneg.
  apply compose_pzero_right.
Qed.

(* Precomposition commutes with negation, dually. / 预构成与取反是对偶可换的。 *)
Lemma compose_pneg_right {x y z : C} (f : y ~> z) (h : x ~> y) :
  pneg f ∘ h ≈ pneg (f ∘ h).
Proof.
  apply pneg_unique.
  rewrite <- compose_padd_right.
  rewrite padd_pneg.
  apply compose_pzero_left.
Qed.

End AdditiveLaws.

(*
 Subtraction of parallel morphisms, and its notation alongside `+` and
 `0` in addition_scope. 

 --------
 平行态射的减法，以及它在 addition_scope 中与 `+` 和 `0` 一起的表示法。
*)
Definition psub {C : Category} `{A : @Additive C} {x y : C}
  (f g : x ~> y) : x ~> y := padd f (pneg g).

Infix "-" := psub : addition_scope.

#[export] Instance psub_respects {C : Category} `{A : @Additive C} {x y : C} :
  Proper (equiv ==> equiv ==> equiv) (@psub C A x y).
Proof.
  intros f1 f2 Hf g1 g2 Hg.
  unfold psub.
  now rewrite Hf, Hg.
Qed.
