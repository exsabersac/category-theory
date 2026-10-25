Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.

Generalizable All Variables.

(** * Preadditive categories / * 预加性范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/preadditive+category
 Wikipedia: https://en.wikipedia.org/wiki/Preadditive_category

 A preadditive category in the classical sense is a category enriched in
 abelian groups: every hom-set is an abelian group and composition is
 bilinear.  The class below records the additive skeleton of that notion
 in setoid form: each hom-setoid carries a commutative monoid structure
 ([padd] with unit [pzero]) that respects ≈, composition distributes over
 addition on both sides, and the zero morphism absorbs composition on
 both sides.  Additive inverses are deliberately not demanded, so the
 class is precisely enrichment in commutative monoids (CMon-enrichment);
 every Ab-enriched category is an instance (the standalone
 Ab-enriched class — this plus negation, nothing more — is
 Structure/AbCategory.v's [AbEnriched]), and this much structure
 already supports biproducts and the matrix calculus.  The laws are
 self-dual, so C^op is preadditive whenever C is.

 The additive notations live in their own [addition_scope] (key %padd),
 keeping `+` and `0` untouched elsewhere; users opt in locally with
 `Open Scope addition_scope` or the %padd scope key.

 When the category also has a zero object, the enrichment zero agrees
 with the tunnelled zero morphism of Structure/ZeroObject.v; this is
 [pzero_zero_mor] below. 

 --------
 nLab:       https://ncatlab.org/nlab/show/preadditive+category 
 维基百科:  https://en.wikipedia.org/wiki/Preadditive_category在经典意义上，前加性范畴是以阿贝尔群为丰富的范畴：每个 Hom 集都是一个阿贝尔群，并且复合是双线性的。下面的类以集合同态形式记录了该概念的加性骨架：每个同态集都携带一个交换幺半群结构（单位 [pzero]）并且尊重 ≈，复合在两边对加法分配，零态射在两边吸收复合。故意不要求加性逆元，因此该类正是交换幺半群（CMon-丰富）的丰富；每个 Ab-丰富范畴都是一个实例（独立的 Ab-丰富类——这加上取负，没有更多——是 Structure/AbCategory.v 的 [AbEnriched]），而这一点结构已经支持积和矩阵运算。这些定律是自对偶的，因此当 C 是预加性的时，C^op 也是预加性的。

 加法表示法存在于它们自己的 [addition_scope] （关键字 %padd）中，在其他地方保持 `+` 和 `0` 不变；用户通过 `Open Scope addition_scope` 或 %padd 作用域关键字在本地选择使用。

 当该范畴还有一个零对象时，加法丰富结构中的零与 Structure/ZeroObject.v 中的隧道零态射一致；下面是 [pzero_zero_mor]。
*)

Class Preadditive (C : Category) := {
  padd {x y : C} : (x ~> y) -> (x ~> y) -> (x ~> y);
  pzero {x y : C} : x ~> y;

  padd_respects {x y : C} :
    Proper (equiv ==> equiv ==> equiv) (@padd x y);

  (* (hom(x,y), padd, pzero) is a commutative monoid. / (hom(x,y), padd, pzero) 是一个交换幺半群。 *)
  padd_assoc {x y : C} (f g h : x ~> y) :
    padd (padd f g) h ≈ padd f (padd g h);
  padd_comm {x y : C} (f g : x ~> y) :
    padd f g ≈ padd g f;
  padd_zero_left {x y : C} (f : x ~> y) :
    padd pzero f ≈ f;

  (* Composition is additive in each argument separately. / 组合在每个参数上都是可加的。 *)
  compose_padd_left {x y z : C} (h : y ~> z) (f g : x ~> y) :
    h ∘ padd f g ≈ padd (h ∘ f) (h ∘ g);
  compose_padd_right {x y z : C} (f g : y ~> z) (h : x ~> y) :
    padd f g ∘ h ≈ padd (f ∘ h) (g ∘ h);

  (* The additive unit absorbs composition on both sides. / 加法单元在两侧吸收组成。 *)
  compose_pzero_left {x y z : C} (f : x ~> y) :
    @pzero y z ∘ f ≈ pzero;
  compose_pzero_right {x y z : C} (f : y ~> z) :
    f ∘ @pzero x y ≈ pzero
}.

#[export] Existing Instance padd_respects.

(* The right unit law follows from commutativity and the left unit law. / 右单位定律由交换律和左单位定律推导而来。 *)
Corollary padd_zero_right {C : Category} `{P : @Preadditive C} {x y : C}
  (f : x ~> y) :
  padd f pzero ≈ f.
Proof.
  rewrite padd_comm.
  apply padd_zero_left.
Qed.

(* Additive notations in a dedicated scope, so `+` and `0` retain their usual meanings wherever this scope is not open. / 在专用范围内的加法符号，因此 `+` 和 `0` 在该范围未打开的任何地方都保持其通常含义。 *)
Declare Scope addition_scope.
Delimit Scope addition_scope with padd.

Infix "+" := padd : addition_scope.
Notation "0" := pzero : addition_scope.

(*
 Compatibility with zero objects: in a preadditive category that also has
 a zero object, the enrichment zero [pzero] coincides with the canonical
 zero morphism x ~> 1 ~> 0 ~> y of Structure/ZeroObject.v.  The proof
 exhibits [pzero] as a morphism factoring through the zero object —
 [compose_pzero_left] collapses each tunnelling leg — after which
 [zero_mor_unique] identifies it with [zero_mor]. 

 --------
 与零对象的兼容性：在一个预加性范畴中，如果它也有零对象，则加丰富的零  [pzero]  与 Structure/ZeroObject.v 中的规范零态射 x ~> 1 ~> 0 ~> y 相一致。证明展示了  [pzero]  作为一个通过零对象分解的态射 —  [compose_pzero_left]  压缩每个隧道分支 — 然后  [zero_mor_unique]  将其与  [zero_mor]  识别。
*)
Lemma pzero_zero_mor {C : Category} `{P : @Preadditive C} `{Z : @ZeroObject C}
  {x y : C} :
  @pzero C P x y ≈ @zero_mor C Z x y.
Proof.
  rewrite <- (@zero_mor_unique C Z x y
                (@one C (@zero_terminal C Z) x)
                (@pzero C P (@initial_obj C (@zero_initial C Z)) y)).
  (*
 Goal: pzero ≈ (pzero ∘ from zero_coincide) ∘ one.  Each composite with
 [pzero] on the left collapses by [compose_pzero_left]. 

 --------
 目标：pzero ≈ (pzero ∘ from zero_coincide) ∘ one。每个与 [pzero] 在左侧的复合通过 [compose_pzero_left] 崩塌。
*)
  rewrite compose_pzero_left.
  rewrite compose_pzero_left.
  reflexivity.
Qed.
