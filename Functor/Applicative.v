Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Strong.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.

Generalizable All Variables.

(** Applicative functors.  / 应用函子。*)

(*
nLab: https://ncatlab.org/nlab/show/applicative+functor
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

   An applicative functor is the categorical structure underlying the
   Haskell [Applicative] class (McBride and Paterson, "Applicative
   programming with effects", JFP 18(1), 2008): it is precisely a strong lax
   monoidal endofunctor on a (closed, symmetric/braided) monoidal category.
   Here it is packaged as an endofunctor F : C ⟶ C on a monoidal closed
   category that is both [StrongFunctor] and [LaxMonoidalFunctor].

   Under that characterization the two operations of the FP class correspond
   to the comparison maps of the lax monoidal structure:

       pure : x ~> F x          ↔ the unit comparison (built in [Pure] from
                                   lax_pure : I ~> F I and the strength),
       ap   : F (x ⇒ y) ⨂ F x   ↔ the tensor comparison lax_ap (μ), composed
              ~> F y              with F eval through the internal hom ⇒.

   The closed structure supplies the internal hom ⇒ and its evaluation
   eval : (x ⇒ y) ⨂ x ~> y, which is what turns the bare tensor comparison
   F (x ⇒ y) ⨂ F x ~> F ((x ⇒ y) ⨂ x) into the Haskell-style <*>.  This is
   the categorical, law-respecting account; the lawless FP type class lives
   in Theory/Coq/Applicative.v. 

--------
nLab: https://ncatlab.org/nlab/show/applicative+functor
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

   Applicative 函子是 Haskell [Applicative] 类背后的范畴结构（McBride and Paterson,
   "Applicative programming with effects", JFP 18(1), 2008）：恰是（闭、对称/辫）
   幺半范畴上的强松弛幺半自函子。此处打包为幺半闭范畴上既是 [StrongFunctor] 又是
   [LaxMonoidalFunctor] 的自函子 F : C ⟶ C。

   在该刻画下，FP 类的两个运算对应松弛幺半结构的比较映射：

       pure : x ~> F x          ↔ 单位比较（由 lax_pure : I ~> F I 与强度在 [Pure] 中建造）
       ap   : F (x ⇒ y) ⨂ F x   ↔ 张量比较 lax_ap (μ)，经内部 hom ⇒ 与 F eval 复合
              ~> F y

   闭结构提供内部 hom ⇒ 及其求值 eval : (x ⇒ y) ⨂ x ~> y，把裸张量比较
   F (x ⇒ y) ⨂ F x ~> F ((x ⇒ y) ⨂ x) 变成 Haskell 风格的 <*>。这是范畴的、尊重定律的
   叙述；无定律的 FP 类型类在 Theory/Coq/Applicative.v。 
*)

Section ApplicativeFunctor.

Context {C : Category}.
Context `{@ClosedMonoidal C}.
Context {F : C ⟶ C}.

(*
   【Class Applicative 语法与字段展开】/ Syntax & field walkthrough（薄）

   1) 这是什么 / What this is
      范畴版 Haskell Applicative：强 + 松弛幺半的自函子 F : C ⟶ C
      （需 ClosedMonoidal C）。
      Categorical Applicative = StrongFunctor + LaxMonoidalFunctor.
      Haskell：pure / <*>；此处 pure 来自 lax 单位+强度，ap 来自 μ 与 eval。
      Haskell pure/<*> recovered from lax unit+strength and μ with eval.

   2) 字段 / Fields
      - applicative_is_strong / applicative_is_lax_monoidal（两 Instance）
      - ap := fmap eval ∘ lax_ap —— 即 <*>
        / the <*> recovered from tensor comparison

   阅读：Strong → LaxMonoidal → Pure → 本 Class；无定律 FP 版在 Theory/Coq/Applicative.v。
   Read: Strong → LaxMonoidal → Pure → here; lawless FP in Theory/Coq/.
*)

Class Applicative := {
  applicative_is_strong : StrongFunctor F;             (* tensorial strength *)
  applicative_is_lax_monoidal : LaxMonoidalFunctor F;  (* lax monoidal: η and μ  / 松弛幺半群： η 和 μ*)

  (* <*> recovered from the tensor comparison μ = lax_ap and F eval  / <*> 从张量比较中恢复 μ = lax_ap 和 F eval*)
  ap {x y} : F (x ⇒ y) ⨂ F x ~> F y :=
    fmap[F] eval ∘ @lax_ap _ _ _ _ F _ (x ⇒ y) x
}.
#[export] Existing Instance applicative_is_strong.
#[export] Existing Instance applicative_is_lax_monoidal.

Coercion applicative_is_strong : Applicative >-> StrongFunctor.
Coercion applicative_is_lax_monoidal : Applicative >-> LaxMonoidalFunctor.

End ApplicativeFunctor.

Arguments Applicative {_ _} F.
Arguments pure {C _ F _ _ _}.

Notation "pure[ F ]" := (@pure _ _ F _ _ _)
  (at level 0, format "pure[ F ]") : morphism_scope.
