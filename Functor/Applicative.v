Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Strong.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.

Generalizable All Variables.

(** Applicative functors. *)

(* nLab: https://ncatlab.org/nlab/show/applicative+functor
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
   叙述；无定律的 FP 类型类在 Theory/Coq/Applicative.v。 *)

Section ApplicativeFunctor.

Context {C : Category}.
Context `{@ClosedMonoidal C}.
Context {F : C ⟶ C}.

Class Applicative := {
  applicative_is_strong : StrongFunctor F;             (* tensorial strength *)
  applicative_is_lax_monoidal : LaxMonoidalFunctor F;  (* lax monoidal: η and μ *)

  (* <*> recovered from the tensor comparison μ = lax_ap and F eval *)
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
