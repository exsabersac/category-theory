Require Import Category.Lib.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Applicative.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Natural.Transformation.Strong.
Require Import Category.Natural.Transformation.Monoidal.

Generalizable All Variables.

(** Morphisms of applicative functors.  / 应用函子的态射。*)

(*
nLab: https://ncatlab.org/nlab/show/applicative+functor
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

   A morphism of applicative functors -- McBride and Paterson's “applicative
   transformation” (“Applicative programming with effects”, JFP 18(1), 2008,
   §5) -- is a natural transformation N : F ⟹ G between applicative functors
   that respects the applicative operations:

       N (pure x)  ≈ pure x,
       N (f <*> x) ≈ N f <*> N x.

   Since an applicative functor is here a strong lax monoidal endofunctor
   (see Functor/Applicative.v), and [pure]/[ap] are recovered from the lax
   monoidal comparison maps (lax_pure, lax_ap = η, μ) together with the
   strength, preserving the FP operations is equivalent to preserving that
   underlying structure.  Accordingly [Applicative_Transform] is packaged as a
   natural transformation that is simultaneously a [Strong_Transform] (commutes
   with the tensorial strength) and a [LaxMonoidal_Transform] (commutes with
   lax_pure and lax_ap) -- the transformation-level analogue of the way
   [Applicative] bundles [StrongFunctor] with [LaxMonoidalFunctor].  These two
   conditions jointly entail the [pure]- and [<*>]-preservation laws above.

   This is the categorical, law-respecting account; the lawless FP version
   lives in Theory/Coq/Applicative.v. 

--------
nLab：https://ncatlab.org/nlab/show/applicative+functor
维基百科：https://en.wikipedia.org/wiki/Applicative_functor

一个应用函子（applicative functor）的态射——McBride 和 Paterson 的“applicative 转换”（“带效果的应用编程”，《JFP》18(1), 2008, 第5节）——是一个自然变换 N : F ⟹ G，位于应用函子之间，并且遵循应用操作：

N (pure x)  ≈ pure x,
       N (f <*> x) ≈ N f <*> N x.

由于这里的可应用函子是一个强弱单体函子（参见 Functor/Applicative.v），并且 [pure]/[ap] 是通过弱单体比较映射（lax_pure, lax_ap = η, μ）以及强度恢复的，因此保留 FP 操作等同于保留其底层结构。因此 [Applicative_Transform] 被打包为一个自然变换，该变换同时是一个 [Strong_Transform]（与张量强度交换）和 [LaxMonoidal_Transform]（与 lax_pure 和 lax_ap 交换）——这是 [Applicative] 将 [StrongFunctor] 与 [LaxMonoidalFunctor] 捆绑的方式在变换级别的类比。这两个条件共同推导出上述 [pure] 和 [<*>] 的保持定律。

这是无条件的、遵守法律的版本；无法无天的 FP 版本位于 Theory/Coq/Applicative.v。 
*)

(*
   【Class Applicative_Transform 展开】/ Walkthrough（薄）
   入口 Transform 见 Theory/Natural/Transformation.v（已有展开，不重复）。

   保持 Applicative 的自然变换 = 同时 Strong_Transform + LaxMonoidal_Transform。
   Nat. trans. that preserves Applicative = strong + lax-monoidal on the nose.
   推导 pure / <*> 的保持；无定律 FP 版在 Theory/Coq/Applicative.v。
*)

Class Applicative_Transform `{@ClosedMonoidal C}
  `{@Applicative C _ F}
  `{@Applicative C _ G} (N : F ⟹ G) := {
  applicative_transform_is_strong_transformation :
    @Strong_Transform C _ F _ G _ N;
  applicative_transform_is_lax_monoidal_transformation :
    @LaxMonoidal_Transform C _ F _ G _ N
}.
#[export] Existing Instance applicative_transform_is_strong_transformation.
#[export] Existing Instance applicative_transform_is_lax_monoidal_transformation.

Coercion applicative_transform_is_strong_transformation :
  Applicative_Transform >-> Strong_Transform.
Coercion applicative_transform_is_lax_monoidal_transformation :
  Applicative_Transform >-> LaxMonoidal_Transform.
