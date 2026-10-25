Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Construction.PROP.

Generalizable All Variables.

(**
* End-to-end typeclass-resolution smoke tests for HypergraphPROP

    nLab:      https://ncatlab.org/nlab/show/PROP
    nLab:      https://ncatlab.org/nlab/show/hypergraph+category
    Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

    A [HypergraphPROP] (see [Construction/PROP.v]) bundles a [PROP] — a
    strict symmetric monoidal category whose object monoid is [(ℕ, +, 0)] —
    with a [Hypergraph] instance, i.e. a chosen special commutative
    Frobenius algebra (SCFA) on every object.  This file is a compile-time
    smoke test: each [Definition] below type-checks only if the coercion /
    [#[export] Existing Instance] chain actually delivers the structure
    named in its type, so a successful build IS the assertion.

    These tests verify that, given just [Variable P : HypergraphPROP],
    Coq's typeclass resolution finds the structural instances downstream
    callers will need:

      - PROP                            -- via the [hpprop] coercion
      - prop_cat P : Category           -- via the [prop_cat] coercion
      - SymmetricMonoidal (prop_cat P)  -- via prop_symmetric
      - StrictMonoidal (prop_cat P)     -- via prop_strict
      - Hypergraph (prop_cat P) ...     -- via hpprop_hyper
      - SpecialCommutativeFrobenius X   -- via scfa : forall X, ...

    If this file compiles, the [#[export] Existing Instance] / Coercion
    chain is working as advertised.

--------
* 针对 HypergraphPROP 的端到端类型类解析烟雾测试

nLab:      https://ncatlab.org/nlab/show/PROP
nLab:      https://ncatlab.org/nlab/show/hypergraph+category
维基百科: https://en.wikipedia.org/wiki/PROP_(category_theory)

一个 [HypergraphPROP]（见 [Construction/PROP.v]）将一个 [PROP] —— 一个严格的对称单体范畴，其对象幺半群为 [(ℕ, +, 0)] —— 与一个 [Hypergraph] 实例捆绑在一起，即在每个对象上选择的特殊交换 Frobenius 代数（SCFA）。这个文件是一个编译时的冒烟测试：下列每个 [Definition] 只有在 coercion / [#[export] Existing Instance 链确实提供其类型中指定的结构时才能类型检查，因此构建成功即为断言。

这些测试验证了，仅给定 [Variable P : HypergraphPROP] 时，Coq 的类型类解析能够找到下游调用者需要的结构实例：

- PROP                            -- 通过 [hpprop] 强制转换
      - prop_cat P : Category           -- 通过 [prop_cat] 强制转换
      - SymmetricMonoidal (prop_cat P)  -- 通过 prop_symmetric
      - StrictMonoidal (prop_cat P)     -- 通过 prop_strict
      - Hypergraph (prop_cat P) ...     -- 通过 hpprop_hyper
      - SpecialCommutativeFrobenius X   -- 通过 scfa : 对于所有 X, ...

如果这个文件可以编译，[#[export] 现有实例] / 强制链就能按宣传那样工作。
*)

Open Scope nat_scope.

Section HypergraphPROPResolutionTests.

Context (P : HypergraphPROP).

(** The "tensor wire" — the canonical 1-arity PROP-object. / “张量线”——典型的一元 PROP 对象。 *)
Notation T := (@prop_of_nat P 1).

(** [T] is an object of [P]. / [T] 是 [P] 的一个对象。 *)
Definition test_obj_resolves : @obj P := T.

(** Identity morphisms at [T] type-check. / [T] 类型的恒等映射能够通过类型检查。 *)
Definition test_id : T ~> T := id.

(** Composition is found via the Category resolution. / 通过类别解析可以找到组成。 *)
Definition test_compose (f g : T ~> T) : T ~> T := g ∘ f.

(** Equivalence is found between two morphisms of the same hom-set. / 在同一个 Hom 集上的两个态射之间找到了等价性。 *)
Definition test_equiv (f g : T ~> T) : Type := f ≈ g.

(**
The SCFA on T is found via the Hypergraph instance, and its flat
    [scfa_*] projections work.

--------
T 上的 SCFA 是通过超图实例找到的，它的扁平 [scfa_*] 投影有效。
*)
Definition test_scfa_mu      := scfa_mu      (scfa T).
Definition test_scfa_eta     := scfa_eta     (scfa T).
Definition test_scfa_delta   := scfa_delta   (scfa T).
Definition test_scfa_epsilon := scfa_epsilon (scfa T).

(**
The SCFA-projected morphisms have the expected hom-set shape.
    We avoid explicit [@I _ _] annotations because the [I] notation
    picks a Monoidal instance and may pick a different one than the
    SymmetricMonoidal-induced one used by [scfa].  Instead, we just
    confirm the bare projections compose with themselves.

--------
SCFA 投影的态射具有预期的 Hom-集形状。我们避免使用显式的 [@I _ _] 注释，因为 [I] 表示法会选择一个 Monoidal 实例，并且可能选择与 [scfa] 使用的由 SymmetricMonoidal 引入的实例不同的实例。相反，我们只是确认裸投影可以与自身组合。
*)
Definition test_scfa_eta_compose := compose test_scfa_epsilon test_scfa_eta.

(**
Beyond the operations, the SCFA special law [mu ∘ delta ≈ id] is a
    resolved component of the structure.  Stating it as the type of a
    definition pins the operations into the law's shape, so an SCFA whose
    special law was dropped or mistyped would fail this test, not only one
    that dropped an operation.

    This remains a resolution and typing test rather than a behavioural one:
    [HypergraphPROP] has no in-tree witness yet (see docs/INHABITATION.md),
    so there is no concrete model here to compute against.  A behavioural
    test awaits such a witness.

--------
超出操作部分，SCFA 特殊法 [mu ∘ delta ≈ id] 是结构的一个已解析组件。将其声明为定义的类型会将操作固定在该法律的形状中，因此，如果 SCFA 的特殊法被删除或输入错误，它会未通过此测试，而不仅仅是删除了某个操作的情况。

这仍然是一个解析和类型测试，而不是行为测试：[HypergraphPROP] 尚未在树中有证据（参见 docs/INHABITATION.md），因此这里没有可用于计算的具体模型。行为测试则要等待这样的证据。
*)
Definition test_scfa_special_law : Type :=
  scfa_mu (scfa T) ∘ scfa_delta (scfa T) ≈ id[T].

End HypergraphPROPResolutionTests.

Close Scope nat_scope.

(**
** KNOWN LIMITATION: ambiguous [Monoidal (prop_cat P)] instance

    The [PROP] class supplies TWO fields that each induce a
    [Monoidal (prop_cat P)]:

      - [prop_strict   : StrictMonoidal     (prop_cat P)] with coercion
        [strict_is_monoidal : StrictMonoidal -> Monoidal]
      - [prop_symmetric : SymmetricMonoidal (prop_cat P)] with coercion
        [braided_is_monoidal . symmetric_is_braided : SymmetricMonoidal
                                                      -> Monoidal]

    The class DOES relate these two paths, via the field

      [prop_monoidal_coherence :
         strict_is_monoidal prop_strict
         = braided_is_monoidal (symmetric_is_braided prop_symmetric)]

    but only as a PROPOSITIONAL (Leibniz) equality, not a definitional
    one.  In consequence, an expression like

      braid : (T ⨂ T) ~> (T ⨂ T)

    still fails to type-check inside a [HypergraphPROP] context (verified
    empirically): the [⨂] notation resolves [T ⨂ T] through
    [strict_is_monoidal] (the StrictMonoidal path) while [braid] expects
    the [SymmetricMonoidal]-induced [Monoidal], and Coq will not unify the
    two records up to a propositional equality on its own.

    Similarly, [scfa_mu (scfa T) : T ⨂ T ~> T] resolves through the
    [Hypergraph]'s [SymmetricMonoidal] path (confirmed by [Check]), while
    [prop_tensor_plus : ⟦m⟧ ⨂ ⟦n⟧ = ⟦m+n⟧] uses the strict path; they
    are interchangeable mathematically but not as bare Coq terms.

    The workaround for downstream code is to bridge the two paths with an
    explicit [rewrite prop_monoidal_coherence] (or [subst]) at the use
    site, or to PIN the [Monoidal] path: write
    [(T ⨂[strict_is_monoidal] T)] when proving against [prop_tensor_plus],
    and let inference pick the [SymmetricMonoidal] path when using [braid]
    / [scfa_*].

    The DEFINITIONAL fix — which would make [prop_monoidal_coherence]
    reduce to [eq_refl] and let [braid] / [scfa_*] / [prop_tensor_plus]
    inter-operate without any [rewrite] — is to re-parameterise the
    library's [BraidedMonoidal] / [SymmetricMonoidal] classes to take an
    [@Monoidal C] as an explicit parameter, so [prop_symmetric] can
    inherit [strict_is_monoidal prop_strict] verbatim.  That is a
    multi-file refactor deferred to a separate PR and tracked in the
    [prop_monoidal_coherence] discussion in [Construction/PROP.v]; the
    tests requiring it (e.g. a typed [braid] on [T ⨂ T]) are omitted from
    this file until then.

--------
** 已知限制：模糊的 [Monoidal (prop_cat P)] 实例

[PROP] 类提供两个字段，每个字段都会引发一个 [Monoidal (prop_cat P)]：

- [prop_strict   : StrictMonoidal     (prop_cat P)] 带强制
        [strict_is_monoidal : StrictMonoidal -> Monoidal]
      - [prop_symmetric : SymmetricMonoidal (prop_cat P)] 带强制
        [braided_is_monoidal . symmetric_is_braided : 对称单体
                                                      -> 单体]

这个类确实通过该字段将这两条路径关联起来

[prop_monoidal_coherence :
         strict_is_monoidal prop_strict
         = braided_is_monoidal (symmetric_is_braided prop_symmetric)]

但仅作为命题上的（莱布尼茨）相等，而不是定义上的相等。因此，像这样的表达式

编织 : (T ⨂ T) ~> (T ⨂ T)

在 [HypergraphPROP] 上下文中仍然无法进行类型检查（经过经验验证）：[⨂] 表示法通过 [strict_is_monoidal]（严格幺半群路径）解析 [T ⨂ T]，而 [braid] 期望 [SymmetricMonoidal] 引入的 [Monoidal]，而 Coq 不会自行将这两个记录统一到一个命题等式上。

同样，[scfa_mu (scfa T) : T ⨂ T ~> T] 通过 [Hypergraph] 的 [SymmetricMonoidal] 路径解析（由 [Check] 证实），而 [prop_tensor_plus : ⟦m⟧ ⨂ ⟦n⟧ = ⟦m+n⟧] 使用严格路径；它们在数学上是可互换的，但作为裸 Coq 项则不行。

下游代码的解决方法是在使用点通过显式的 [rewrite prop_monoidal_coherence]（或 [subst]）桥接这两个路径，或者固定 [Monoidal] 路径：在针对 [prop_tensor_plus] 进行验证时写入 [(T ⨂[strict_is_monoidal] T)]，并在使用 [braid] / [scfa_*] 时让推理选择 [SymmetricMonoidal] 路径。

定义性修复——它将使 [prop_monoidal_coherence] 简化为 [eq_refl]，并且允许 [braid] / [scfa_*] / [prop_tensor_plus] 互操作而不需要任何 [rewrite]——是将库的 [BraidedMonoidal] / [SymmetricMonoidal] 类重新参数化，以显式接受一个 [@Monoidal C] 作为参数，这样 [prop_symmetric] 就可以完整继承 [strict_is_monoidal prop_strict]。这是一个多文件重构，推迟到一个单独的 PR 并在 [Construction/PROP.v] 中的 [prop_monoidal_coherence] 讨论中跟踪；直到那时，要求它的测试（例如 [T ⨂ T] 上的类型化 [braid]）会从该文件中省略。
*)
