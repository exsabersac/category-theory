(**
* Boundary probe: what is and is not definitional in the opposite and
      product quivers.

    Companion to Construction/Free/Quiver/Constructions.v (Mac Lane §II.7
    Ex. 1).  That file's headline is that the forgetful functor preserves
    opposites and products ON THE NOSE — [QuiverOfCat (C^op) = QuiverOp
    (QuiverOfCat C)] and its product analogue hold at Leibniz equality of the
    whole [Quiver] record, by [eq_refl] — while three neighbouring statements
    reach only [≈].  Its header records that the negative side was "measured
    and found NOT to reach [eq_refl]", but the measurements themselves lived
    outside the tree, so nothing in the build would notice if a refactor moved
    the boundary.  This file pins it, in the manner of Test/ProbeFunnyPoly.v:
    **if the [Fail] commands here stop failing, this file breaks the build.**

    Both sides are pinned deliberately.  A [Fail] alone proves very little — it
    passes just as happily when the term is ill-typed for some unrelated
    reason, or when a name has been renamed out from under it.  So each
    negative probe is paired with a positive control which must SUCCEED, and
    the controls are the headline claims themselves.  A rename or a change in
    the [Quiver] record breaks the controls loudly rather than turning the
    [Fail]s vacuously green.

    The instrument was checked before being trusted: wrapping [Fail] around a
    command that succeeds reports "The command has not failed!" and aborts
    compilation, so [Fail] here is not a no-op.

    The three negatives and their causes, each diagnosed rather than merely
    observed (the diagnoses are argued in Constructions.v's header, item (5)):

      - [Forgetful_preserves_fst]/[_snd]: [Fst] and [Snd] of
        Construction/Product.v are [Program Instance]s, so their
        [fmap_respects] field is an opaque obligation (the tree runs
        [Unset Transparent Obligations], Lib/Tactics.v).  The node and edge
        actions do agree definitionally; it is respectfulness alone that
        blocks.

      - [QuiverSwap_invol]: the node action of the twice-swapped quiver is
        [fun x => (fst x, snd x)], and surjective pairing is not definitional
        for the standard library's [prod] — it holds on a constructor and not
        on a variable.

      - [prod_setoid]: Lib/Datatypes.v's global instance has exactly the
        [equiv] that Constructions.v's [edgeset_prod] spells out, but an opaque
        [setoid_equiv].  Since [Setoid] has primitive projections with eta,
        conversion compares that field, and an opaque one defeats the
        definitional agreement.  This is why [edgeset_prod] writes its
        [Equivalence] fields out by hand instead of reusing the instance —
        a deliberate non-reuse, and therefore worth guarding.

--------
* 边界探针：在相反和乘积箭袋中什么是定义性的，什么不是定义性的。

《Construction/Free/Quiver/Constructions.v》的伴随文件（Mac Lane §II.7 习题 1）。该文件的标题指出，遗忘函子在严格意义上保持对偶和积——[QuiverOfCat (C^op) = QuiverOp (QuiverOfCat C)]，其积类比在整个 [Quiver] 记录的莱布尼茨等式下成立，通过 [eq_refl] ——而三个相邻的陈述只能达到 [≈]。它的头部记录了负面方面被“测量并发现未达到 [eq_refl]”，但测量本身存在于树之外，因此如果重构移动边界，构建中不会注意到。该文件以 Test/ProbeFunnyPoly.v 的方式固定它：**如果这里的 [Fail] 命令不再失败，此文件将破坏构建。**

双方都是刻意固定的。单凭 [Fail] 几乎无法证明什么——当某个术语因某种无关的原因类型不匹配，或者某个名称已被重命名时，它同样可以顺利通过。因此，每一个负向探测都有一个必须成功的正向对照，而这些对照就是主要声明本身。重命名或 [Quiver] 记录的更改会显著破坏对照，而不会让 [Fail] 无意义地变为绿色。

在被信任之前，仪器已经被检查过：将 [Fail] 包裹在一个成功的命令周围会报告“命令未失败！”并中止编译，所以这里的 [Fail] 并非无操作。

三种否定及其成因，每一种都是经过诊断而不仅仅是观察（诊断在 Constructions.v 的标题第（5）项中有论证）:

- [Forgetful_preserves_fst]/[_snd]：Construction/Product.v 的 [Fst] 和 [Snd] 是 [Program Instance]，因此它们的 [fmap_respects] 字段是一个不透明的义务（树运行在 [Unset Transparent Obligations]，Lib/Tactics.v）。节点和边的操作在定义上确实一致；唯一阻碍的是尊重性。

- [QuiverSwap_invol]：两次交换的箭袋的节点操作是 [fun x => (fst x, snd x)]，并且满射配对不是标准库的 [prod] 的定义性——它在构造函数上成立，而不在变量上成立。

- [prod_setoid]：Lib/Datatypes.v 的全局实例正好具有 Constructions.v 的 [edgeset_prod] 所说明的 [equiv]，但具有不透明的 [setoid_equiv]。由于 [Setoid] 具有带有 eta 的原始投影，转换会比较该字段，而不透明字段会破坏定义上的一致性。这就是为什么 [edgeset_prod] 要手动写出其 [Equivalence] 字段，而不是重用实例——这是故意的不重用，因此值得保护。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Constructions.

Local Open Scope category_scope.

(**
** Positive controls: the headline claims are definitional.

    These must SUCCEED.  They are restated here rather than cited from
    Constructions.v so that this file measures the claims independently of the
    constants that assert them.

--------
** 阳性对照：标题声明是定义性的。

    它们必须成功。这里重新陈述它们，而不是引用自 Constructions.v，以便此文件能够独立于断言它们的常量来衡量这些声明。
*)

Definition control_op (C : Category) :
  QuiverOfCat (C^op) = QuiverOp (QuiverOfCat C) := eq_refl.

Definition control_prod (C D : Category) :
  QuiverOfCat (C ∏ D) = QuiverProd (QuiverOfCat C) (QuiverOfCat D) := eq_refl.

Definition control_invol (G : Quiver) : QuiverOp (QuiverOp G) = G := eq_refl.

(**
** Negative probes: the boundary.

    These must FAIL.  Each is the [eq_refl] strengthening of a statement that
    Constructions.v delivers at [≈].

--------
** 负探针：边界。

    这些必须失败。每一个都是 [eq_refl] 对 Constructions.v 在 [≈] 提供的陈述的加强。
*)

(* [Fst]/[Snd] are [Program Instance]s: [fmap_respects] is opaque. / [Fst]/[Snd] 是 [Program Instance]：[fmap_respects] 是不透明的。 *)
Fail Definition probe_fst_strict (C D : Category) :
  QuiverHomomorphismOfFunctor _ _ (@Fst C D)
    = @QuiverFst (QuiverOfCat C) (QuiverOfCat D) := eq_refl.

Fail Definition probe_snd_strict (C D : Category) :
  QuiverHomomorphismOfFunctor _ _ (@Snd C D)
    = @QuiverSnd (QuiverOfCat C) (QuiverOfCat D) := eq_refl.

(* Surjective pairing is not definitional for [prod]. / 对于 [prod]，满射配对不是定义性的。 *)
Fail Definition probe_swap_invol_strict (G H : Quiver) :
  @compose QuiverCategory (QuiverProd G H) (QuiverProd H G) (QuiverProd G H)
    QuiverSwap QuiverSwap
    = @id QuiverCategory (QuiverProd G H) := eq_refl.

(**
** The [prod_setoid] non-reuse.

    [QuiverProd_alt] is [QuiverProd] with Lib/Datatypes.v's global
    [prod_setoid] in place of [edgeset_prod].  It is a perfectly good quiver —
    that definition succeeds — but the preservation lemma is then no longer
    definitional, which is the whole reason [edgeset_prod] exists.

--------
** [prod_setoid] 不可重用。

[QuiverProd_alt] 是 [QuiverProd]，与 Lib/Datatypes.v 的全局 [prod_setoid] 替代 [edgeset_prod]。它是一个完全可行的箭袋——该定义是成立的——但是保持引理就不再是定义性的，这正是 [edgeset_prod] 存在的全部原因。
*)

Definition QuiverProd_alt (G H : Quiver) : Quiver := {|
  nodes   := (@nodes G * @nodes H)%type;
  edges   := fun x y =>
    (@edges G (fst x) (fst y) * @edges H (snd x) (snd y))%type;
  edgeset := fun x y =>
    @prod_setoid _ _ (@edgeset G (fst x) (fst y)) (@edgeset H (snd x) (snd y))
|}.

Fail Definition probe_prod_setoid_strict (C D : Category) :
  QuiverOfCat (C ∏ D) = QuiverProd_alt (QuiverOfCat C) (QuiverOfCat D)
    := eq_refl.

(**
** The scoped universal property.

    Constructions.v proves [QuiverPair_unique] with LEIBNIZ hypotheses, noting
    that the [≈]-hypothesis form would need respectfulness of [QuiverPair],
    which is not proved.  [QuiverPair_eta] is likewise delivered at [≈].  Both
    weakenings are real, not defensive: the strengthenings fail.

--------
** 带作用域的全称性质。

Constructions.v 在 LEIBNIZ 假设下证明了 [QuiverPair_unique]，指出 [≈]-假设形式需要对 [QuiverPair] 的尊重性，但尚未证明。[QuiverPair_eta] 同样在 [≈] 处被给出。这两种弱化是真实的，而非防御性的：加强都失败了。
*)

Fail Definition probe_pair_eta_strict {G H K : Quiver}
  (M : QuiverHomomorphism K (QuiverProd G H)) :
  QuiverPair (@compose QuiverCategory _ _ _ QuiverFst M)
             (@compose QuiverCategory _ _ _ QuiverSnd M) = M := eq_refl.
