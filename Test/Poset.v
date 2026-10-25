Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(**
* Regression test for the [Poset] category construction (issue #124)

    nLab:      https://ncatlab.org/nlab/show/poset
    Wikipedia: https://en.wikipedia.org/wiki/Partially_ordered_set

    Issue #124 reported two defects in [Instance/Poset.v] (fixed in PR
    #136 / commit e2bcc89):

      1. the carrier [C] was typed as a [Category] rather than a plain
         [Type] (the morphism structure is unused); and
      2. the order relation was required [Asymmetric] instead of
         [Antisymmetric].  Because [PreOrder] is reflexive ([R x x]), an
         [Asymmetric] relation ([R x y -> ~ R y x]) forces [~ R x x],
         contradicting reflexivity — so under the old definition the only
         possible carrier was empty ([there_is_no_poset : Poset P -> False]).

    This file locks in the corrected definition.  Every [Definition],
    [Example], and [Lemma] below type-checks only against the fixed
    signature [Poset {C : Type} `{R : relation C} (P : PreOrder R)
    `{@Antisymmetric C eq eq_equiv R}], so a successful build IS the
    assertion.  The accompanying comments record why each item would have
    been ill-typed or unprovable under the old broken definition.

    NB on name resolution: [Instance/Proset.v] ALSO exports a
    [LessThanEqualTo_Category] (the proset over [(ℕ, ≤)]).  To make the
    [nat] block below a genuine regression guard rather than silently
    falling through to the proset's definition, every reference to the
    poset's example is fully qualified as
    [Category.Instance.Poset.LessThanEqualTo_Category]; under the old
    definition that name does not exist (no example could be built), so the
    reference fails outright.

--------
* 针对 [Poset] 类别构建的回归测试（问题 #124）

nLab：https://ncatlab.org/nlab/show/poset
维基百科：https://en.wikipedia.org/wiki/Partially_ordered_set

问题 #124 报告了 [Instance/Poset.v] 中的两个缺陷（已在 PR #136 / 提交 e2bcc89 中修复）：

1. 载体 [C] 被定义为 [Category]，而不是普通的 [Type]（同态结构未使用）；并且
2. 需要的顺序关系是 [Asymmetric]，而不是 [Antisymmetric]。由于 [PreOrder] 是自反的（[R x x]），[Asymmetric] 关系（[R x y -> ~ R y x]）会强制 [~ R x x]，这与自反性矛盾——因此根据旧定义，唯一可能的载体是空的（[there_is_no_poset : Poset P -> False]）。

此文件锁定了已更正的定义。下面的每个 [Definition]、[Example] 和 [Lemma] 仅针对固定的签名 [Poset {C : Type} `{R : relation C} (P : PreOrder R) `{@Antisymmetric C eq eq_equiv R}] 进行类型检查，因此构建成功即意味着断言成立。随附的注释记录了在旧的错误定义下每个项目为何会类型错误或无法证明的原因。

关于名称解析的注意事项：[Instance/Proset.v] 还导出了一个 [LessThanEqualTo_Category]（[(ℕ, ≤)] 上的 proset）。为了使下面的 [nat] 块成为真正的回归保护，而不是默默地回退到 proset 的定义，每一个对 poset 示例的引用都被完全限定为 [Category.Instance.Poset.LessThanEqualTo_Category]；在旧定义下，该名称不存在（无法构建示例），因此引用会直接失败。
*)

(**
** The canonical example [(ℕ, ≤)]

    [Category.Instance.Poset.LessThanEqualTo_Category] is exported from
    [Instance/Poset.v] and is built as [@Poset nat le le_preorder
    (partial_order_antisym le_partialorder)].  It exists ONLY because the
    carrier is now a plain [Type] ([nat]) and the constraint is
    [Antisymmetric] (discharged by [partial_order_antisym]).  It is the
    concrete witness that a poset over a non-empty carrier is constructible
    — the exact opposite of the old [there_is_no_poset].

--------
** 典型示例 [(ℕ, ≤)]

    [Category.Instance.Poset.LessThanEqualTo_Category] 从 [Instance/Poset.v] 导出，并构建为 [@Poset nat le le_preorder
    (partial_order_antisym le_partialorder)]。 它存在的唯一原因是承载现在是一个普通的 [Type] ([nat])，并且约束是 [Antisymmetric] (由 [partial_order_antisym] 解消)。 它是一个具体的见证，说明非空承载的偏序集是可构造的——与旧的 [there_is_no_poset] 完全相反。
*)

Definition Poset_nat : Category :=
  Category.Instance.Poset.LessThanEqualTo_Category.

(**
*** Inhabitation: the carrier is a plain, non-empty [Type]

    Under the old [{C : Category}] / [Asymmetric] signature the carrier was
    forced empty (reflexivity + asymmetry yields [False] for any element),
    so no object term could exist; moreover [obj] would be [obj[C]] for some
    [Category C], never definitionally the bare [Type nat].

--------
*** 居住性：载体是一个普通的、非空的 [Type]

    在旧的 [{C : Category}] / [Asymmetric] 签名下，载体被强制为空（自反性 + 不对称性对任何元素产生 [False]），因此不可能存在对象项；此外 [obj] 对于某些 [Category C] 来说将是 [obj[C]，永远不会在定义上是裸露的 [Type nat]。
*)

Definition poset_nat_has_object : obj[Poset_nat] := 0%nat.

Example poset_nat_obj_is_nat : obj[Poset_nat] = nat := eq_refl.

Theorem poset_nat_is_inhabited : inhabited obj[Poset_nat].
Proof. exact (inhabits 0%nat). Qed.

(**
*** Morphisms: identities from reflexivity, arrows from [≤],
        composition from transitivity

    In [Proset] the hom-type [x ~> y] is definitionally [R x y], here
    [(x <= y)%nat].  The object arguments to [@id]/[@compose] parse in
    [object_scope], so the numeric indices carry explicit [%nat].

--------
*** 态射：同一性来自自反性，箭头来自 [≤]，组合来自传递性

在 [Proset] 中，同态类型 [x ~> y] 在定义上是 [R x y]，这里是 [(x <= y)%nat]。[@id]/[@compose] 的对象参数在 [object_scope] 中解析，因此数值索引具有显式的 [%nat]。
*)

Definition poset_nat_id0 : (0 ~{Poset_nat}~> 0)%nat := @id Poset_nat 0%nat.

Definition poset_nat_hom_0_1 : (0 ~{Poset_nat}~> 1)%nat := le_S 0 0 (le_n 0).

Definition poset_nat_hom_1_2 : (1 ~{Poset_nat}~> 2)%nat := le_S 1 1 (le_n 1).

Definition poset_nat_comp_0_2 : (0 ~{Poset_nat}~> 2)%nat :=
  @compose Poset_nat 0%nat 1%nat 2%nat poset_nat_hom_1_2 poset_nat_hom_0_1.

(**
*** Antisymmetry / skeletality

    [poset_nat_skeletal] records that the poset is skeletal: any two
    mutually related objects are equal.  It is stated over [obj[Poset_nat]]
    and the poset hom-types, so it type-checks only once [Poset_nat] is
    well-formed, and its proof reuses [poset_nat_antisym], the
    standard-library antisymmetry of [(nat, ≤)] that backs the
    [Antisymmetric] hypothesis the fixed [Poset] requires.  (These
    nat-level facts document the skeletal property; the regression guards
    proper are the [Poset_nat] and [Poset_two] constructions, which do not
    build under the old definition.)

--------
*** 反对称性 / 骨架性

    [poset_nat_skeletal] 记录该偏序集是骨架的：任何两个相互相关的对象都是相等的。它是在 [obj[Poset_nat] 和偏序集 Hom 类型上陈述的，因此仅在 [Poset_nat] 合法时才能进行类型检查，并且它的证明重用了 [poset_nat_antisym]，即支持 [Antisymmetric] 假设的 [(nat, ≤)] 标准库反对称性，这是固定的 [Poset] 所需要的。(这些自然数级别的事实记录了骨架性属性；适当的回归保护是 [Poset_nat] 和 [Poset_two] 构造，而在旧定义下无法构建它们。)
*)

Definition poset_nat_antisym : Antisymmetric nat eq PeanoNat.Nat.le :=
  partial_order_antisym PeanoNat.Nat.le_partialorder.

(*
Retained as a regression guard.  The library-proper statement is
   [Proset_Skeletal_iff_Antisymmetric] (Instance/Proset/Skeletal.v), which
   proves this proposition and [Skeletal (Proset P)] mutually derivable --
   not definitionally equal, since an isomorphism is a record and not a
   pair of [R]-proofs.  For this instance the exact counterpart is
   [Nat_le_Skeletal].

--------
保留作为回归保护。库本身的声明是
   [Proset_Skeletal_iff_Antisymmetric] (Instance/Proset/Skeletal.v)，它
   证明这个命题与 [Skeletal (Proset P)] 互相可推导 ——
   不是定义上相等，因为同构是一个记录，而不是一对 [R] 证明。对于这个实例，完全对应的是
   [Nat_le_Skeletal]。
*)

Lemma poset_nat_skeletal :
  forall x y : obj[Poset_nat],
    (x ~{Poset_nat}~> y)%nat -> (y ~{Poset_nat}~> x)%nat -> x = y.
Proof. intros x y Hxy Hyx; exact (poset_nat_antisym x y Hxy Hyx). Qed.

(**
** A bespoke 2-element poset over a [Type] with no categorical structure

    This decisively exercises defect 1: the carrier [two] is an ordinary
    inductive [Type] that is NOT a [Category], so [@Poset two ...] is
    unbuildable under the old [{C : Category}] signature.  It also exercises
    defect 2: the fourth argument is an [Antisymmetric] instance, exactly
    where the old definition demanded an [Asymmetric] one.  A small bespoke
    order on [two] is used so the example is self-contained and depends only
    on this file.

--------
** 一个在没有范畴结构的 [Type] 上定制的 2 元偏序集

    这明确地体现了缺陷 1：承载体 [two] 是一个普通的归纳 [Type]，但不是 [Category]，因此在旧的 [{C : Category}] 签名下 [@Poset two ...] 是无法构建的。它还体现了缺陷 2：第四个参数是一个 [Antisymmetric] 实例，正好在旧定义要求 [Asymmetric] 实例的位置。使用了一个在 [two] 上的小型定制序，使这个例子是自包含的，仅依赖于这个文件。
*)

Inductive two : Type := lo | hi.

Definition two_le (x y : two) : Prop :=
  match x, y with
  | lo, _   => True
  | hi, hi  => True
  | hi, lo  => False
  end.

#[local] Instance two_le_preorder : PreOrder two_le.
Proof.
  constructor.
  - intros [|]; constructor.
  - intros [|] [|] [|]; simpl; auto.
Qed.

#[local] Instance two_le_antisym : @Antisymmetric two eq eq_equiv two_le.
Proof.
  intros [|] [|]; simpl; intros H1 H2;
    solve [ reflexivity | contradiction ].
Qed.

Definition Poset_two : Category := @Poset two two_le two_le_preorder two_le_antisym.

Definition poset_two_has_object : obj[Poset_two] := lo.

Example poset_two_obj_is_two : obj[Poset_two] = two := eq_refl.

Definition poset_two_hom : (lo ~{Poset_two}~> hi) := I.

Theorem poset_two_is_inhabited : inhabited obj[Poset_two].
Proof. exact (inhabits lo). Qed.

(*
Retained as a regression guard.  The library-proper statement is
   [Proset_Skeletal_iff_Antisymmetric] (Instance/Proset/Skeletal.v), which
   proves this proposition and [Skeletal (Proset P)] mutually derivable --
   not definitionally equal, since an isomorphism is a record and not a
   pair of [R]-proofs.  For this instance the exact counterpart is
   [Poset_Skeletal].

--------
保留作为回归保护。库本身的声明是
   [Proset_Skeletal_iff_Antisymmetric] (Instance/Proset/Skeletal.v)，它
   证明这个命题与 [Skeletal (Proset P)] 互相可推导 ——
   不是定义上相等，因为同构是一个记录，而不是一对 [R] 证明。对于这个实例，完全对应的是
   [Poset_Skeletal]。
*)

Lemma poset_two_skeletal :
  forall x y : obj[Poset_two],
    (x ~{Poset_two}~> y) -> (y ~{Poset_two}~> x) -> x = y.
Proof. intros x y Hxy Hyx; exact (two_le_antisym x y Hxy Hyx). Qed.

(**
** Why the OLD definition forced an empty carrier (documentation)

    This standalone lemma captures, in categorical-free vocabulary, the
    precise contradiction the fix repaired: any inhabitant of a carrier
    bearing both a [PreOrder] and an [Asymmetric] relation yields [False].
    It does not mention [Poset] and is valid regardless of its definition;
    it is here purely as explanatory contrast for issue #124.

--------
** 为什么旧定义会强制生成空载体（文档）

    这个独立的引理以无范畴的词汇捕捉到了修复所解决的精确矛盾：一个载体上同时存在 [PreOrder] 和 [Asymmetric] 关系的任何元素都会产生 [False]。
    它没有提到 [Poset]，并且无论其定义如何都是有效的；这里它纯粹作为对问题 #124 的解释性对比。
*)

Lemma asym_preorder_forces_empty :
  forall (C : Type) (R : relation C),
    PreOrder R -> Asymmetric R -> C -> False.
Proof.
  intros C R P A x.
  pose proof (@reflexivity C R (@PreOrder_Reflexive C R P) x) as Hrefl.
  exact (A x x Hrefl Hrefl).
Qed.
