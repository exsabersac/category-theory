(**
* Boundary probes for the two-variable Yoneda isomorphism

    Companion to Functor/Hom/Yoneda/Natural.v (issue #316; Mac Lane §III.2
    Lemma 2, Riehl §2.2 and §E.1, Awodey §8.3 Lemma 8.2).  That file makes
    strength claims of two DIFFERENT kinds, and this file pins both.  **If
    the [Fail] commands below stop failing, this file breaks the build.**

    THE TWO KINDS ARE NOT THE SAME AND ARE NOT DESCRIBED WITH ONE WORD.

    (1) FORMABILITY.  [Covariant_Yoneda_Lemma] and [Yoneda_Lemma]
    (Functor/Hom/Yoneda.v) are stated over
    [C : Category@{u u u}] — object, hom and proof universes IDENTIFIED —
    so nothing built over them can be applied to a category whose objects
    live strictly below its homs.  [yoneda_natural] inherits exactly that,
    and the rejections below are UNIVERSE INCONSISTENCIES: the term is not
    formable at all, not merely non-convertible.  The two bifunctors
    [YoEval] and [YoNat] — and [YoEvalAt] — are over [Category@{u u0 u0}]
    with the object universe FREE below the hom universe (measured: their
    constraint sets carry [u <= u0] and no [u = u0]), and all three ARE
    formable there; so is the THEOREM'S OWN TYPE, [YoNat C ≅ YoEval C],
    which an audit checked elaborates in this very section — so the
    rejection is attributable to the donor TERM, not to the statement or to
    the [Isomorphism]-in-[[X, Sets]] packaging.  So is an identity
    isomorphism between the bifunctors in
    the very functor category the theorem lives in, which is what makes the
    rejection attributable to the donor rather than to the packaging.  The
    boundary runs exactly where [Covariant_Yoneda_Lemma] is consumed:
    [YoEvalAt] does not consume it and is free, while
    [YoEvalAt_Representable] does and carries [u = u0].

    (2) CONVERSION.  Four claims of Leibniz equality are rejected because
    the two sides carry different opaque proof terms, while the corresponding
    claims one or two applications further in DO hold.  These are [Fail
    Definition ... := eq_refl] and not [Fail Example ... : T.]: a failing
    type ascription would guard only the statement, whereas what is claimed
    is convertibility of the two terms.

    COUNTS.  Eight negatives — four in each group — and seven positive
    controls, which is not a one-to-one pairing: the four controls of group
    (1) serve all four of its negatives jointly, and in group (2) the [to]
    control serves two negatives.  Every negative is accompanied by at least
    one control that must SUCCEED.  The instrument itself was checked —
    wrapping [Fail] around a succeeding command reports "The command has not
    failed!" and aborts compilation — and every negative was compiled once
    with the [Fail] stripped, to confirm the error is the intended one: four
    reports of "universe inconsistency: Cannot enforce uh = uo because
    uo < uh" naming the declared universes for group (1), and four "cannot
    unify" conversion errors for group (2).  The import list is the target
    file's own, in the target file's order, plus the target file itself.

--------
* 用于双变量Yoneda同构的边界探针

Functor/Hom/Yoneda/Natural.v 的配套文件（问题 #316；Mac Lane §III.2 引理 2，Riehl §2.2 和 §E.1，Awodey §8.3 引理 8.2）。该文件对两种不同类型的强度进行了声明，而这个文件解决了两者。**如果下面的 [Fail] 命令不再失败，这个文件会导致构建失败。**

这两种类型不同，不可以用一个词来描述。

(1) 可构造性。[Covariant_Yoneda_Lemma] 和 [Yoneda_Lemma]（Functor/Hom/Yoneda.v）是基于 [C : Category@{u u u}] — 对象、Hom 和证明宇宙已被识别 — 声明的 — 因此，基于它们构建的任何东西都不能应用于其对象严格低于其 Hom 的范畴。[yoneda_natural] 正是继承了这一点，下面的拒绝是宇宙不一致性：该项根本无法构造，而不仅仅是不可转换。
两个双函子 [YoEval] 和 [YoNat] —— 以及 [YoEvalAt] —— 是在 [Category@{u u0 u0}] 上的，其对象宇宙在同态宇宙之下（衡量方式：它们的约束集合携带 [u <= u0] 而不携带 [u = u0]），并且三者都可以在那里形成；定理自身的类型 [YoNat C ≅ YoEval C] 也是如此，一个审核检查表明其在本节中确实得到了展开 —— 因此拒绝应归因于供体项而非陈述或 [Isomorphism]-in-[[X, Sets] 包装。同样，一个在定理所在函子范畴中的双函子之间的恒等同构也是如此，这使得拒绝归因于供体而不是包装。边界正好位于 [Covariant_Yoneda_Lemma] 被消耗的地方：[YoEvalAt] 不消耗它并且是自由的，而 [YoEvalAt_Representable] 会消耗它并携带 [u = u0]。

(2) 转换。莱布尼茨等式的四个声明被拒绝，因为双方包含不同的不透明证明项，而在 DO 中相应的一两个应用后这些声明是成立的。这些是 [Fail Definition ... := eq_refl] 和 not [Fail Example ... : T.]：失败的类型标注只会保护语句，而声明的是两个项的可转换性。

计数。八个阴性样本——每组四个——以及七个阳性对照，这不是一对一配对：第一组的四个对照共同用于其四个阴性样本，而在第二组中，[to] 对照用于两个阴性样本。每个阴性样本都至少伴随一个必须成功的对照。仪器本身也经过检查——将 [Fail] 包裹在成功命令周围会报告“命令未失败！”并中止编译——每个阴性样本也都在去掉 [Fail] 后编译一次，以确认错误是预期的：第一组四个报告为“宇宙不一致：无法强制 uh = uo，因为 uo < uh”并标明声明的宇宙，第二组四个报告“无法统一”的转换错误。导入列表是目标文件自身的列表，按目标文件的顺序，加上目标文件本身。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sheaf.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Natural.

Generalizable All Variables.

(**
** (1) The inherited universe restriction

    A category whose object universe is declared STRICTLY BELOW its hom
    universe.  The two bifunctors reach it; the theorem does not.

--------
** (1) 继承的宇宙限制

    一个类别，其对象宇宙被声明严格低于其同态宇宙。两个双函子能够到达它；定理则不能。
*)

Section ObjectsBelowHoms.

Universes uo uh.
Constraint uo < uh.

Context (C : Category@{uo uh uh}).

(*
Positive controls: both bifunctors are formable here, and so is the
   partially applied evaluation functor...

--------
阳性对照：这里两个双函子都是可形成的，部分应用的评估函子也是如此……
*)
Check (YoEval C).
Check (YoNat C).
Check (fun c : C => @YoEvalAt C c).

(*
...and so is an isomorphism between them in the functor category the
   theorem is stated in, so the packaging is not what is rejected.

--------
...因此在所陈述定理的函子范畴中，它们之间也存在同构，所以被拒绝的不是封装方式。
*)
Definition probe_iso_id_control :
  @Isomorphism ([([C, Sets] ∏ C), Sets]) (YoEval C) (YoEval C) := iso_id.

(* Negative 1: the theorem itself is not formable at this category. / 否定 1：该定理本身在此类别中不可形成。 *)
Fail Check (yoneda_natural C).

(*
Negatives 2 and 3: neither is its donor, in either variance — so the
   restriction is inherited and not introduced by this development.

--------
否定词 2 和 3：它们都不是其给体，在任何变体中都是如此——因此这一限制是继承的，而不是由此发展引入的。
*)
Fail Check (fun (F : C ⟶ Sets) (A : C) => Covariant_Yoneda_Lemma C F A).
Fail Check (fun (F : C^op ⟶ Sets) (A : C) => Yoneda_Lemma C F A).

(*
Negative 4: the representability instance is restricted too, though the
   functor it represents is not — the boundary runs exactly where
   [Covariant_Yoneda_Lemma] is consumed, and [YoEvalAt] above does not
   consume it.

--------
负数 4：可表示性实例也受到限制，尽管它所表示的函子没有受到限制——边界正好在 [Covariant_Yoneda_Lemma] 被使用的地方，而上面的 [YoEvalAt] 并未使用它。
*)
Fail Check (fun c : C => YoEvalAt_Representable C c).

End ObjectsBelowHoms.

(** ** (2) The conversion boundaries / ** (2) 转换边界 *)

Section Conversion.

Context (C : Category).
Context (x y : [C, Sets] ∏ C).
Context (tf : x ~> y).
Context (F : C^op ⟶ Sets).
Context (A : C).
Context (yv : F A).
Context (z : C).
Context (phi : z ~{C}~> A).

(*
Negative 5.  The assembled [YoNat]'s arrow action and the hand-written
   [yo_nat_map] are not the same [SetoidMorphism] RECORD: their
   [proper_morphism] fields are different proof terms, one a fresh
   obligation of the target file and one assembled from [Hom]'s and
   [Swap]'s.  Control: pointwise they ARE the same term.

--------
负 5。组装的 [YoNat] 的箭头操作和手写的 [yo_nat_map] 并不是相同的 [SetoidMorphism] 记录：它们的 [proper_morphism] 字段是不同的证明项，一个是目标文件的新义务，一个是由 [Hom] 和 [Swap] 组装而成的。控制：逐点而言，它们是相同的项。
*)
Fail Definition probe_nat_map_record :
  @fmap _ _ (YoNat C) x y tf = yo_nat_map tf := eq_refl.

Definition probe_nat_map_pointwise_control (a : fobj[YoNat C] x) :
  @fmap _ _ (YoNat C) x y tf a = yo_nat_map tf a := eq_refl.

(*
Negative 6.  The derived contravariant lemma and the in-tree one are not
   the same [Isomorphism] record: all four fields differ as proof terms.
   Control: the forward legs agree once applied.

--------
负6。派生的逆变引理和树内的引理不是相同的[Isomorphism]记录：作为证明项，所有四个字段都不同。控制：一旦应用，前向部分是一致的。
*)
Fail Definition probe_derived_iso_record :
  Yoneda_Lemma_derived C F A = Yoneda_Lemma C F A := eq_refl.

Definition probe_derived_to_control (w : Presheaves [Hom ─,A] F) :
  to (Yoneda_Lemma_derived C F A) w = to (Yoneda_Lemma C F A) w := eq_refl.

(*
Negative 7.  Nor are the two forward MORPHISMS equal as records, though
   they agree on every argument — the [proper_morphism] fields differ.

--------
负7。尽管在每个参数上它们都一致——[proper_morphism] 字段不同，但这两个前向形态态射作为记录并不相等。
*)
Fail Definition probe_derived_to_record :
  to (Yoneda_Lemma_derived C F A) = to (Yoneda_Lemma C F A) := eq_refl.

(*
Negative 8.  The backward legs do not even agree on an argument: the
   VALUE is a whole [Transform] record whose [naturality] and
   [naturality_sym] fields are different opaque constants.  Control: the
   agreement holds one level further in, at the components.

--------
负 8。后腿甚至无法在一个论点上达成一致：VALUE 是一个完整的 [Transform] 记录，其 [naturality] 和 [naturality_sym] 字段是不同的不透明常量。控制：一致性在更深一级的组件上仍然成立。
*)
Fail Definition probe_derived_from_value :
  from (Yoneda_Lemma_derived C F A) yv = from (Yoneda_Lemma C F A) yv
  := eq_refl.

Definition probe_derived_from_component_control :
  transform[from (Yoneda_Lemma_derived C F A) yv] z phi
    = transform[from (Yoneda_Lemma C F A) yv] z phi := eq_refl.

End Conversion.
