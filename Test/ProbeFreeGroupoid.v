(**
* Boundary probe: what is and is not definitional in the free groupoid
      and the free group.

    Companion to Construction/Free/Groupoid.v and Instance/Grp/Free.v
    (Mac Lane §II.7 Ex. 3, Riehl §4.2 Example 4).  Those files make several
    strength claims — some things hold at Leibniz [=] or by [eq_refl], others
    only up to [≈] — and a strength claim that lives only in a header is a
    claim nothing in the build would notice losing.  This file pins the
    boundary in the manner of Test/ProbeQuiverConstructions.v and
    Test/ProbeFunnyPoly.v: **if the [Fail] commands here stop failing, this
    file breaks the build.**

    Both sides are pinned deliberately.  A [Fail] alone proves very little —
    it passes just as happily when the term is ill-typed for some unrelated
    reason, or when a name has been renamed out from under it.  So each
    negative probe is paired with a positive control which must SUCCEED, and
    the controls are the headline claims themselves.

    The instrument was checked before being trusted: wrapping [Fail] around a
    command that succeeds reports "The command has not failed!" and aborts
    compilation, so [Fail] here is not a no-op.  Each negative below was also
    run with the [Fail] stripped, and the error confirmed to be a genuine
    unification or typing failure rather than a syntax, scope or universe
    error; the diagnoses are recorded beside each probe.

    RE-MEASURED after the PR "algebraic carriers are sets" (2026-09-17),
    which made the free GROUP's `≈` the propositional truncation of the free
    GROUPOID's hom-equality (Instance/Grp/Free.v's [fg_equiv]).  The free
    groupoid itself is untouched, and every negative and every control below
    still holds with its text unchanged; the truncation's own boundary is
    pinned separately, in Test/ProbeGrpProp.v.

    The five negatives and their causes:

      - [FreeGroupoid] is not [FreeSigned].  The two share their objects and
        their hom TYPES definitionally — that is [fg_hom_type], the positive
        control, and it is the whole content of "equations merge, and never
        add" — but the [Category] records differ in their [homset] field, so
        the categories are not convertible.  The mathematical form of the
        same fact is [free_signed_not_groupoid].

      - The inverse law holds only up to [≈].  [fginv f ∘ f] is the word
        [f] followed by its reversal, which is not the empty word until the
        cancellation congruence is applied; the positive control is
        [fginv_involutive], which DOES hold at Leibniz [=] because
        [Lib/TList.v]'s [tlist_rev_involutive] does.

      - The counit of the free-group adjunction does not compute.  It is
        [from adj id], i.e. [unique_obj (ump_universal_arrows …)], and
        [ump_universal_arrows] (Theory/Universal/Arrow.v) is [Qed]-opaque, so
        no reduction is available.  The unit is on the other side of that
        boundary and DOES compute, which is the positive control
        [free_group_unit_is_insert].  Instance/Grp/Free.v says so in terms
        and states the counit only up to [≈]
        ([free_group_counit_evaluates]).

      - The generator clause of the universal property is not even WELL-TYPED
        without the object agreement in scope.  Stripped of [Fail] this one
        is a typing error rather than a unification failure: [fedgemap x y e]
        has type [edges (F x) (F y)] while the clause needs
        [fobj[K] x ~> fobj[K] y], and nothing identifies those two until
        [Hobj] is available to [hom_cast] across.  This is why
        [free_groupoid_universal] nests [Hobj] INSIDE the sigma rather than
        stating a flat generator clause beside it — the nesting is forced,
        not stylistic.

      - [Deloop] does not accept an [Instance/Grp.v] group.  There are two
        records named [GrpObject] in the tree — Construction/Deloop.v's,
        layered on [MonObject], and Instance/Grp.v's, flat — and no
        converter between them, which is exactly why Instance/Grp/Free.v
        builds [grp_deloop_monoid] by hand.  The positive control is that
        [grp_deloop] does accept one.

--------
* 边界探针：在自由群范畴和自由群中，什么是定义性的，什么不是定义性的。

Construction/Free/Groupoid.v 和 Instance/Grp/Free.v 的配套文件（Mac Lane §II.7 例 3, Riehl §4.2 例 4）。这些文件提出了多个强度声明 —— 有些事情在 Leibniz [=] 上或通过 [eq_refl] 成立，其他的仅在 [≈] 范围内成立 —— 而仅存在于头文件中的强度声明是构建过程中没有任何东西会注意到丢失的声明。此文件通过 Test/ProbeQuiverConstructions.v 和 Test/ProbeFunnyPoly.v 的方式固定了边界：**如果此处的 [Fail] 命令不再失败，则此文件会破坏构建。**

双方都是故意固定的。单靠 [Fail] 本身几乎无法证明什么——当术语由于某些无关的原因类型错误，或者名称已经被重新命名时，它同样可以顺利通过。因此，每个负向测试都配有一个必须成功的阳性对照，而这些对照本身就是主要的声明。

该仪器在被信任之前进行了检查：将 [Fail] 包裹在一个成功的命令周围会报告“命令未失败！”并中止编译，所以这里的 [Fail] 不是空操作。下面的每个负测试也都在去掉 [Fail] 后运行，并确认错误是真正的归一化或类型错误，而不是语法、作用域或宇宙错误；每个探测的诊断结果都记录在旁边。

在 PR “代数承载是集合”(2026-09-17) 之后重新测量，这使得自由群的 `≈` 成为自由群范畴的同态相等的命题截断 (Instance/Grp/Free.v 的 [fg_equiv])。自由群范畴本身未被修改，下面的每个负号和控制依旧有效且文本保持不变；截断自身的边界在 Test/ProbeGrpProp.v 中单独固定。

五种消极及其原因：

- [FreeGroupoid] 不是 [FreeSigned]。两者在本质上共享它们的对象和它们的 hom 类型——也就是 [fg_hom_type]，正向控制，并且它是“方程合并，从不相加”的全部内容——但是 [Category] 记录在 [homset] 字段上有所不同，因此这些类别不可互换。同一事实的数学形式是 [free_signed_not_groupoid]。

- 逆定律仅适用于 [≈]。[fginv f ∘ f] 是单词 [f] 后跟其反转，直到应用消去合同之前，它不是空单词；正向控制是 [fginv_involutive]，在莱布尼茨 [=] 上成立，因为 [Lib/TList.v] 的 [tlist_rev_involutive] 成立。

- 自由群伴随的余单位无法计算。它是 [from adj id]，即 [unique_obj (ump_universal_arrows …)]，并且 [ump_universal_arrows]（Theory/Universal/Arrow.v）是 [Qed]-不透明的，因此无法进行归约。单位在该边界的另一侧并且可以计算，这是正向控制 [free_group_unit_is_insert]。Instance/Grp/Free.v 从术语的角度说明了这一点，并且指出余单位只能到 [≈]（[free_group_counit_evaluates]）为止。

- 如果没有作用域中的对象一致性，通用性质的生成子子句甚至都不能正确类型化。去掉 [Fail] 后，这实际上是一个类型错误而不是统一失败：[fedgemap x y e] 的类型是 [edges (F x) (F y)]，而该子句需要 [fobj[K] x ~> fobj[K] y，并且在 [Hobj] 对 [hom_cast] 可用之前，没有任何东西能识别这两者。这就是为什么 [free_groupoid_universal] 会将 [Hobj] 嵌套在 sigma 中，而不是在旁边声明一个平面的生成子子句——这种嵌套是被迫的，而不是风格选择。

- [Deloop] 不接受 [Instance/Grp.v] 组。树中有两个名为 [GrpObject] 的记录——Construction/Deloop.v 中的，分层在 [MonObject] 上，以及 Instance/Grp.v 中的，平铺——它们之间没有转换器，这正是 Instance/Grp/Free.v 手动构建 [grp_deloop_monoid] 的原因。正面控制是 [grp_deloop] 确实接受一个。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Free.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.

Local Open Scope category_scope.

#[local] Existing Instance edgeset.

(** ** Positive controls: the definitional claims / ** 阳性对照：定义性主张 *)

(*
The hom TYPES of the free groupoid and of the free category on the signed
   quiver agree on the nose: the quotient coarsens the equivalence and
   nothing else.

--------
自由群族和带符号四元图的自由范畴的 Hom 类型完全一致：商化了等价关系，除此之外没有其他变化。
*)
Example control_hom_type (G : Quiver) (x y : G) :
  (x ~{FreeGroupoid G}~> y) = (x ~{FreeSigned G}~> y) := eq_refl.

(* The chosen inverse of the groupoid structure IS word reversal. / 所选择的群结构的逆元是单词反转。 *)
Example control_ginv_is_reversal (G : Quiver) (x y : G)
  (f : x ~{FreeGroupoid G}~> y) :
  ginv (FreeGroupoid_IsGroupoid G) f = fginv f := eq_refl.

(* Reversal is involutive at Leibniz [=], before any quotient. / 在 Leibniz [=] 上，反转是自反的，在任何商之前。 *)
Check (fun (G : Quiver) (x y : G) (f : x ~{FreeGroupoid G}~> y) =>
         fginv_involutive f : fginv (fginv f) = f).

(*
The generator clause of the universal property typechecks once the object
   agreement [Hobj] is in scope, and is then conjugated by [hom_cast].

--------
一旦对象一致性 [Hobj] 在范围内，泛型性质的生成器条款就会进行类型检查，然后由 [hom_cast] 进行配合变位。
*)
Check (∀ (G : Quiver) (D : Category)
         (F : QuiverHomomorphism G (QuiverOfCat D))
         (K : FreeGroupoid G ⟶ D)
         (Hobj : ∀ x : G, fobj[K] x = @fnodes _ _ F x)
         (x y : G) (e : edges x y),
       hom_cast (Hobj x) (Hobj y) (fmap[K] (fgpos e))
         ≈ @fedgemap _ _ F x y e).

(* The free functor's object part is the word group, definitionally. / The free functor's object part is the word group, definitionally. / 自由函子的对象部分从定义上来说就是单词组。 *)
Example control_FreeGrp_obj (X : Sets) : FreeGrp X = FreeGrpObject X
  := eq_refl.

(* The unit of the adjunction computes to the one-letter word. / 伴随的单位计算为一个字母的单词。 *)
Example control_unit_computes (X : Sets) (a : carrier X) :
  free_group_unit X a = fg_insert X a := eq_refl.

(* [Deloop] accepts an [Instance/Grp.v] group only through the bridge. / [Deloop] 仅通过桥接接受 [Instance/Grp.v] 组。 *)
Check (fun H : GrpObject => grp_deloop H).

(** ** Negative probes: these commands MUST fail / ** 负面探测：这些命令必须失败 *)

(*
The free groupoid is not the free category on the signed quiver: the
   [homset] fields differ.  (Stripped of [Fail]: "cannot unify".)

--------
自由群oid不是带符号的quiver上的自由范畴：[homset]字段不同。（去掉[Fail]："无法统一"。）
*)
Fail Example probe_groupoid_is_free_category (G : Quiver) :
  FreeGroupoid G = FreeSigned G := eq_refl.

(*
The inverse law is not definitional.  (Stripped of [Fail]: "Unable to
   unify ... with ...".)

--------
逆律不是定义性的。（去掉 [Fail]："无法将...与...统一"。）
*)
Fail Example probe_inverse_definitional (G : Quiver) (x y : G)
  (f : x ~{FreeGroupoid G}~> y) :
  @compose (FreeGroupoid G) x y x (fginv f) f = @id (FreeGroupoid G) x
  := eq_refl.

(*
The counit does not compute.  (Stripped of [Fail]: "cannot unify",
   the offending head being the opaque [ump_universal_arrows].)

--------
余单位无法计算。（去掉 [Fail]："无法统一"，出错的头是不透明的 [ump_universal_arrows]。）
*)
Fail Example probe_counit_computes (H : Grp) (w : FGWord (Grp_Forget H)) :
  free_group_counit H w = free_grp_extend (@id Sets (Grp_Forget H)) w
  := eq_refl.

(*
The generator clause of the universal property is not even well-typed
   without the object agreement in scope — this is why the bundled
   [free_groupoid_universal] nests [Hobj] inside the sigma.  (Stripped of
   [Fail]: a typing error on the two sides of [≈].)

--------
没有作用域内的对象一致性，泛性质的生成子条款甚至都无法正确类型化——这就是为什么捆绑的 [free_groupoid_universal] 会将 [Hobj] 嵌套在 sigma 内部。（去掉 [Fail]：[≈] 两边的一个类型错误。）
*)
Fail Check (∀ (G : Quiver) (D : Category)
              (F : QuiverHomomorphism G (QuiverOfCat D))
              (K : FreeGroupoid G ⟶ D)
              (x y : G) (e : edges x y),
            fmap[K] (fgpos e) ≈ @fedgemap _ _ F x y e).

(*
[Deloop] does not accept an [Instance/Grp.v] group directly: it wants a
   [MonObject], and there is no coercion.  (Stripped of [Fail]: "The term
   ... has type GrpObject while it is expected to have type MonObject".)

--------
[Deloop] 不直接接受 [Instance/Grp.v] 组：它需要一个 [MonObject]，并且没有强制转换。（去掉 [Fail]："该术语的类型是 GrpObject，而预期类型是 MonObject"。）
*)
Fail Check (fun H : GrpObject => Deloop H).
