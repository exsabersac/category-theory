(**
* Boundary probes for Instance/Cat/Pullback.v (issue #337)

    Mac Lane CWM 2nd ed. §III.5 Exercise 3, book p. 74.

    The target proves that the fibre product of categories IS a pullback in
    [StrictCat] under [ObjUIP C], that the same hypothesis is NECESSARY, and
    that the fibre product is NOT a pullback in [Cat].  Three of its four
    measured boundaries are pinned here; the fourth, the universe one, is
    pinned here BECAUSE it cannot be pinned in the target: stating it needs
    a section that declares three object universes strictly apart, and a
    [Constraint] declaration inside the target would constrain the whole
    file rather than one probe.

    FOUR NEGATIVES OF THREE KINDS, kept lexically apart:

      * Negative 1 is FORMABILITY (a universe inconsistency).  It does more
        than record that [FibreProduct_IsPullback] identifies the three
        object universes -- its positive control shows [FibreProduct]
        ITSELF is formable at three universes declared strictly apart, so
        the identification is the [IsPullback] PACKAGING's and not the
        construction's.  Stripped, the error names the declared levels
        (this one, and only this one, is legible from the message TAIL):
          universe inconsistency: Cannot enforce co = ao
          because ao < bo < co.

      * Negatives 2 and 3 are CONVERSION ("cannot unify"), and they differ
        in CAUSE.  Negative 2 fails only in the LAW fields -- its two
        controls show the object and arrow actions of [FP_fst ◯ FP_med]
        agree with [q1]'s at [eq_refl], so what does not convert is the
        three rebuilt proofs.  Negative 3 fails in the DATA: the slice
        stores an arrow where the fibre product stores a pair carrying an
        equality proof, so these are different categories that happen to be
        pullbacks of one cospan.

      * Negative 4 is TYPING, and its marker is "cannot satisfy constraint"
        -- which sits MID-MESSAGE, the tail ending in a "cannot unify" that
        would misread as CONVERSION, so this kind must be read off the
        whole error rather than off its tail.  It is the
        content of [IB_FibreProduct_empty] made checkable at the term
        level: no object of [FibreProduct IBtrue IBfalse] can be written,
        while the control writes one at the AGREEING cospan, so the failure
        is the cospan's and not the fibre product's.

    Every negative is paired with a positive control naming its own
    constants.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others.

--------
* Instance/Cat/Pullback.v 的边界探针（问题 #337）

Mac Lane 《CWM》第2版 §III.5 练习3，第74页。

目标证明了类别的纤维积在 [StrictCat] 下的 [ObjUIP C] 中是一个拉回图，说明了相同的假设是必要的，并且纤维积在 [Cat] 中不是一个拉回图。它的四个测量边界中有三个在这里固定；第四个，即宇宙边界，在这里固定是因为它无法在目标中固定：说明它需要一个声明三个对象宇宙严格分开的节，并且目标内的 [Constraint] 声明会约束整个文件，而不是单个探针。

三类的四个否定，按词汇分开保存：

* 负 1 是可形成性（宇宙不一致性）。它不仅记录了 [FibreProduct_IsPullback] 识别三个对象宇宙的情况——它的正面控制显示 [FibreProduct] 本身可以在严格分开的三个宇宙中形成，因此识别的是 [IsPullback] 打包的，而不是构造的。剥离后，错误指明了声明的层级（只有这一层级可以从消息尾部读取）：
  宇宙不一致性：无法强制 co = ao
  因为 ao < bo < co。

* 否定 2 和 3 是转换（"无法统一"），并且它们在原因上不同。否定 2 仅在法则字段中失败——它的两个控制显示 [FP_fst ◯ FP_med] 的对象和箭头动作与 [q1] 在 [eq_refl] 的动作一致，因此不能转换的是三个重建的证明。否定 3 在数据上失败：切片存储了一个箭头，而纤维积存储了一对携带等式证明的元素，所以这些是不同的范畴，它们碰巧是同一跨度的拉回。

* 负四是 TYPING，其标记为“无法满足约束”——它位于消息中间，其尾部以“无法统一”结束，可能被误读为 CONVERSION，因此这种类型必须从整个错误中读取，而不是从其尾部读取。它是 [IB_FibreProduct_empty] 的内容，在项级上可检查：不能写入 [FibreProduct IBtrue IBfalse] 的任何对象，而控制会在匹配的余割上写入一个，因此失败是余割的，而不是纤维积的。

每个阴性样本都配有一个阳性对照，其命名自己的常数。测得的重命名-模拟得分在最后，覆盖阴性样本命名的常数，而不是其他的常数。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Category.Monoid.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Construction.Slice.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Cat.Pullback.

Generalizable All Variables.

(**
** Instrument check

    A [Fail] that never fails would make every negative below vacuous.

--------
** 仪器检查

    一个永不失败的 [Fail] 会使下面的每个负面都变得无效。
*)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(**
** Negative 1 (FORMABILITY): the universe identification is the
       PACKAGING's, not the construction's

    [FibreProduct] carries bounds only.  [FibreProduct_IsPullback] displays
    three separate category binders, but its constraint block contains
    [u = u1], [u = u3], [u0 = u2] and [u0 = u4] -- all three object
    universes identified, and all three hom-and-proof universes too.  The
    control and the negative differ in nothing but which of the two is
    asked for at the same three levels.

--------
** 负 1（可形成性）：宇宙识别属于包装，而不是构造

[FibreProduct] 仅携带界限。[FibreProduct_IsPullback] 显示三个独立类别的绑定器，但其约束块包含 [u = u1]、[u = u3]、[u0 = u2] 和 [u0 = u4] —— 所有三个对象宇宙已识别，并且所有三个同源及证明宇宙也已识别。控制和负项之间的唯一区别仅在于在相同的三个级别上请求的是哪一个。
*)

Section UniverseBoundary.

Universe ao bo co h.
Constraint ao < bo.
Constraint bo < co.

(*
Control: the construction is formable with the three object universes
   declared strictly apart.

--------
控制：该结构可以在严格分开的三个对象宇宙中形成。
*)
Check (fun (A : Category@{ao h h}) (B : Category@{bo h h})
           (C : Category@{co h h}) (F : A ⟶ C) (G : B ⟶ C) =>
         FibreProduct F G).

(* Control: so are both projections, at the same three levels. / 控制：所以两个投影都在相同的三个层次上。 *)
Check (fun (A : Category@{ao h h}) (B : Category@{bo h h})
           (C : Category@{co h h}) (F : A ⟶ C) (G : B ⟶ C) =>
         (FP_fst F G, FP_snd F G)).

(* Control: so is the hypothesis. / 对照：假设也是如此。 *)
Check (fun (C : Category@{co h h}) => ObjUIP C).

(* NEGATIVE 1. / 否定 1. *)
Fail Check (fun (A : Category@{ao h h}) (B : Category@{bo h h})
                (C : Category@{co h h}) (F : A ⟶ C) (G : B ⟶ C)
                (uip : ObjUIP C) =>
              FibreProduct_IsPullback F G uip).

End UniverseBoundary.

(**
** Negative 2 (CONVERSION): the first triangle holds in the data and
       fails in the laws

    [FP_med_fst] is proved with an [eq_refl] object component and a
    [reflexivity] arrow half.  That is exactly as far as conversion goes:
    the two controls below close by [eq_refl], and the whole-record
    equality does not, because [Functor]'s three law fields are rebuilt
    proofs on the two sides.

--------
** 负2（转换）：第一个三角形在数据中成立，但在定律中失败

[FP_med_fst] 已通过 [eq_refl] 对象组件和 [reflexivity] 箭头半段证明。转换到此为止：下面的两个控制通过 [eq_refl] 收敛，而整个记录的相等性不行，因为 [Functor] 的三个定律字段在两边都是重新构建的证明。
*)

Section TriangleData.

Context {A B C Q : Category} (F : A ⟶ C) (G : B ⟶ C).
Context (q1 : Q ⟶ A) (q2 : Q ⟶ B).
Context (Hsq : F ∘[StrictCat] q1 ≈[StrictCat] G ∘[StrictCat] q2).

(* Control: the object action is [q1]'s on the nose. / 控制：对象动作正是 [q1] 的鼻子。 *)
Definition probe_fp_obj (z : Q) :
  fobj[FP_fst F G ◯ FP_med F G q1 q2 Hsq] z = fobj[q1] z := eq_refl.

(* Control: so is the arrow action. / 控制：箭头操作也是如此。 *)
Definition probe_fp_map (z w : Q) (f : z ~> w) :
  fmap[FP_fst F G ◯ FP_med F G q1 q2 Hsq] f = fmap[q1] f := eq_refl.

(* Control: the second triangle's data likewise. / 控制：第二个三角形的数据也是如此。 *)
Definition probe_fp_obj_snd (z : Q) :
  fobj[FP_snd F G ◯ FP_med F G q1 q2 Hsq] z = fobj[q2] z := eq_refl.

(* NEGATIVE 2. / 负 2. *)
Fail Definition probe_fp_record :
  FP_fst F G ◯ FP_med F G q1 q2 Hsq = q1 := eq_refl.

(*
Control: what IS available at that strength, in [StrictCat]'s own
   hom-setoid.

--------
控制：在 [StrictCat] 自己的同类集合中，以该强度可用的是什么。
*)
Check (FP_med_fst F G q1 q2 Hsq).
Check (FP_med_snd F G q1 q2 Hsq).

End TriangleData.

(**
** Negative 3 (CONVERSION): the slice is not the fibre product of its
       own cospan

    Both are pullbacks of [Arrow_cod] along [Diagonal 1 c], so they are
    isomorphic; the target does not build that isomorphism and does not
    claim it.  They are certainly not the same category: an object of the
    slice is an arrow, an object of the fibre product is a pair of objects
    carrying a proof that their images agree.

--------
** 负 3（转换）：slice 不是它自身 cospan 的纤维积

两者都是沿 [Diagonal 1 c] 的 [Arrow_cod] 的拉回，所以它们是同构的；目标对象并没有构建这个同构，也没有声明它。它们当然不是同一个范畴：slice 的一个对象是一个箭头，纤维积的一个对象是一对对象，并携带一个证明它们的像相等。
*)

Section SliceApex.

Context {C : Category} (c : C).

(* Control: the leg's object action, on the nose. / 控制：腿的物体动作，在鼻子上。 *)
Definition probe_slice_obj (x : Slice C c) :
  fobj[Slice_Arrow c] x = ((`1 x, c); `2 x) := eq_refl.

(* NEGATIVE 3. / 负三。 *)
Fail Definition probe_slice_apex :
  Slice C c = FibreProduct (@Arrow_cod C) (@Diagonal C _1 c) := eq_refl.

End SliceApex.

(**
** Negative 4 (TYPING): the refuting cospan has an empty fibre product

    This is [IB_FibreProduct_empty] read at the term level.  The control
    writes an object of the fibre product of the AGREEING cospan with the
    same syntax, so what the negative measures is the cospan and not the
    construction.

--------
** 负4（打字）：反驳的余对列有一个空的纤维积

这是在术语层面上读取的 [IB_FibreProduct_empty]。控制端写入一个与之语法相同的 AGREING 余对列的纤维积对象，因此负面测量的是余对列，而不是构造。
*)

(*
Control: at a cospan whose two legs agree, the pair with [eq_refl] is an
   object.

--------
控制：在两条腿一致的余弦图中，带有 [eq_refl] 的对是一个对象。
*)
Definition probe_ib_agree : obj[FibreProduct IBtrue IBtrue] :=
  ((ttt, ttt); eq_refl).

(* NEGATIVE 4. / 负四 *)
Fail Definition probe_ib_empty : obj[FibreProduct IBtrue IBfalse] :=
  ((ttt, ttt); eq_refl).

(* Control: the same fact, proved rather than probed. / 控制：相同的事实，被证明而非被探查。 *)
Check IB_FibreProduct_empty.
Check IB_iso.

(**
** Positive controls for the headline artifacts

    Every constant the four negatives name appears above; these guard the
    results the file exists for, so that a rename anywhere in it breaks
    this probe loudly.

--------
** 标题工件的阳性对照

每个常数四个否定名称出现在上面；这些保护文件存在的结果，因此文件中的任何重命名都会大声地破坏这个探针。
*)

Check FibreProduct.
Check FP_fst.
Check FP_snd.
Check FP_commutes_strict.
Check FP_commutes_cat.
Check FP_med.
Check FP_med_unique.
Check FibreProduct_IsPullback.
Check FibreProduct_Pullback.
Check ObjUIP_of_ObjDecEq.
Check FibreProduct_IsPullback_dec.
Check StrictCat_HasPullbacks.

(**
The [Cat] side: the candidate is refuted, and the refutation is narrow
    -- the same cospan does have a [Cat] pullback.

--------
[Cat] 方面：候选者被驳斥，并且驳斥很狭窄 —— 相同的余范确实有一个 [Cat] 拔回。
*)

Check FibreProduct_not_Cat_pullback.
Check point_cospan_Cat_IsPullback.
Check point_cospan_square.
Check one_functors_equiv.

(** Necessity of the hypothesis. / 假设的必要性。 *)

Check FP_uniqueness_forces_UIP.
Check loop_functor.
Check loop_functor_fst.
Check loop_functor_snd.

(** The comma half. / 逗号一半。 *)

Check Slice_Arrow.
Check Slice_commutes.
Check Slice_IsPullback.
Check Coslice_Arrow.
Check Coslice_commutes.
Check Coslice_IsPullback.
Check slice_arrow_reflect.
Check coslice_arrow_reflect.

(**
** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

      Negative 1: [FibreProduct_IsPullback], [ObjUIP]
      Negative 2: [FP_fst], [FP_med], [q1] (a section variable, not a
                  constant, so it is not counted)
      Negative 3: [Slice], [FibreProduct], [Arrow_cod], [Diagonal]
      Negative 4: [FibreProduct], [IBtrue], [IBfalse]

    Deduplicated, and with the two stdlib/donor names [Slice] and
    [Diagonal] kept in because both are library constants this file
    depends on, that is [FibreProduct_IsPullback], [ObjUIP],
    [FibreProduct], [FP_fst], [FP_med], [Slice], [Arrow_cod], [Diagonal],
    [IBtrue], [IBfalse] -- TEN, counted rather than recalled.  [Category],
    [obj], [ttt] and [_1] are named by the negatives too and are EXCLUDED,
    on the stated ground that they are core vocabulary named by almost
    every file in the tree, not that they are hard to guard.

    Each is named by a positive control above: [FibreProduct_IsPullback],
    [FibreProduct], [FP_fst] and [FP_med] by the headline block;
    [ObjUIP] by the third control of Negative 1; [Slice] and [Arrow_cod]
    and [Diagonal] by [probe_slice_obj] and by [Check Slice_Arrow] (whose
    type mentions [Slice] and [Arrow]) -- and, to leave nothing to a type
    display, explicitly below; [IBtrue] and [IBfalse] by [probe_ib_agree]
    and [Check IB_FibreProduct_empty].

    Score: 10/10, on an unpadded denominator.

--------
** 测量的重命名模拟分数

NEGATIVES 命名的常数：

负面 1：[FibreProduct_IsPullback]，[ObjUIP]
负面 2：[FP_fst]，[FP_med]，[q1]（一个段变量，不是常量，因此不计入）
负面 3：[Slice]，[FibreProduct]，[Arrow_cod]，[Diagonal]
负面 4：[FibreProduct]，[IBtrue]，[IBfalse]

去重后，并且保留了两个 stdlib/donor 名称 [Slice] 和 [Diagonal]，因为它们都是此文件依赖的库常量，即 [FibreProduct_IsPullback]、[ObjUIP]、[FibreProduct]、[FP_fst]、[FP_med]、[Slice]、[Arrow_cod]、[Diagonal]、[IBtrue]、[IBfalse] —— 十个，数的而不是回忆的。[Category]、[obj]、[ttt] 和 [_1] 也被 negatives 命名，并被排除，理由是它们是核心词汇，几乎每个文件在树中都会命名它们，而不是因为它们难以保护。

每个都由上面的阳性对照命名：[FibreProduct_IsPullback]、[FibreProduct]、[FP_fst] 和 [FP_med] 由标题块命名；[ObjUIP] 由负对照 1 的第三个控制命名；[Slice]、[Arrow_cod] 和 [Diagonal] 由 [probe_slice_obj] 和 [Check Slice_Arrow]（其类型提到 [Slice] 和 [Arrow]）命名——并且，为了不让类型显示遗漏，明确在下面列出；[IBtrue] 和 [IBfalse] 由 [probe_ib_agree] 和 [Check IB_FibreProduct_empty] 命名。

得分：10/10，在未填充的分母上。
*)

Check (fun (C : Category) (c : C) => (@Slice C c, @Arrow_cod C,
                                      @Diagonal C _1 c)).
Check IBtrue.
Check IBfalse.
Check IB.
