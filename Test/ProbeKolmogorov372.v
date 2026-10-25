(**
* Boundary probe for Instance/Top/Kolmogorov.v (issue #372, part b)

    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    §IV.3, printed p. 92, Exercise 4(b).

    Every rejection the target's header MEASURES is pinned here rather
    than in the target itself, for the reason this tree records
    elsewhere: an in-file [Fail] renames in lockstep with the constant
    it guards, so it cannot detect a rename.  This file mirrors the
    target's FULL [Require] list plus the target -- a short prefix is
    what makes a probe pass for a reason it never measured.

    SEVEN [Fail] commands: SIX negatives of THREE KINDS kept lexically
    apart, plus one scope-free instrument check.

      - CONVERSION (3): each reports "cannot unify" between two terms
        of ONE type.
      - TYPING (1): a plain "has type ... while it is expected to have
        type ...", with NO "cannot unify" and no universe clause.
      - FORMABILITY (2): each ends "universe inconsistency: Cannot
        enforce ...".  The first is this development's own headline
        measurement -- the unrestricted indistinguishability relation
        is one universe too big to be a space's `≈`; the second is the
        donor identification [Subcategory] carries.

    CORRECTION (#1347): CONVERSION 1 below now holds at [eq_refl], since
    Instance/Sets.v gives its identity's and composite's properness fields
    as terms; it is a control, so the refutations are SIX, FIVE negatives
    and the instrument, CONVERSION counting 2.

    Each negative was stripped ONE AT A TIME (the others left as
    [Fail]), compiled alone, and its WHOLE error read; a [Fail] that
    succeeds prints NOTHING under this coqc, which is why stripping is
    the only way to see what fired.  Every constant a negative names is
    also named OUTSIDE a [Fail] below, so that renaming any of them
    breaks this file at a control rather than turning a guard silently
    green.
    CORRECTION (#1347): the five negatives that remain, stripped one at a
    time in copies of the WHOLE file, stop inside their commands with the
    errors they printed before #1347 (compared by script); CONVERSION 1,
    wrapped in the refutation keyword in such a copy, stops the build at
    that command.

--------
* 针对实例/Top/Kolmogorov.v 的边界探测（问题 #372，第 b 部分）

Mac Lane，《为作业数学家准备的范畴》，第2版，第IV.3节，印刷第92页，练习4(b)。

每一次对目标头部 MEASURES 的拒绝都固定在这里，而不是在目标本身，因为这个树在其他地方记录的原因：文件内的 [Fail] 与它所保护的常量同步重命名，所以它无法检测重命名。该文件镜像了目标的完整 [Require] 列表以及目标本身 —— 一个短前缀就是使一次探测通过而达到它从未测量过的原因。

SEVEN [Fail] 命令：三种类型的六个否定在词汇上保持分离，再加一个无作用域的仪器检查。

- 转换 (3)：每条报告“无法统一”在同一类型的两个项之间。
- 类型检测 (1)：一个简单的“具有类型...而预期类型是...”，没有“无法统一”也没有宇宙条款。
- 形成性 (2)：每条以“宇宙不一致：无法强制...”结束。第一条是本开发的自身主要测量——不受限制的不可区分关系比一个空间的 `≈` 大一个宇宙；第二条是捐赠者识别 [Subcategory] 的内容。

更正（#1347）：下面的转换1现在在[eq_refl]中成立，因为Instance/Sets.v将其身份和复合的适当性字段作为项给出；它是一个控制，因此反驳为SIX、FIVE个否定和工具，转换计为2。

每个否定项都是一次剥离一个（其他保留为[Fail]），单独编译，并读取其完整错误；在此coqc下成功的[Fail]不会打印任何内容，这就是为什么剥离是查看触发原因的唯一方法。每个否定项命名的常量也在下面的[Fail]之外被命名，因此重命名它们中的任何一个会让这个文件在某个控制处出错，而不是悄悄地将保护变为绿色。
修正 (#1347)：剩下的五个否定项，在整个文件副本中一次剥离一个，会在其命令内部停止，并显示在#1347之前打印的错误（通过脚本对比）；在这样的副本中，用反驳关键字包裹的转换1，会在该命令处停止构建。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Kolmogorov.

(**
** Instrument check

    Scope-free: it names nothing, so it stays red however the target is
    renamed, and it shows [Fail] is doing its job in this file.

--------
** 工具检查

    无范围：它不命名任何东西，所以无论目标如何被重命名，它都保持红色，并且它显示 [Fail] 正在这个文件中执行其工作。
*)

Fail Check probe_372b_no_such_reference.

(**
** FORMABILITY 1 -- the headline: the unrestricted relation is one
       universe too big to be a space's `≈`

    [TopSpace@{o}] carries [top_carrier :> SetoidObject@{o o}], so a
    space's own `≈` is valued in [Type@{o}], while [IsOpen] quantifies
    over predicates [X → Type@{o}] and so a relation quantifying over
    ALL of them lands at a level strictly above [o].  The control shows the
    level-restricted [SameOpens] DOES land at [Type@{o}] at the very
    same declared levels, and [kq_setoid] builds the coarsened
    [SetoidObject] out of it; the negative shows [SameOpensAll] does
    not.  That is the whole reason the target's quotient tests against
    the opens valued at a level strictly below the space's own.

--------
** 可形性 1 -- 标题：非受限关系是一个宇宙，太大而无法成为某空间的 `≈`

[TopSpace@{o}] 携带 [top_carrier :> SetoidObject@{o o}]，因此某空间自身的 `≈` 在 [Type@{o}] 中被估值，而 [IsOpen] 对谓词 [X → Type@{o}] 进行量化，因此对其进行量化的关系落在严格高于 [o] 的层级上。控制显示，层级受限的 [SameOpens] 确实在完全相同的声明层级下落在 [Type@{o}]，而 [kq_setoid] 从中构建了粗化的 [SetoidObject]；否定情况表明 [SameOpensAll] 不会这样。也就是说，目标的商对空间自身以下严格层级的开集进行测试，这就是全部原因。
*)

Section ProbeKolmogorovLevels.

Universes s o.
Constraint s < o.

Context (Xu : TopSpace@{o}).

Definition k372_probe_small_at_o (x y : Xu) : Type@{o} :=
  SameOpens@{s o} Xu x y.

Definition k372_probe_kq_setoid_at_o : SetoidObject@{o o} :=
  kq_setoid@{s o} Xu.

Fail Definition k372_probe_all_at_o (x y : Xu) : Type@{o} :=
  SameOpensAll Xu x y.

End ProbeKolmogorovLevels.

(**
** FORMABILITY 2 -- the donor identifies hom with proof

    [Subcategory] is declared over [Category@{u u0 u0}].  At a category
    whose hom and proof universes are declared strictly apart, naming a
    hom-set and an identity is fine while [Subcategory] is refused.
    The identification is the DONOR's and is inherited by
    [T0_Subcategory], [T0Spaces] and [T0_Reflective_in_Top]; nothing in
    the target adds to it, and no constraint block of any constant of
    the target carries a universe equation at all.

    Only ONE such negative is stated.  [Reflective] takes a
    [Subcategory] and cannot be tested apart from it, so a negative
    naming [Reflective] would fire at its [Subcategory] argument with
    the identical message and separate nothing (the trap
    Test/ProbeRingLattice340.v records for [MonoidObject]).

--------
** 可塑性 2 -- 供体使用证明识别同态

[Subcategory] 被声明在 [Category@{u u0 u0}] 上。在一个其同态和证明宇宙严格分开的范畴中，命名一个同态集和一个恒等式是可以的，而 [Subcategory] 被拒绝。这个识别属于供体，并被 [T0_Subcategory]、[T0Spaces] 和 [T0_Reflective_in_Top] 继承；目标中没有任何内容对此有所增加，并且目标中任何常量的约束块都不携带宇宙方程。

只陈述了一个这样的负面情况。[Reflective] 接受一个 [Subcategory] 并且无法与其分开测试，因此命名 [Reflective] 的负面将在其 [Subcategory] 参数上触发，给出相同的信息且不产生任何分离（Test/ProbeRingLattice340.v 的陷阱记录了 [MonoidObject]）。
*)

Section ProbeKolmogorovDonor.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).
Context (xu yu : obj[Cu]).

Check (xu ~{Cu}~> yu).
Check (@id Cu xu).

Fail Check (@Subcategory Cu).

End ProbeKolmogorovDonor.

(**
** CONVERSION 1 -- the unit is the projection POINTWISE, not as a
       morphism record

    [AdjunctionFromUniversalArrows] builds the forward transpose as
    [fun g => fmap[U] g ∘ arrow], so the class unit is
    [fmap[Incl] id ∘ kolmogorov_proj X].  Applied to a POINT that
    composite reduces to the point itself, which is the target's
    [t0_unit_is_proj]; as a whole [ContinuousMorphism] record it does
    not, and the `≈` form is the target's [t0_unit_is_proj_hom].
    CORRECTION (#1347): as a whole record it does now: the command below
    holds at [eq_refl], since Instance/Sets.v gives its identity's and
    composite's properness fields as terms, and is a control.  That it
    does not was argued; the measurement shows the residue was the
    standard library's, the opaque lemmas instance resolution had put in the two
    properness fields, the identity's and the composite's.

--------
** 换算1——单位是按点投影，而不是作为
       态射记录

    [AdjunctionFromUniversalArrows] 将前移调构建为
    [fun g => fmap[U] g ∘ 箭头]，因此类单位为
    [fmap[Incl] id ∘ kolmogorov_proj X]。应用于一个点
    复合还原到目标的点本身
    [t0_unit_is_proj];作为一张[ContinuousMorphism]专辑，它确实如此
    不是，而“≈”形式是目标的[t0_unit_is_proj_hom]。
    更正（#1347）：作为整体记录，现在是：下面的命令
    在 [eq_refl] 成立，因为 Instance/Sets.v 给出了其恒时元 和
    复合的适当场作为项，是控制。就是这样
    不存在的观点被争论;测量显示残余为
    标准库的不透明度引理实例解析在两者中设置了
    固有域、单位元和复合体。
*)

Example k372_probe_unit_is_proj_strict (X : TopSpace) :
  t0_unit X = kolmogorov_proj X := eq_refl.

Example k372_probe_unit_is_proj_pointwise (X : TopSpace) (x : X) :
  continuous_map (t0_unit X) x
    = continuous_map (kolmogorov_proj X) x := eq_refl.

Lemma k372_probe_unit_is_proj_hom (X : TopSpace) :
  t0_unit X ≈ kolmogorov_proj X.
Proof. apply t0_unit_is_proj_hom. Qed.

(**
** CONVERSION 2 -- the quotient's opens are NOT the base space's

    [KolmogorovQuotient X] keeps X's carrier ([kq_carrier_strict]) and
    coarsens its `≈` to [SameOpens X] ([kq_equiv_strict]), but its
    opens are the pairs of an open of X with a proof that the open
    respects that relation -- which is [kq_open], and is what makes
    [open_proper] available for the coarser `≈`.  So the two [IsOpen]
    fields are different terms.  The one-directional passage is the
    target's [small_open_is_kq_open].

--------
** 转换 2 -- 商的开集不是基础空间的开集

[KolmogorovQuotient X] 保持 X 的承载（[kq_carrier_strict]）并将其 `≈` 粗化为 [SameOpens X]（[kq_equiv_strict]），但它的开集是 X 的开集与一个证明该开集遵守该关系的证明的对儿——即 [kq_open]，这也是使 [open_proper] 可用于较粗 `≈` 的原因。因此，这两个 [IsOpen] 字段是不同的项。单向传递是目标的 [small_open_is_kq_open]。
*)

Fail Example k372_probe_kq_isopen_strict (X : TopSpace) (U : X → Type) :
  IsOpen (KolmogorovQuotient X) U = IsOpen X U := eq_refl.

Example k372_probe_kq_isopen_is_kq_open (X : TopSpace) (U : X → Type) :
  IsOpen (KolmogorovQuotient X) U = kq_open X U := eq_refl.

Example k372_probe_kq_carrier (X : TopSpace) :
  carrier (top_carrier (KolmogorovQuotient X))
    = carrier (top_carrier X) := eq_refl.

(**
** CONVERSION 3 -- a T0 space is not EQUAL to its own quotient

    [Bool_Discrete] is T0, so the reflector returns it up to
    isomorphism ([bool_reflect_iso], the counit isomorphism
    instantiated).  The two spaces are nevertheless distinct:
    [Discrete_Top]'s opens are the `≈`-respecting predicates and the
    quotient's are the respecting ones in the sense above, and the
    setoid field and every law field are separately built.

--------
** 转换 3 —— 一个 T0 空间不等于它自己的商空间

[Bool_Discrete] 是 T0，因此反射器返回它到同构（[bool_reflect_iso]，余单位同构被实例化）。然而，这两个空间仍然是不同的：[Discrete_Top] 的开集是“≈”兼容的谓词，而商空间的开集是上述意义下兼容的谓词，并且集合域和每一个律域都是单独构建的。
*)

Fail Example k372_probe_quot_bool_strict :
  KolmogorovQuotient Bool_Discrete = Bool_Discrete := eq_refl.

Definition k372_probe_bool_iso :
  fobj[T0_reflector] (Incl Top T0_Subcategory Bool_Discrete_T0Space)
    ≅[T0Spaces] Bool_Discrete_T0Space := bool_reflect_iso.

(**
** TYPING -- [Reflective] is a record, not an adjunction

    Mac Lane's phrase "full reflective subcategory" is the RECORD:
    fullness, a reflector, and the adjunction.  The adjunction alone is
    strictly less, and the mismatch is a plain typing error -- no
    "cannot unify", no universe clause.

--------
** 输入 -- [Reflective] 是一个记录，而不是一个伴随

    麦克·莱恩的短语“完全反射子范畴”是记录：
    完整性、一个反射子，以及伴随。仅有伴随严格来说较少，而不匹配是一个明显的类型错误——没有“无法统一”，没有宇宙条款。
*)

Fail Definition k372_probe_reflective_is_adjunction
  : T0_reflector ⊣ Incl Top T0_Subcategory :=
  T0_Reflective_in_Top.

Definition k372_probe_reflective_adj
  : T0_reflector ⊣ Incl Top T0_Subcategory :=
  reflective_adj T0_Reflective_in_Top.

Definition k372_probe_reflective_record : Reflective T0_Subcategory :=
  T0_Reflective_in_Top.

Definition k372_probe_reflective_full :
  Category.Construction.Subcategory.Full Top T0_Subcategory :=
  reflective_full T0_Reflective_in_Top.

(** ** Controls naming every constant the negatives mention / ** 控制命名每一个负面提到的常量 *)

Check @SameOpens.
Check @SameOpensAll.
Check @SameOpensAll_SameOpens.
Check @IsT0.
Check @kq_setoid.
Check @kq_open.
Check @small_open_is_kq_open.
Check @KolmogorovQuotient.
Check @KolmogorovQuotient_T0.
Check @KolmogorovT0.
Check @kolmogorov_proj.
Check @kolmogorov_med.
Check @kolmogorov_universal.
Check @kolmogorov_universal_arrow.
Check @t0_unit.
Check @t0_unit_is_proj_hom.
Check @t0_reflect_iso.
Check @T0_reflector.
Check @T0_adj.
Check @T0_Subcategory.
Check @T0Spaces.
Check @T0_Full.
Check @T0_Incl_Full.
Check @T0_Incl_Faithful.
Check @T0_Reflective_in_Top.
Check @Bool_Discrete_T0.
Check @Bool_Discrete_T0Space.
Check @bool_reflect_iso.
Check @TwoPoint_Indiscrete_not_T0.
Check @Hausdorff_T0_nn.
Check @Tri_Top.
Check @Tri_Top_not_T0.
Check @tri_point_apart.
Check @tri_quot_keeps_point_apart.
Check @Tri_T0.
Check @Subcategory.
Check @Reflective.
Check @Sub.
Check @Incl.
Check @Top.
Check @TopSpace.
Check @IsOpen.
Check @Bool_Discrete.
Check @continuous_map.
Check @carrier.
Check @top_carrier.
Check @SetoidObject.
