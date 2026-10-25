(**
* Probe for Instance/Cat/Limit.v (issue #414)

    Guards the boundary claims of Instance/Cat/Limit.v from OUTSIDE the
    target: an in-file [Fail] renames in lockstep with the constant it guards
    and so cannot detect a rename.  The [Require] list below mirrors the
    target's in full, plus the target itself; a shorter prefix is what makes
    a probe pass vacuously (a refusal on a missing coercion or an unresolved
    implicit reads like the refusal one meant to pin).

    Every [Fail] was stripped ONE AT A TIME in a copy of the WHOLE file and
    compiled alone, its error read in full; a passing [Fail] prints NOTHING
    under this coqc, so that is the only way to know a negative fires.

    Refutation commands: 1 instrument check + 9 negatives of THREE kinds,
    told apart by the error TEXT and not by their labels:

      FORMABILITY (universe; the message ends in a universe clause)
        N1  the donor: at [so < sh] the projection [PiCat_Proj C a] cannot be
            ascribed at a product whose object universe is [so] — its
            declared [PiCat] instance identifies the index universe with the
            small hom universe and bounds the product's object universe
            below by it.  Controls at the SAME levels: [PiCat C] at
            [Category@{so sh sh}], [PiCat C] as an object of
            [Cat@{_ sh _ so sh}], the class applied up to (not including)
            the projections, and the bare [PiCat_Proj C a] and [PiCat_ump R]
            (whose products land in a LARGER object universe).
        N2  inherited: [PiCat_IsIndexedProduct C] at [so < sh] — fires at
            the ARGUMENT [C] (the already-refused-argument shape), so it
            pins the boundary a consumer meets and corroborates nothing.
        N3  inherited: the instance [Cat_HasIndexedProducts@{i so sh _ _}]
            at [so < sh], refused directly ("Cannot enforce sh <= so").
        N4  [StrictCat_HasIndexedProducts uip fe] ascribed at a class whose
            index universe [i] sits strictly below the hom universe [h]:
            the message is a has-type mismatch CLOSING with a universe
            clause ("Cannot enforce h = i"), so it is classified here and
            not as typing.  Control: [StrictCat_HasEqualizers] at [h].
        N5  [StrictCat_Complete uip fe] ascribed at [Complete@{i h h _}],
            the shape [Complete_from_products_equalizers] forces (the index
            universe IS the ambient hom universe).
        N6  the donor of N5: [Complete_from_products_equalizers] fed a
            product structure whose index universe is [i < h].
      TYPING (a plain has-type mismatch, no "cannot unify", no universe
              clause)
        N7  [Eq_IsEqualizer F G uip] ascribed at [@IsEqualizer Cat ...]: the
            strict equalizer's universal property is a statement in
            [StrictCat], and the two types differ in the (implicit) ambient
            category.  The mathematics behind the refusal is
            [EqCat_not_Cat_equalizer] in the target.
      CONVERSION (an [eq_refl] refused where both sides share a type)
        N8  [EqIncl F G ◯ Eq_med F G h Hh = h] as WHOLE functor records,
            with the two DATA fields agreeing at [eq_refl] as controls: the
            difference is confined to [Compose]'s three rebuilt law fields.
        N9  [PiCat_Proj C i ◯ PiCat_Pair R = R i], likewise, with both data
            fields as controls.

    Positive readbacks (all [eq_refl]): the class's object and projections
    at [Cat] ARE [PiCat] and [PiCat_Proj]; the mediator the strict
    equalizer's universal property produces IS [Eq_med]; the chosen
    equalizer of [StrictCat_HasEqualizers] IS [EqCat] with inclusion
    [EqIncl]; [EqCat F G] IS [Sub C (EqSub F G)] (delta, a guard against
    name drift); the inclusion's object action IS the first projection.

    Guard block: every constant a negative names is [Check]ed outside every
    [Fail], so a rename in the target breaks this file on a [Check] line and
    never turns a negative vacuously green.  Rename-simulated over the
    target constants the negatives name; the result is recorded in the
    target's header.

--------
* 探测实例/Cat/Limit.v（问题 #414）

从目标之外保护 Instance/Cat/Limit.v 的边界声明：文件内的 [Fail] 会与它保护的常量同步重命名，因此无法检测重命名。下面的 [Require] 列表完整镜像了目标，包括目标本身；一个较短的前缀会使探测在表面上通过（对缺失的强制转换或未解决的隐式的拒绝，看起来就像是本来想固定的拒绝）。

每个 [Fail] 都在整个文件的副本中一次性被剥离，并单独编译，其错误会完整读取；一个通过的 [Fail] 在这个 coqc 下不会打印任何内容，因此这是唯一知道负触发的方法。

反驳命令：1次乐器检查 + 9种类型的否定，通过错误文本而不是它们的标签区分：

可形成性（宇宙；消息以宇宙子句结束）
        N1 捐赠者：在 [so < sh] 上，投影 [PiCat_Proj C a] 不能归因于对象宇宙为 [so] 的积——其声明的 [PiCat] 实例将索引宇宙标识为小同构宇宙，并将积的对象宇宙的下界限定于此。在相同层级上的控制：[PiCat C] 在 [Category@{so sh sh}]，[PiCat C] 作为 [Cat@{_ sh _ so sh}] 的对象，类应用直到（但不包括）投影，以及裸 [PiCat_Proj C a] 和 [PiCat_ump R]（其积落入更大的对象宇宙）。
        N2 继承：[PiCat_IsIndexedProduct C] 在 [so < sh] — 触发于参数 [C]（已拒绝参数形状），因此它固定了消费者所遇到的边界，但没有提供任何佐证。
N3 继承自：实例 [Cat_HasIndexedProducts@{i so sh _ _}] 在 [so < sh] 直接拒绝（“无法强制执行 sh <= so”）。N4  [StrictCat_HasIndexedProducts uip fe] 被归属于一个类，其索引宇宙 [i] 严格低于同态宇宙 [h]：消息是一个带有宇宙子句的类型不匹配 CLOSING（“无法强制执行 h = i”），因此它在此处被分类，而不是作为类型。控制：[StrictCat_HasEqualizers] 在 [h]。N5  [StrictCat_Complete uip fe] 被归属于 [Complete@{i h h _}]，形状 [Complete_from_products_equalizers] 强制（索引宇宙就是环境同态宇宙）。N6  N5 的提供者：[Complete_from_products_equalizers] 提供了一个其索引宇宙是 [i < h] 的积结构。
TYPING（一个普通的类型不匹配，没有“无法统一”，没有宇宙子句）
        N7  [Eq_IsEqualizer F G uip] 在 [@IsEqualizer Cat ...] 被指定：严格等化器的普遍性质是在 [StrictCat] 中的陈述，而两种类型在（隐含的）环境类别中不同。拒绝背后的数学是目标中的 [EqCat_not_Cat_equalizer]。CONVERSION（在双方共享类型的情况下被拒绝的 [eq_refl]）
        N8  [EqIncl F G ◯ Eq_med F G h Hh = h] 作为整体函子记录，两个 DATA 字段在 [eq_refl] 上作为控制器一致：区别仅限于 [Compose] 的三个重建的定律字段。N9  [PiCat_Proj C i ◯ PiCat_Pair R = R i]，同样地，两个数据字段作为控制器。

积极反馈（全部 [eq_refl]）：类的对象和在 [Cat] 的投影是 [PiCat] 和 [PiCat_Proj]；中介者严格等化器的普遍性质产生的是 [Eq_med]；[StrictCat_HasEqualizers] 的选定等化器是 [EqCat]，包含 [EqIncl]；[EqCat F G] 是 [Sub C (EqSub F G)]（delta，防止名称漂移）；包含的对象作用是第一个投影。

保护块：每个常量的负名称在每个 [Fail] 外部都被 [Check]，因此目标中的重命名会在 [Check] 行上破坏此文件，并且永远不会使负值无条件变为绿色。重命名在目标常量上模拟了负名称；结果记录在目标的头部。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Category.Monoid.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.One.

From Coq Require Import Eqdep_dec.

Require Import Category.Instance.Cat.Limit.

Generalizable All Variables.

(** ** Instrument check: a [Fail] on an absent name does fail / ** 仪器检查：在缺席名称上，[Fail] 会失败 *)

Fail Check probe414_absent_name.

(** ** N1-N3: the index-below-object boundary of the [Cat] instance / ** N1-N3：[Cat] 实例的索引下方对象边界 *)

Section IndexBoundary.

Universe i so sh.
Constraint so < sh.
Constraint i <= so.

(*
Controls: the product itself sits at the small categories' own levels,
   is an object of a [Cat] over them, and the class is formable up to the
   projections.

--------
控制：产品本身位于小类别自身的层级上，是它们之上的 [Cat] 的对象，并且该类可以形成直到投影。
*)
Check (fun (I : Type@{i}) (C : I → Category@{so sh sh}) =>
         (PiCat C : Category@{so sh sh})).
Check (fun (I : Type@{i}) (C : I → Category@{so sh sh}) =>
         (PiCat C : obj[Cat@{_ sh _ so sh}])).
Check (fun (I : Type@{i}) (C : I → Category@{so sh sh}) =>
         @IsIndexedProduct Cat@{_ sh _ so sh} I C (PiCat C)).
Check (fun (I : Type@{i}) (C : I → Category@{so sh sh}) (a : I) =>
         PiCat_Proj C a).
Check (fun (I : Type@{i}) (C : I → Category@{so sh sh})
           (D : Category@{so sh sh}) (R : ∀ a, D ⟶ C a) => PiCat_ump R).

(*
N1: the donor.  The projection's product cannot have object universe
   [so] when [so < sh].

--------
N1：捐赠者。投影的产物在 [so < sh] 时不能有对象宇宙 [so]。
*)
Fail Check (fun (I : Type@{i}) (C : I → Category@{so sh sh}) (a : I) =>
              (PiCat_Proj C a : PiCat@{i so sh so sh} C ⟶ C a)).

(* N2: inherited, firing at the argument [C]. / N2：继承，自 [C] 参数触发。 *)
Fail Check (fun (I : Type@{i}) (C : I → Category@{so sh sh}) =>
              PiCat_IsIndexedProduct C).

(* N3: inherited, the instance refused directly. / N3：继承的，实例直接被拒绝。 *)
Fail Check @Cat_HasIndexedProducts@{i so sh _ _}.

End IndexBoundary.

(** ** N4-N6: the index universe of the strict product and of completeness / ** N4-N6：严格乘积和完备性的指标宇宙 *)

Section StrictIndexBoundary.

Universe i h.
Constraint i < h.

(* Control: equalizers in [StrictCat] mention no index. / 控制：[StrictCat] 中的均衡器未提及索引。 *)
Check @StrictCat_HasEqualizers@{h _ _ _ _ _}.

(*
N4: the strict product structure at an index universe below the hom
   universe.

--------
N4：在同伦宇宙之下的指数宇宙中的严格乘积结构。
*)
Fail Check (fun (uip : ∀ C : Category@{h h h}, ObjUIP C)
                (fe : DepFunext@{h h}) =>
              (StrictCat_HasIndexedProducts uip fe
                 : HasIndexedProducts@{i i i _ _ h} StrictCat)).

(* Control: the completeness statement at its own shape. / 控制：其自身形态的完整性声明。 *)
Check (fun (uip : ∀ C : Category@{h h h}, ObjUIP C)
           (fe : DepFunext@{h h}) =>
         (StrictCat_Complete uip fe : Complete@{h h h _})).

(* N5: completeness over diagram shapes whose objects sit below [h]. / N5：关于其对象位于 [h] 下方的图表形状的完整性。 *)
Fail Check (fun (uip : ∀ C : Category@{h h h}, ObjUIP C)
                (fe : DepFunext@{h h}) =>
              (StrictCat_Complete uip fe : Complete@{i h h _})).

(* N6: the donor of N5 — the reduction theorem itself demands index = hom. / N6：N5 的供体——归约定理本身要求索引 = 同胚。 *)
Fail Check (fun (Cu : Category@{_ h h})
                (HP : HasIndexedProducts@{i i i _ _ h} Cu)
                (HE : HasEqualizers Cu) =>
              Complete_from_products_equalizers HP HE).

End StrictIndexBoundary.

(** ** N7: the strict equalizer is a [StrictCat] statement / ** N7：严格均衡器是一个 [StrictCat] 语句 *)

Section StrictNotWeak.

Context {C D : Category} (F G : C ⟶ D) (uip : ObjUIP D).

Check (Eq_IsEqualizer F G uip
         : @IsEqualizer StrictCat C D F G (EqCat F G) (EqIncl F G)).

Fail Check (Eq_IsEqualizer F G uip
              : @IsEqualizer Cat C D F G (EqCat F G) (EqIncl F G)).

End StrictNotWeak.

(** ** N8: the equalizer triangle holds on both data fields, not as records / ** N8: the equalizer triangle holds on both data fields, not as records / ** N8：均衡三角形在两个数据字段上都成立，而不是作为记录 *)

Section EqualizerTriangle.

Context {C D : Category} (F G : C ⟶ D) {Z : Category} (h : Z ⟶ C)
  (Hh : F ∘[StrictCat] h ≈[StrictCat] G ∘[StrictCat] h).

Example eq_triangle_fobj :
  ∀ z, fobj[EqIncl F G ◯ Eq_med F G h Hh] z = fobj[h] z := fun _ => eq_refl.

Example eq_triangle_fmap :
  ∀ x y (f : x ~> y), fmap[EqIncl F G ◯ Eq_med F G h Hh] f = fmap[h] f
  := fun _ _ _ => eq_refl.

Fail Example eq_triangle_record :
  EqIncl F G ◯ Eq_med F G h Hh = h := eq_refl.

End EqualizerTriangle.

(** ** N9: the product triangle, likewise / ** N9：产品三角形，同样 *)

Section ProductTriangle.

Context {I : Type} (C : I → Category) {D : Category} (R : ∀ i, D ⟶ C i)
  (i : I).

Example pi_triangle_fobj :
  ∀ d, fobj[PiCat_Proj C i ◯ PiCat_Pair R] d = fobj[R i] d := fun _ => eq_refl.

Example pi_triangle_fmap :
  ∀ x y (f : x ~> y), fmap[PiCat_Proj C i ◯ PiCat_Pair R] f = fmap[R i] f
  := fun _ _ _ => eq_refl.

Fail Example pi_triangle_record :
  PiCat_Proj C i ◯ PiCat_Pair R = R i := eq_refl.

End ProductTriangle.

(** ** Positive readbacks / ** 积极复述 *)

Section Readbacks.

Context {C D : Category} (F G : C ⟶ D) (uip : ∀ C : Category, ObjUIP C)
  {Z : Category} (h : Z ⟶ C)
  (Hh : F ∘[StrictCat] h ≈[StrictCat] G ∘[StrictCat] h).

Example eq_mediator_is_Eq_med :
  unique_obj (eq_desc (Eq_IsEqualizer F G (uip D)) h Hh) = Eq_med F G h Hh
  := eq_refl.

Example strict_equalizer_obj :
  `1 (@equalizer StrictCat (StrictCat_HasEqualizers uip) C D F G) = EqCat F G
  := eq_refl.

Example strict_equalizer_map :
  `1 `2 (@equalizer StrictCat (StrictCat_HasEqualizers uip) C D F G)
  = EqIncl F G := eq_refl.

Example eqcat_is_sub : EqCat F G = Sub C (EqSub F G) := eq_refl.

Example eqincl_obj : ∀ x, fobj[EqIncl F G] x = `1 x := fun _ => eq_refl.

End Readbacks.

Section ProductReadbacks.

Context {A : Type} (C : A → Category).

Example cat_iprod_is_PiCat : @indexed_product Cat _ A C = PiCat C := eq_refl.

Example cat_iprod_proj_is_PiCat_Proj :
  ∀ a, @indexed_product_proj Cat _ A C a = PiCat_Proj C a := fun _ => eq_refl.

End ProductReadbacks.

(** ** The weak ambient, at the measurement the target ships / ** 在测量目标船只时的微弱环境 *)

Check EqCat_not_Cat_equalizer.
Check ChaoticBool_points_equiv.

(** ** Guard block: every constant a negative names, outside every [Fail] / ** 保护块：每个常量都是负名，在每个 [Fail] 之外 *)

Check @PiCat.
Check @PiCat_Proj.
Check @PiCat_Pair.
Check @PiCat_ump.
Check @PiCat_IsIndexedProduct.
Check @Cat_HasIndexedProducts.
Check @StrictCat_HasEqualizers.
Check @StrictCat_HasIndexedProducts.
Check @StrictCat_Complete.
Check @Complete_from_products_equalizers.
Check @DepFunext.
Check @ObjUIP.
Check @HasIndexedProducts.
Check @HasEqualizers.
Check @Complete.
Check @IsEqualizer.
Check @IsIndexedProduct.
Check @Eq_IsEqualizer.
Check @EqCat.
Check @EqIncl.
Check @EqSub.
Check @Eq_med.
Check @Cat.
Check @StrictCat.
