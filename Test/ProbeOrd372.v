(**
* Probe for #372(a): the boundaries of Instance/Ord.v and
      Instance/Ord/Poset.v

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          §IV.3, printed p. 92, Exercise 4(a).  Catalog id:
          maclane:IV.3:ex4.

    This file exists so that every rejection the two library files
    MEASURE is also GUARDED.  It restates them from OUTSIDE those files,
    because an in-file [Fail] renames in lockstep with the constant it
    guards and so cannot detect a rename; and it mirrors the FULL
    [Require] list of both, because a short prefix is what makes a probe
    fail for a reason it never measured.

    Six negatives of THREE kinds, plus one scope-free instrument check.
    Each was stripped ONE AT A TIME into its own file and compiled alone,
    and its WHOLE error was read; the kind recorded below is read off that
    error rather than assumed.

    CONVERSION (four; each ends "cannot unify" between two terms of one
    type):

    1. [neg_posets_round_strict] -- the [Pos]/[Posets] round trip is not
       [eq_refl] on the nose.  Error: cannot unify
       "fobj[Pos_to_Posets] (fobj[Posets_to_Pos] x)" and "x".  Cause: an
       object of [Posets] is a stdlib [sigT], which Lib.v's [Set
       Primitive Projections] does not cover, so [(`1 x; `2 x) = x] holds
       only after a [destruct].  Control: [ctrl_posets_round], the SAME
       statement discharged by [posets_pos_posets_obj] -- so the negative
       measures the missing eta and nothing else.
    2. [neg_unit_record] -- the adjunction's unit is not the projection as
       a RECORD.  Error: cannot unify "poset_unit P" and
       "reflection_proj P".  Control: [ctrl_unit_pointwise], the same
       identification applied to a point, which IS [eq_refl].
    3. [neg_natle_reflection_eq] -- the reflection of a partial order is
       not equal to it.  Error: cannot unify "PosetReflection NatLe" and
       "NatLe".  Control: [ctrl_natle_reflection_order], which shows the
       two agree in the ORDER field, so the difference is the setoid.
    5. [neg_ord_obj_is_not_points] -- the reviewer's distinction.  Error:
       cannot unify "obj[Ord]" and "obj[OrdAsCategory Chaos2]".  Controls:
       [ctrl_ord_obj] and [ctrl_thin_obj] name both sides positively.

    TYPING (one; a plain mismatch, with NO "cannot unify" and no universe
    clause):

    4. [neg_adj_is_not_reflective] -- the adjunction is strictly less than
       the [Reflective] record.  Error: The term "Poset_adj" has type
       "Poset_reflector ⊣ Incl Ord Pos_Sub" while it is expected to have
       type "Reflective Pos_Sub".  Control: [ctrl_reflective_adj].

    FORMABILITY (one; "universe inconsistency: Cannot enforce up = uh"):

    6. [Subcategory C] is refused at a category whose hom and proof
       universes are declared strictly apart, while [x ~> y] and [id{C}]
       at those very levels are ACCEPTED -- so the rejection is the
       donor's identification and not an artifact of naming a hom.  Only
       ONE such negative is stated: [Reflective] takes a [Subcategory] and
       cannot be tested apart from it (the trap
       Test/ProbeRingLattice340.v records for [MonoidObject]), so a second
       negative naming [Reflective] would fire at its argument and measure
       nothing new.

    A SEVENTH negative was drafted and WITHDRAWN as a false pass:
    [Fail Example : obj[Ord] := OrdAsCategory P] SUCCEEDS, because Coq
    inserts [@reverse_coercion (obj[Ord]) Category P (OrdAsCategory P)].
    Negative 5 replaces it at the level of the two object TYPES, where no
    coercion can intervene.  The episode is recorded rather than quietly
    fixed.

    Every constant a negative names also appears OUTSIDE a [Fail], in the
    control block below or in a control beside the negative itself.

--------
* 探查 #372(a)：Instance/Ord.v 和 Instance/Ord/Poset.v 的边界

书籍：Mac Lane，《为在职数学家准备的范畴论》，第2版，第IV.3节，第92页印刷，练习4(a)。目录编号：maclane:IV.3:ex4。

这个文件存在的目的是为了确保两个库文件中的每个拒绝 MEASURE 也受到保护。它从这些文件之外重新声明它们，因为文件内的 [Fail] 会与它所保护的常量同步重命名，所以无法检测重命名；并且它镜像了两者的完整 [Require] 列表，因为一个简短的前缀会导致探测失败，而这是它从未测量过的原因。

三种类型的六个负号，加上一个无范围工具检查。每一个都被一次性剥离到自己的文件中并单独编译，然后读取其整个错误；下面记录的类型是从该错误中读取的，而不是假设的。

转换（四个；每个在同一类型的两个项之间结束“无法统一”）：

1. [neg_posets_round_strict] —— [Pos]/[Posets] 往返不是 [eq_refl] 精确匹配。错误：无法统一“fobj[Pos_to_Posets] (fobj[Posets_to_Pos] x)”和“x”。原因：一个 [Posets] 对象是 stdlib [sigT]，而 Lib.v 的 [Set Primitive Projections] 并未涵盖它，所以 [(`1 x; `2 x) = x] 只在 [destruct] 之后成立。控制：[ctrl_posets_round]，即由 [posets_pos_posets_obj] 处理的相同语句 —— 因此负向仅衡量缺失的 eta，而无其他。 2. [neg_unit_record] —— 结合子的单位不是作为 RECORD 的投影。错误：无法统一“poset_unit P”和“reflection_proj P”。控制：[ctrl_unit_pointwise]，相同的标识应用于一个点，即 [eq_refl]。3. [neg_natle_reflection_eq] -- 部分序的反射不等于它本身。错误：无法统一 "PosetReflection NatLe" 和 "NatLe"。控制：[ctrl_natle_reflection_order]，显示两者在 ORDER 字段上是一致的，因此差异在于等价类。5. [neg_ord_obj_is_not_points] -- 审阅者的区分。错误：无法统一 "obj[Ord]" 和 "obj[OrdAsCategory Chaos2]"。控制：[ctrl_ord_obj] 和 [ctrl_thin_obj] 正确地命名了两边。

类型检查（一个；一个简单的不匹配，没有“无法统一”和没有宇宙条款）：

4. [neg_adj_is_not_reflective] -- 附加严格小于 [Reflective] 记录。错误：术语“Poset_adj”的类型为“Poset_reflector ⊣ Incl Ord Pos_Sub”，而预期类型为“Reflective Pos_Sub”。控制：[ctrl_reflective_adj]。

可成形性（一个；“宇宙不一致：无法强制执行 up = uh”）：

6. 当同构和证明宇宙被严格区分声明时，[Subcategory C] 在该类别中被拒绝，而 [x ~> y] 和 [id{C}] 在同一级别则被接受——因此拒绝的是捐赠者的标识，而不是命名同构的产物。只有一个这样的否定被陈述：[Reflective] 接受一个 [Subcategory] 并且无法独立测试它（陷阱 Test/ProbeRingLattice340.v 为 [MonoidObject] 记录），所以第二个命名 [Reflective] 的否定将作用于它的参数而不会测量到新的内容。

第七条否定被起草并作为虚假通过被撤回：
    [Fail Example : obj[Ord] := OrdAsCategory P] 成功，因为 Coq
    插入了 [@reverse_coercion (obj[Ord]) Category P (OrdAsCategory P)]。
    否定 5 在两个对象类型的层面上取代了它，此处不能进行任何强制转换。这个事件被记录下来，而不是悄悄修正。

每个常量负名称也出现在 [Fail] 外，在下面的控制块中或在负本身旁边的控制中。
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
Require Import Category.Instance.Proset.
Require Import Category.Instance.Pos.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Ord.
Require Import Category.Instance.Ord.Poset.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** ** Instrument check / ** 仪表检查 *)

Fail Definition probe_ord372_instrument : nat := true.

(** ** Controls / ** 控制 *)

Check @Poset_Reflective_in_Ord.
Check @Poset_reflector.
Check @Poset_adj.
Check @Pos_Sub.
Check @Pos_Sub_Full.
Check @Posets.
Check @Ord.
Check @OrdObject.
Check @OrdAntisymmetric.
Check @PosetReflection.
Check @PosetReflectionObj.
Check @reflection_proj.
Check @poset_unit.
Check @NatLe.
Check @NatLePos.
Check @Chaos2.
Check @MixOrd.
Check @Pos_to_Posets.
Check @Posets_to_Pos.
Check @Pos_Posets_strict_iso.
Check @posets_pos_posets_obj.
Check @OrdAsCategory.
Check @OrdHomAsFunctor.
Check @Subcategory.
Check @Reflective.
Check @Incl.
Check @Proset.
Check @PosetObject.

(** ** Negative 1 (CONVERSION) / ** 负 1（转换） *)

Example ctrl_posets_round (x : Posets) :
  fobj[Pos_to_Posets] (fobj[Posets_to_Pos] x) = x
  := posets_pos_posets_obj x.

Fail Example neg_posets_round_strict (x : Posets) :
  fobj[Pos_to_Posets] (fobj[Posets_to_Pos] x) = x := eq_refl.

(** ** Negative 2 (CONVERSION) / ** 负 2（转换） *)

Example ctrl_unit_pointwise (P : OrdObject)
    (x : carrier (ord_setoid P)) :
  ord_fn (poset_unit P) x = ord_fn (reflection_proj P) x := eq_refl.

Fail Example neg_unit_record (P : OrdObject) :
  poset_unit P = reflection_proj P := eq_refl.

(** ** Negative 3 (CONVERSION) / ** 负 3（转换） *)

Example ctrl_natle_reflection_order :
  ord_le (PosetReflection NatLe) = ord_le NatLe := eq_refl.

Fail Example neg_natle_reflection_eq :
  PosetReflection NatLe = NatLe := eq_refl.

(** ** Negative 4 (TYPING) / ** 负 4（打字中） *)

Example ctrl_reflective_adj :
  Poset_reflector ⊣ Incl Ord Pos_Sub := Poset_adj.

Fail Example neg_adj_is_not_reflective :
  Reflective Pos_Sub := Poset_adj.

(**
** Negative 5 (CONVERSION): the reviewer's distinction.

    The objects of [Ord] are PREORDERS; the objects of [OrdAsCategory P]
    are the POINTS of one preorder.  Both readings are pinned positively
    just below, and their identification is refuted.

--------
** 负 5（转换）：评论者的区分。

[Ord] 的对象是前序；[OrdAsCategory P] 的对象是一个前序的点。两种读法都在下方被正向固定，并且它们的同一性被驳斥。
*)

Example ctrl_ord_obj : obj[Ord] = OrdObject := eq_refl.

Example ctrl_thin_obj :
  obj[OrdAsCategory Chaos2] = carrier (ord_setoid Chaos2) := eq_refl.

Fail Example neg_ord_obj_is_not_points :
  obj[Ord] = obj[OrdAsCategory Chaos2] := eq_refl.

(** ** Negative 6 (FORMABILITY) / ** 负 6（可成型性） *)

Section ProbeUniverses.
  Universes uo uh up.
  Constraint uh < up.
  Context (C : Category@{uo uh up}) (x y : C).

  Check (x ~> y).
  Check (@id C x).

  Fail Check (Subcategory C).
End ProbeUniverses.
