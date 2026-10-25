(**
* Boundary probe for Instance/Ab/TorsionFree.v (issue #371)

    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    §IV.3, printed p. 92, Exercise 2.

    Every rejection the target's header MEASURES is pinned here rather
    than in the target itself, for the reason this tree records
    elsewhere: an in-file [Fail] renames in lockstep with the constant
    it guards, so it cannot detect a rename.  This file mirrors the
    target's FULL [Require] list plus the target — a short prefix is
    what makes a probe pass for a reason it never measured.

    SEVEN [Fail] commands: SIX negatives of THREE KINDS kept lexically
    apart, plus one scope-free instrument check.

      - CONVERSION (3): each reports "cannot unify" between two terms of
        ONE type.
      - TYPING (1): a plain "has type ... while it is expected to have
        type ...", with NO "cannot unify" and no universe clause.
      - FORMABILITY (2): each ends "universe inconsistency: Cannot
        enforce up = uh because uh < up".

    Each negative was stripped ONE AT A TIME (the others left as
    [Fail]), compiled alone, and its WHOLE error read; a [Fail] that
    succeeds prints NOTHING under this coqc, which is why stripping is
    the only way to see what fired.  Every constant a negative names is
    also named OUTSIDE a [Fail] below, so that renaming any of them
    breaks this file at a control rather than turning a guard silently
    green.

--------
* 用于 Instance/Ab/TorsionFree.v 的边界探测（问题 #371）

Mac Lane，《面向实际数学家的范畴》，第二版，第 IV.3 节，印刷页 92，练习 2。

每一次对目标头部 MEASURES 的拒绝都固定在这里，而不是在目标本身，因为这个树在其他地方记录了原因：文件内的 [Fail] 会与它保护的常量同步重命名，所以它无法检测重命名。该文件镜像了目标的完整 [Require] 列表以及目标本身 —— 一个短前缀就是让一次探测通过而达到它从未测量过的原因。

SEVEN [Fail] 命令：三种类型的六个否定在词汇上保持分离，再加一个无作用域的仪器检查。

- 转换 (3)：每个报告“无法统一”两个相同类型的项。
- 类型检查 (1)：一个简单的“具有类型...，但预期具有类型...”，没有“无法统一”也没有宇宙条款。
- 可形成性 (2)：每个以“宇宙不一致：无法强制 up = uh 因为 uh < up”结尾。

每个否定条件都是一次剥离（其他保持为 [Fail]），单独编译，并读取其整个错误；在此 coqc 下成功的 [Fail] 不会打印任何内容，这就是为什么剥离是唯一查看触发内容的方法。每个否定条件命名的常量也在下面的 [Fail] 外部命名，所以重命名其中任何一个会在控制处破坏此文件，而不是悄悄将保护标记为绿色。
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
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Ab.Character.Finite.
Require Import Category.Adjunction.Unitalization.
Require Import Category.Instance.Ab.TorsionFree.
Require Import Coq.ZArith.ZArith.

(**
** Instrument check

    Scope-free: it names nothing, so it stays red however the target is
    renamed, and it shows [Fail] is doing its job in this file.

--------
** 工具检查

    无范围：它不命名任何东西，所以无论目标如何被重命名，它都保持红色，并且它显示 [Fail] 正在这个文件中执行其工作。
*)

Fail Check probe_371_no_such_reference.

(**
** CONVERSION 1 — the unit is the projection POINTWISE, not as a
       morphism record

    [AdjunctionFromUniversalArrows] builds ⌊−⌋ as
    [fun g => fmap[U] g ∘ arrow], so the class unit is
    [fmap[Incl] id ∘ ab_quot_proj …].  Applied to an ELEMENT that
    composite reduces to the element itself, which is the target's
    [torsion_unit_is_proj]; as a whole [CMonHom] record it does not,
    and the `≈` form is the target's [torsion_unit_is_proj_hom].

--------
** 转换 1 — 单位是投影的逐点单位，而不是作为态射记录

[AdjunctionFromUniversalArrows] 将 ⌊−⌋ 构建为 [fun g => fmap[U] g ∘ arrow，因此类单位是 [fmap[Incl] id ∘ ab_quot_proj …]。应用于元素时，复合会简化为元素自身，这就是目标的 [torsion_unit_is_proj]；作为整体的 [CMonHom] 记录不会这样，而 `≈` 形式是目标的 [torsion_unit_is_proj_hom]。
*)

Fail Example probe_unit_is_proj_strict (A : AbObject) :
  torsion_unit A = ab_quot_proj (torsion_incl A) := eq_refl.

Example probe_unit_is_proj_pointwise (A : AbObject) (a : carrier A) :
  cmon_map (torsion_unit A) a
    = cmon_map (ab_quot_proj (torsion_incl A)) a := eq_refl.

(*
#1347: the unit's setoid-morphism component, at [eq_refl] since
   Instance/Sets.v gives its identity's and composite's properness fields
   as terms; against master 687ac356 it is refused with "cannot unify".
   The whole record is still refused (above).

--------
#1347：该单元的集合态射分量，在 [eq_refl] 处，因为 Instance/Sets.v 提供了其恒等和复合的适当性字段作为项；在主分支 687ac356 上，它被拒绝，“无法统一”。整个记录仍然被拒绝（如上所示）。
*)
Example probe_unit_is_proj_component (A : AbObject) :
  cmon_map (torsion_unit A)
    = cmon_map (ab_quot_proj (torsion_incl A)) := eq_refl.

(**
** CONVERSION 2 — the scalar action at a VARIABLE scalar

    [AbQuotient] reuses [A]'s own zero and addition, so those two fields
    ARE [A]'s on the nose (controls below) and [nat_smul] agrees at every
    CLOSED scalar.  At a variable [k] the [Fixpoint] is stuck, so
    conversion is left comparing the two [AbObject]s themselves, which
    differ in their setoid field — the whole point of the quotient — and
    in every law field; one differing law field alone already blocks
    it (measured in the target's header).  The target proves the
    agreement by induction ([nat_smul_quot]).

--------
** 转换 2 — 在可变标量上的标量操作

[AbQuotient] 重新使用 [A] 自身的零和加法，因此这两个字段正好成为 [A] 的字段（如下控制），并且 [nat_smul] 在每个闭合标量上都保持一致。在可变 [k] 上，[Fixpoint] 被卡住，因此转换会比较两个 [AbObject] 本身，它们在集合字段上有所不同——这是商的全部意义——并且在每个定律字段上也是如此；仅一个不同的定律字段就已经阻止了它（在目标的头部中测量）。目标通过归纳法（[nat_smul_quot]）证明了一致性。
*)

Fail Example probe_nat_smul_quot_strict
  (A : AbObject) (k : nat) (x : carrier A) :
  nat_smul (AbModTorsion A) k x = nat_smul A k x := eq_refl.

Example probe_nat_smul_quot_closed (A : AbObject) (x : carrier A) :
  nat_smul (AbModTorsion A) 2 x = nat_smul A 2 x := eq_refl.

Example probe_quot_zero_strict (A : AbObject) :
  cmon_zero (AbModTorsion A) = cmon_zero A := eq_refl.

Example probe_quot_plus_strict (A : AbObject) (x y : carrier A) :
  cmon_plus (AbModTorsion A) x y = cmon_plus A x y := eq_refl.

Lemma probe_nat_smul_quot_lemma
  (A : AbObject) (k : nat) (x : carrier A) :
  nat_smul (AbModTorsion A) k x = nat_smul A k x.
Proof. apply nat_smul_quot. Qed.

(**
** CONVERSION 3 — ℤ/T(ℤ) is not ℤ, though it is isomorphic to it

    ℤ is torsion-free, so its torsion subgroup is trivial and the
    reflector returns it up to isomorphism ([ZAb_reflect_iso], the
    counit isomorphism instantiated).  The two objects are nevertheless
    distinct: [AbModTorsion ZAb] carries the coarsened setoid.

--------
** 转换 3 — ℤ/T(ℤ) 不是 ℤ，尽管它与 ℤ 同构

ℤ 是无挠的，因此它的挠子子群是平凡的，反射器将其返回至同构（[ZAb_reflect_iso]，余单位同构被实例化）。然而，这两个对象仍然是不同的：[AbModTorsion ZAb] 承载了粗化的等价集。
*)

Fail Example probe_quot_ZAb_strict : AbModTorsion ZAb = ZAb := eq_refl.

Definition probe_ZAb_iso :
  fobj[TorsionFree_reflector] (Incl Ab TorsionFree_Sub ZAb_TF)
    ≅[Sub Ab TorsionFree_Sub] ZAb_TF := ZAb_reflect_iso.

(**
** TYPING — [Reflective] is a record, not an adjunction

    Mac Lane's phrase "full reflective subcategory" is the RECORD:
    fullness, a reflector, and the adjunction.  The adjunction alone is
    strictly less, and the mismatch is a plain typing error — no
    "cannot unify", no universe clause.

--------
** 输入——[Reflective] 是一个记录，而不是一个伴随

   麦克·莱恩（Mac Lane）的短语“完全反射子范畴”是这个记录：
   完整性、一个反射器，以及这个伴随。单独的伴随严格来说较少，这种不匹配只是一个明显的类型错误——没有“不能统一”，也没有宇宙子句。
*)

Fail Definition probe_reflective_is_adjunction
  : TorsionFree_reflector ⊣ Incl Ab TorsionFree_Sub :=
  TorsionFree_Reflective.

Definition probe_reflective_adj
  : TorsionFree_reflector ⊣ Incl Ab TorsionFree_Sub :=
  reflective_adj TorsionFree_Reflective.

Definition probe_reflective_record : Reflective TorsionFree_Sub :=
  TorsionFree_Reflective.

(**
** FORMABILITY — the donors identify hom with proof

    [Subcategory] is declared over [Category@{u u0 u0}] and [Reflective]
    over [Category@{u3 u5 u5}].  At a category whose hom and proof
    universes are declared strictly apart, naming a hom-set and an
    identity is fine while [Subcategory] is refused.  The second
    rejection below names [Reflective], but it fires at the
    [Subcategory] ARGUMENT with the identical message -- [Reflective]
    takes a [Subcategory] and cannot be tested apart from it (the trap
    Test/ProbeRingLattice340.v records for [MonoidObject]) -- so it
    separates nothing, and whether [Reflective] identifies anything OF
    ITS OWN is not measured here.  The identification is the DONORS'
    and is inherited by everything in the target; nothing there adds to
    it, and no constraint block of any constant of the target carries a
    universe equation at all.

--------
** 可构形性 — 捐赠者用证明识别 hom

[Subcategory] 在 [Category@{u u0 u0}] 和 [Reflective] 之上声明  
在 [Category@{u3 u5 u5}] 之上。在一个 hom 和证明宇宙严格分开的类别中，命名一个 hom 集合和一个恒等式是可以的，而 [Subcategory] 会被拒绝。下面第二个拒绝命名了 [Reflective]，但它在 [Subcategory] 参数上触发了相同的消息 —— [Reflective] 接受一个 [Subcategory]，并且不能被独立测试（Test/ProbeRingLattice340.v 记录了 [MonoidObject]）——所以它没有分离任何东西，[Reflective] 是否识别它自身的任何东西在这里不作衡量。该识别是捐赠者的，并被目标中的所有内容继承；那里没有任何东西能增加它，目标的任何常量的约束块根本不会携带宇宙方程。
*)

Section ProbeTorsionUniverses.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).
Context (xu yu : obj[Cu]).

Check (xu ~{Cu}~> yu).
Check (@id Cu xu).

Fail Check (@Subcategory Cu).

Fail Check (fun S : @Subcategory Cu => @Reflective Cu S).

End ProbeTorsionUniverses.

(** ** Controls naming every constant the negatives mention / ** 控制命名每一个负面提到的常量 *)

Check @torsion_unit.
Check @torsion_incl.
Check @ab_quot_proj.
Check @nat_smul.
Check @AbModTorsion.
Check @AbObject.
Check @carrier.
Check @TorsionFree_reflector.
Check @TorsionFree_Sub.
Check @TorsionFree_Reflective.
Check @TorsionFree_Full.
Check @Incl.
Check @Ab.
Check @ZAb.
Check @ZAb_TF.
Check @ZAb_reflect_iso.
Check @Subcategory.
Check @Reflective.
Check @Sub.
Check @nat_smul_quot.
Check @cmon_map.
Check @cmon_zero.
Check @cmon_plus.
