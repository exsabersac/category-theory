Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Instance.Mod.Quotient.Isomorphism.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Universal.Element.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(**
* Boundary probes for the quotient module and the quotient ring

    Companion to Instance/Mod/Quotient.v,
    Instance/Mod/Quotient/Isomorphism.v and Instance/Rng/Quotient.v
    (issue #314, Mac Lane §III.1 Exercises 5 and 6).  Those files make
    four strength claims whose negative side is a CONVERSION boundary;
    a measurement recorded only in prose would not be noticed by a
    refactor, so it is pinned here.  **If the [Fail] commands below stop
    being rejected, this file breaks the build.**

    Each negative is paired with a positive control that must SUCCEED,
    for the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone
    passes just as happily when a name has been renamed out from under
    it.  Every negative is a [Fail Definition ... := eq_refl] and not a
    [Fail Example ... : T.]; the latter guards only that the STATEMENT
    elaborates and reports "The command has not failed!" when the
    statement is fine and only the proof would have been rejected.

    The instrument itself was checked (wrapping [Fail] around a
    succeeding command aborts compilation with "The command has not
    failed!"), and each negative was compiled once with the [Fail]
    stripped, to confirm the error is the intended conversion failure
    and not a syntax, scope or resolution error.  The observed errors
    are recorded beside each probe.

    THE IMPORT LIST IS THE UNION OF THE TARGETS', IN THEIR ORDER, and
    that is deliberate rather than tidy: a short prefix is exactly what
    makes a probe pass vacuously, by turning a conversion rejection into
    an elaboration error that [Fail] swallows just as happily.

--------
* 商模和商环的边界探测

《Instance/Mod/Quotient.v、Instance/Mod/Quotient/Isomorphism.v 和 Instance/Rng/Quotient.v 的配套文件》（问题 #314，Mac Lane §III.1 练习 5 和 6）。这些文件提出了四个强度声明，其负面方面是 CONVERSION 边界；仅以散文记录的测量将不会被重构工具注意到，所以它在这里被固定。**如果下面的 [Fail] 命令不再被拒绝，这个文件将导致构建失败。**

每个阴性样本都配有一个必须成功的阳性对照，其原因如 Test/ProbeQuiverConstructions.v 所示：单独的 [Fail] 在名称被重命名后仍然能愉快地通过。每个阴性样本都是一个 [Fail Definition ... := eq_refl]，而不是 [Fail Example ... : T.]；后者只保护 STATEMENT 的展开并报告“命令未失败！”当语句正确且仅证明会被拒绝时。

仪器本身已被检查（将 [Fail] 包裹在随后的命令周围会中止编译，并显示“命令未失败！”），每个负面案例都在去掉 [Fail] 后编译一次，以确认错误是预期的转换失败，而不是语法、作用域或解析错误。观察到的错误记录在每个探针旁边。

导入列表是目标的并集，按它们的顺序排列，这是故意的，而不是为了整洁：一个短前缀正是让探测徒然通过的原因，它通过将转换拒绝变成 [Fail] 同样乐意吞掉的展开错误。
*)

(**
** (1) The two quotient relations are not convertible

    Instance/Mod/Quotient.v reconciles Instance/Mod.v's [RModQuotient]
    with [QuotientMod (ImageSubmod f)] by the BICONDITIONAL
    [rmod_quotient_relations_agree] and by an isomorphism whose legs are
    the identity on elements.  The header says the two relations are not
    convertible -- [∃ a, x ≈ y + f a] against
    [inhabited { a & x + (-y) ≈ f a }] -- and this is that measurement.

    Stripped, the first probe reports
      "(cannot unify "ab_coset_eq f x y" and
        "mquot_rel (ImageSubmod f) x y")"
    -- a genuine conversion refusal.  (The printed form drops [rm_hom],
    which is a coercion.)  RE-MEASURED at the end of the PR "algebraic
    carriers are sets" (2026-09-17) by stripping this [Fail] alone in a
    copy of this WHOLE file: rc=1, and the parenthetical above reproduces
    byte for byte.  An earlier note said the file was blocked from
    building and the text could not be re-measured; it builds, and it
    was.

    AN EARLIER REVISION wrote both relations as [sigT]s and called the
    refusal "a conversion failure between the two [sigT] types".  Since the
    PR "algebraic carriers are sets" (2026-09-17) the left side is an [ex]
    and the right side the propositional TRUNCATION of a [sigT], so they
    now differ in shape as well as in sort, and neither is a bare [sigT].
    The refusal itself was RE-MEASURED at this revision, by stripping this
    probe in a copy of the whole file, and its "cannot unify" clause is
    unchanged word for word; P2-I could not re-measure it because the ring
    layer was not building then.

--------
** (1) 这两个商关系不可互换

Instance/Mod/Quotient.v 通过 BICONDITIONAL [rmod_quotient_relations_agree] 以及一个两条边在元素上为恒等的同构，将 Instance/Mod.v 的 [RModQuotient] 与 [QuotientMod (ImageSubmod f)] 调和。头部说明这两个关系不可转换 -- [∃ a, x ≈ y + f a] 对 [inhabited { a & x + (-y) ≈ f a }] -- 这就是该测量。

第一个探测器报告说，已经被剥夺了
      “（无法统一”ab_coset_eq f x y“ 和
        “mquot_rel （ImageSubmod f） x y”）”
    ——真正的皈依拒绝。（打印表格[rm_hom]，
    这是一种强制力。）在PR“代数”末尾重新测量
    载体是集合“（2026-09-17），仅在一页中剥离[Fail]
    复制整个文件：rc=1，括号内还原了上述内容
    逐字节。之前的说明说该文件被阻挡了
    构建和文本无法重新衡量;它在构建，而且
    曾经。

早期的一个修订将两个关系都写作 [sigT]s，并称拒绝为“两个 [sigT] 类型之间的转换失败”。由于 PR“代数承载体是集合”（2026-09-17），左侧是一个 [ex]，而右侧是一个 [sigT] 的命题截断，所以它们现在在形状和类型上都不同，而且都不是单纯的 [sigT]。本次修订中，拒绝本身经过重新测量，通过在整个文件的副本中去掉该探针，其“无法统一”条款完全保持不变；P2-I 当时无法重新测量它，因为环层当时没有构建。
*)

Section RelationBoundary.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).
Context (x y : carrier (cmon_setoid N)).

Fail Definition probe_relations_convertible :
  ab_coset_eq (rm_hom f) x y = mquot_rel (ImageSubmod f) x y := eq_refl.

(*
POSITIVE CONTROL at the same arguments: the two relations DO agree,
   and the biconditional that says so is available here.

--------
在相同参数下的阳性对照：这两个关系确实一致，说明这一点的双条件在这里是可用的。
*)
Definition control_relations_agree :
  ab_coset_eq (rm_hom f) x y ↔ mquot_rel (ImageSubmod f) x y :=
  rmod_quotient_relations_agree f x y.

(*
SECOND POSITIVE CONTROL: an [eq_refl] of the same SHAPE that does
   hold, so the probe above is not merely rejecting all [eq_refl]s
   between relation types.  Membership in the image submodule IS the
   sigma it is defined as.

--------
第二个阳性对照：一个相同形状的 [eq_refl] 它确实保持，所以上面的探针并不仅仅是拒绝关系类型之间的所有 [eq_refl]。图像子模块中的成员资格确实是它被定义为的 sigma。
*)
Definition control_image_mem :
  smod_mem (ImageSubmod f) x
    = { a : carrier (cmon_setoid M) & cmon_map (rm_hom f) a ≈ x }
  := eq_refl.

End RelationBoundary.

(**
** (2) ...nor are the two quotient objects Leibniz-equal

    [RModQuotient_is_quotient_by_image] is an ISOMORPHISM in [RMod R],
    not an equality of records; the carriers agree but the setoids do
    not, so nothing stronger is available.

    Stripped, this reports a conversion failure between the two
    [RModObject] records.

--------
** (2) ...这两个商对象也不是莱布尼兹等价的

[RModQuotient_is_quotient_by_image] 是 [RMod R] 中的一个同构，而不是记录的相等；其承载体相同，但集体不同，因此无法提供更强的结论。

简化后，这报告了两个 [RModObject] 记录之间的转换失败。
*)

Section ObjectBoundary.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).

Fail Definition probe_objects_equal :
  RModQuotient f = QuotientMod (ImageSubmod f) := eq_refl.

(*
POSITIVE CONTROL: the CARRIERS do agree on the nose -- both are N's
   -- so what the probe measures is the setoid and not the carrier.

--------
阳性对照：载体在鼻子上确实一致——两者都是 N——所以探针测量的是等价类而不是载体。
*)
Definition control_carriers_agree :
  carrier (cmon_setoid (RModQuotient f))
    = carrier (cmon_setoid (QuotientMod (ImageSubmod f))) := eq_refl.

(* SECOND POSITIVE CONTROL: the isomorphism that IS available. / 第二个阳性对照：可用的同构。 *)
Definition control_objects_iso :
  RModQuotient f ≅[RMod R] QuotientMod (ImageSubmod f) :=
  RModQuotient_is_quotient_by_image f.

End ObjectBoundary.

(**
** (3) The first isomorphism theorem's triangle is not [eq_refl]

    Instance/Mod/Quotient/Isomorphism.v says both LEGS of the comparison
    are the two mediators by convertibility, and that the boundary which
    does NOT hold strictly is the mediator's TRIANGLE, which is `≈` and
    not Leibniz.  Both halves are pinned here, the positive one first.

    Stripped, the probe reports a conversion failure between the
    composite [RModHom] and [mod_image_cores f]: the composite's
    underlying map is [Basics.compose] of two maps, which is not the
    same TERM as the corestriction even though it sends every element to
    the same value.

--------
** (3) 第一同构定理的三角形不是 [eq_refl]

    Instance/Mod/Quotient/Isomorphism.v 表明比较的两个支线（LEGS）都是通过可转换性得到的两个中介，而不严格成立的边界是中介的三角形（TRIANGLE），它是 `≈` 而不是 Leibniz。这里固定了两半，先处理正边。

    去除后，探测器报告复合 [RModHom] 与 [mod_image_cores f] 之间的转换失败：该复合的底层映射是两个映射的 [Basics.compose]，虽然它将每个元素都映射到相同的值，但与余限制（corestriction）的 TERM 并不相同。
*)

Section TriangleBoundary.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).

(* POSITIVE CONTROLS: both legs are the two mediators, strictly. / 阳性对照：两条腿都是两个中介，严格来说。 *)
Definition control_to_is_mediator :
  to (mod_first_isomorphism_theorem f)
    = mquot_med (KernelSub f) (mod_image_elem f) := eq_refl.

Definition control_from_is_mediator :
  from (mod_first_isomorphism_theorem f)
    = mod_image_med f (mquot_elem (KernelSub f)) := eq_refl.

Fail Definition probe_triangle_strict :
  to (mod_first_isomorphism_theorem f) ∘ mquot_proj (KernelSub f)
    = mod_image_cores f := eq_refl.

(* ...and the `≈` form, which is what the file states. / ...以及 `≈` 形式，这就是文件中所说明的。 *)
Definition control_triangle_equiv :
  to (mod_first_isomorphism_theorem f) ∘ mquot_proj (KernelSub f)
    ≈ mod_image_cores f :=
  mod_first_isomorphism_triangle f.

End TriangleBoundary.

(**
** (4) Quotienting a ring by the total ideal is not the zero ring
       on the nose

    Instance/Rng/Quotient.v states [rquot_total_one_is_zero] -- that
    1 ≈ 0 in R/R -- and says the quotient is the zero ring "up to the
    identification [rquot_total_collapses] supplies".  That wording is
    deliberate: the carrier of R/R is R's, not [poly_unit], so no
    equality of [RingObject]s is available and none is claimed.

    Stripped, this reports a conversion failure between the two
    [RingObject] records; the carriers alone already differ.

--------
** (4) 将一个环按其全理想取商并不严格等于零环

Instance/Rng/Quotient.v中指出 [rquot_total_one_is_zero] —— 即在R/R中1 ≈ 0 —— 并且说明商环是零环“在[rquot_total_collapses]提供的同一性下”。这种措辞是故意的：R/R的载体是R的元素，而不是[poly_unit]，因此不存在[RingObject]的等式，也未声称存在。

简而言之，这报告了两个[RingObject]记录之间的转换失败；仅载体就已经不同。
*)

Section ZeroRingBoundary.

Context {R : RingObject}.

Fail Definition probe_total_is_zero_ring :
  QuotientRing (TotalIdeal R) = Zero_Ring := eq_refl.

(*
POSITIVE CONTROL: what IS true, and strictly -- the carrier of the
   quotient is R's own.

--------
阳性对照：什么是真实的，并且严格来说——商的载体是R自己的。
*)
Definition control_total_carrier :
  carrier (rig_setoid (QuotientRing (TotalIdeal R)))
    = carrier (rig_setoid R) := eq_refl.

(* SECOND POSITIVE CONTROL: the `≈`-level statement the file makes. / 第二个阳性对照：文件所作的 `≈` 级别声明。 *)
Definition control_total_one_is_zero :
  rig_one (QuotientRing (TotalIdeal R))
    ≈ rig_zero (QuotientRing (TotalIdeal R)) :=
  rquot_total_one_is_zero R.

End ZeroRingBoundary.

(**
** Positive controls for the two universal elements

    Not boundaries, but guards: these are the [eq_refl] claims the two
    principal files make about their own packaging, restated here so
    that a change to [AUniversalElement] which silently rebuilt the
    mediators would break this file too.

--------
** 两个通用元素的阳性对照

不是边界，而是保护：这是两个主要文件对其自身封装的 [eq_refl] 声明，这里重新表述，以便对 [AUniversalElement] 的更改如果悄悄重建了中介者，也会破坏此文件。
*)

Definition control_mod_universal_elem {R : RingObject} {M : RModObject R}
  (S : Submodule M) :
  `1 (@aue_elem _ (MKillsFunctor S) (QuotientMod S)
        (mquot_universal_element S)) = mquot_proj S := eq_refl.

Definition control_rng_universal_elem {R : RingObject} (I : Ideal R) :
  `1 (@aue_elem _ (RKillsFunctor I) (QuotientRing I)
        (rquot_universal_element I)) = rquot_proj I := eq_refl.

(*
And the ring-side reading of a left ideal's relation as the two-sided
   one, which Instance/Rng/Quotient.v claims by convertibility.

--------
以及把左理想关系作双边关系的环边读法，这是 Instance/Rng/Quotient.v 所声称的可转换性。
*)
Definition control_lquot_is_rquot {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) :
  lquot_rel (Ideal_LeftIdeal I) x y = rquot_rel I x y := eq_refl.
