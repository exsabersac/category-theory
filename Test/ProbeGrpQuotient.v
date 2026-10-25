(**
* Boundary probes for the quotient group and the isomorphism theorems

    Companion to Instance/Grp/Quotient.v, Instance/Grp/Quotient/Isomorphism.v
    and Instance/Grp/Quotient/Colimit.v (issue #313, Mac Lane §III.1
    construction 5 and Exercise 4; Awodey §4.2 Theorem 4.4 and
    Corollary 4.5; Riehl §3.1 Example 3.1.25).  Those files make four
    strength claims whose negative side is a conversion or a universe
    boundary.  A measurement made outside the tree would not be noticed by
    a refactor, so it is pinned here.  **If the [Fail] commands below stop
    being rejected, this file breaks the build.**

    Each negative is paired with a positive control that must SUCCEED, for
    the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone
    passes just as happily when a name has been renamed out from under it.
    The instrument itself was checked — wrapping [Fail] around a
    succeeding command aborts compilation with "The command has not
    failed!" — and that check was not hypothetical here: an earlier draft
    wrote the three conversion negatives as [Fail Example ... : T.], which
    guards only the STATEMENT and not the proof, and the build reported
    that message at the first of them.  They are written as
    [Fail Definition ... := eq_refl] below, so that what is rejected is
    the elaboration of the term.  Each negative was also compiled once
    with the [Fail] stripped, to confirm the rejection is the intended one
    and not a syntax, scope or resolution error: three "Unable to unify"
    conversion errors, and one genuine universe inconsistency naming the
    declared universe, "Cannot enforce Set = big".  (Since #450 that
    fourth negative is a control; boundary (4) below says why.)

    The import list below is the union of the three target files' own
    lists, in their order.  That matters: a short prefix would leave the
    coercions and instances unresolved and the negatives would then be
    reported as illegal applications rather than as the conversion errors
    they are, which is a probe that passes for the wrong reason.

    THE FOUR BOUNDARIES.

    (1) THE KERNEL SUBGROUP IS NOT THE PRE-EXISTING KERNEL GROUP.
    Instance/Grp/Quotient.v's [KernelNS_carrier_is_Grp_kernel] records
    that [SubgroupGrp (KernelNS h)] and Instance/Grp.v's [Grp_kernel h]
    have the same CARRIER by [eq_refl].  The whole records are NOT
    convertible, the group-law fields being different proof terms
    ([SubgroupGrp] is [Program]-built, [Grp_kernel] is built by
    [unshelve notypeclasses refine]).  Negative 1 pins that, so the
    carrier-level claim is not silently read as a record-level one.

    (2) THE MEDIATOR'S TRIANGLE IS `≈`, NOT LEIBNIZ.
    [quot_med_commutes] states [quot_med N x ∘ quot_proj N ≈ `1 x] and
    proves it pointwise by [reflexivity] — the projection being the
    identity function, the two homomorphisms agree at every element.  They
    are nevertheless distinct RECORDS: the composite rebuilds the
    unit-preservation and multiplication-preservation fields.  Negative 2
    pins the distinction, which is exactly the `≈`/`=` discipline the
    house rules ask for.

    (3) THE IMAGE'S CLOSURE WITNESSES DO NOT REDUCE.
    Instance/Grp/Epi.v's [GrpImage_unit], [GrpImage_mul] and
    [GrpImage_inv] are [Qed]-opaque, so the preimage carried by the group
    operations of [ImageGrp] is not accessible to computation.  That is
    why Isomorphism.v's [image_med] discharges its unit and product laws
    through [image_med_wd] — comparing h-images — rather than by
    unfolding.  Negative 3 pins the opacity; if those lemmas were ever
    made transparent this probe would break and the comment in
    [image_med_wd] would need revisiting.

    (4) ZERO MORPHISMS IN [Grp] WERE CONFINED TO [Set] (until #450; see
    the correction closing this paragraph).
    [Grp_trivial] elaborates at [GrpObject@{u u Set}] and hence [Grp_Zero]
    at [ZeroObject@{u Set} Grp@{u Set}], even though
    the donor [unit_setoid@{t u}] (Lib/Setoid.v) is polymorphic in
    exactly the pinned argument.  So every [IsCokernel] and every
    coequalizer-against-zero statement about [Grp] — the whole of
    Instance/Grp/Quotient/Colimit.v — holds only for groups whose carriers
    live in [Set].  THE PIN IS THE DONOR'S, not this development's, and it
    is not shown unavoidable; it has the shape of the
    [Build_Quiver_Standard_Eq] erratum that issue #300 lifted.  Negative 4
    is the guard: if a later change to Instance/Grp.v lifts it, this probe
    breaks and Colimit.v's disclosure should be deleted.  (An earlier
    revision of this paragraph quoted [GrpObject@{u Set u}] and cited
    Instance/Grp.v; re-measured after the PR "algebraic carriers are
    sets" (2026-09-17), which permuted [GrpObject]'s universe roles from
    (carrier, proof, aux) to (aux, carrier, proof).  The same reading, one
    position over; the pin and every negative below are unchanged.)
    CORRECTION (#450): the guard did its job.  #450 annotated
    Instance/Grp.v's zero-object constants in place ([Grp_trivial@{p} :
    GrpObject@{p p p}], [Grp_Zero@{u p} : ZeroObject@{u p} Grp@{u p}]),
    the build then stopped at Negative 4 with Rocq's report that the
    guarded command had been accepted, and it is kept, without the guard,
    as a CONTROL in section [BigZero] below.
    Zero morphisms in [Grp] are no longer confined to [Set], and
    Instance/Grp/Quotient/Colimit.v's disclosure is corrected in place.

    WHAT IS DELIBERATELY *NOT* PROBED.  The positive controls in
    section [Positive] include the two strict identifications that DO
    hold — the isomorphism of the first isomorphism theorem has the two
    mediators as its legs, by [eq_refl] — because those are the claims a
    refactor is most likely to break silently.

--------
* 商群和同构定理的边界探讨

《Instance/Grp/Quotient.v, Instance/Grp/Quotient/Isomorphism.v 和 Instance/Grp/Quotient/Colimit.v 的配套文件》（问题 #313，Mac Lane §III.1 构造 5 和练习 4；Awodey §4.2 定理 4.4 和推论 4.5；Riehl §3.1 示例 3.1.25）。这些文件提出了四个强度声明，它们的负面方面是转换或宇宙边界。在树外进行的测量将不会被重构器注意到，因此这里进行了固定。**如果下面的 [Fail] 命令不再被拒绝，此文件将导致构建失败。**

每个阴性测试都配有一个必须成功的阳性对照，其原因如 Test/ProbeQuiverConstructions.v 所示：单独的 [Fail] 即使在名称被重新命名后仍能同样顺利地通过。工具本身也经过检查——在成功命令周围包裹 [Fail] 会因“命令未失败！”而中止编译——且该检查在此并非假设：早期的一个草稿将三个转换阴性测试写为 [Fail Example ... : T.]，它只保护语句而不保护证明，构建在第一个测试上就报告了该消息。它们被写为下面的 [Fail Definition ... := eq_refl]，因此被拒绝的是该术语的展开。每个负例也编译过一次，去掉了 [Fail]，以确认被拒绝的是预期的，而不是语法、作用域或解析错误：三个“无法统一”的转换错误，以及一个真正的宇宙不一致错误，命名了声明的宇宙，“无法强制 Set = big”。（自 #450 起，第四个负例是一个控制；下面的边界 (4) 说明原因。）

下面的导入列表是三个目标文件自身列表的并集，按它们的顺序排列。这很重要：如果前缀太短，会导致强制转换和实例未被解析，然后负号将被报告为非法应用，而不是它们本来的转换错误，这是一种以错误理由通过的检查。

四个边界。

(1) 核子子群不是预先存在的核子群。
Instance/Grp/Quotient.v 中的 [KernelNS_carrier_is_Grp_kernel] 记录了 [SubgroupGrp (KernelNS h)] 和 Instance/Grp.v 中的 [Grp_kernel h] 通过 [eq_refl] 具有相同的 CARRIER。整个记录不可转换，因为群运算字段是不同的证明项（[SubgroupGrp] 是由 [Program] 构建的，[Grp_kernel] 是由 [unshelve notypeclasses refine] 构建的）。负 1 说明了这一点，因此载体层级的声明不会被默认为记录层级的声明。

(2) 中介者的三角形是 `≈`，不是莱布尼茨。  
[quot_med_commutes] 陈述了 [quot_med N x ∘ quot_proj N ≈ `1 x] 并通过 [reflexivity] 对其逐点证明 —— 投影是恒等函数，这两个同态在每个元素上都一致。 但它们仍然是不同的 RECORDS：复合体重建了单位保持和乘法保持字段。 负2指出了这种区别，这正是家庭规则要求的 `≈`/`=` 规范。

(3) 图像的闭包见证不会减少。  
Instance/Grp/Epi.v 中的 [GrpImage_unit]、[GrpImage_mul] 和 [GrpImage_inv] 是 [Qed]-不透明的，因此由 [ImageGrp] 群运算携带的前像无法进行计算。这就是为什么 Isomorphism.v 中的 [image_med] 通过 [image_med_wd] —— 比较 h-像 —— 来完成其单位和乘法律，而不是通过展开。负 3 固定了不透明性；如果那些引理曾被设为透明，这个探测将会失效，[image_med_wd] 中的注释也需要重新审视。

(4) [Grp] 中的零态态射仅限于 [Set]（直到 #450；见本段结束的更正）。[Grp_trivial] 在 [GrpObject@{u u Set}] 处进行了阐述，因此 [Grp_Zero] 在 [ZeroObject@{u Set} Grp@{u Set}] 处同样成立，尽管捐赠者 [unit_setoid@{t u}]（Lib/Setoid.v）在精确固定的参数上是多态的。所以每一个 [IsCokernel] 和每一个关于 [Grp] 的零态余等化声明——整个 Instance/Grp/Quotient/Colimit.v——仅对其载体位于 [Set] 的群体成立。PIN 是捐赠者的，而不是这个开发的，而且它并非不可避免；它具有 [Build_Quiver_Standard_Eq] 勘误表的形状，该勘误在第 300 期中被提出。负 4 是保护：如果稍后对 Instance/Grp.v 的更改解除它，这个探针会失效，并且 Colimit.v 的披露应当被删除。（本段的早期修订引用了 [GrpObject@{u Set u}] 并引用了 Instance/Grp.v；在 PR “代数载体是集合”（2026-09-17）之后重新测量，它将 [GrpObject] 的宇宙角色从 (carrier, proof, aux) 转换为 (aux, carrier, proof)）。相同的读取，位置向前一个；针和下面的每一个负值保持不变。)
更正（#450）：警卫完成了它的工作。#450 注释了实例/Grp.v 中的零对象常量（[Grp_trivial@{p} : GrpObject@{p p p}], [Grp_Zero@{u p} : ZeroObject@{u p} Grp@{u p}]），然后在负值4处构建停止，Rocq 报告说受保护的命令已被接受，它被保留在下面的 [BigZero] 部分作为一个 CONTROL，没有警卫。[Grp] 中的零态射不再仅限于 [Set]，实例/Grp/Quotient/Colimit.v 的披露已在原位修正。

刻意*不*探测的内容。第 [Positive] 节中的阳性对照包括两个确实成立的严格识别——第一个同构定理的同构有两个中介作为其支柱，由 [eq_refl] 提供——因为这些是重构最可能悄然破坏的断言。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Isomorphism.
Require Import Category.Theory.Universal.Element.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Regular.
Require Import Category.Structure.Kernel.
Require Import Category.Instance.Grp.Quotient.Colimit.

Generalizable All Variables.

(** ** Negative 1: the kernel subgroup group is not [Grp_kernel] / ** 负1：内核子群组不是 [Grp_kernel] *)

(* POSITIVE CONTROL: the carriers ARE convertible. / 阳性对照：载体是可转换的。 *)
Example control_kernel_carrier {G K : GrpObject} (h : G ~{Grp}~> K) :
  carrier (SubgroupGrp (KernelNS h)) = carrier (Grp_kernel h).
Proof. reflexivity. Qed.

(* NEGATIVE: the whole records are not. / 消极：整个记录都不是。 *)
Fail Definition negative_kernel_record {G K : GrpObject} (h : G ~{Grp}~> K) :
  SubgroupGrp (KernelNS h) = Grp_kernel h := eq_refl.

(** ** Negative 2: the mediator triangle is `≈` and not Leibniz / ** 负 2：中介三角形是 `≈` 而不是莱布尼茨 *)

(* POSITIVE CONTROL: the `≈` form holds, pointwise by reflexivity. / 阳性对照：`≈` 形式成立，通过自反性逐点成立。 *)
Example control_med_triangle {G K : GrpObject} (N : NormalSubgroup G)
  (x : Kills N K) : quot_med N x ∘ quot_proj N ≈ `1 x.
Proof. exact (quot_med_commutes N x). Qed.

(* NEGATIVE: the Leibniz form does not. / 消极：莱布尼茨形式不适用。 *)
Fail Definition negative_med_triangle {G K : GrpObject} (N : NormalSubgroup G)
  (x : Kills N K) : quot_med N x ∘ quot_proj N = `1 x := eq_refl.

(** ** Negative 3: [GrpImage_unit] is opaque / ** 负 3：[GrpImage_unit] 是不透明的 *)

(*
POSITIVE CONTROL: the equation the opaque lemma carries IS accessible,
   which is what [image_med] uses instead of the witness.

--------
阳性对照：不透明引理携带的方程是可访问的，这就是 [image_med] 使用它而不是见证的原因。
*)
Example control_image_unit_equation {G K : GrpObject} (h : G ~{Grp}~> K) :
  grp_map h (`1 (GrpImage_unit h)) ≈ grp_unit K.
Proof. exact (`2 (GrpImage_unit h)). Qed.

(* NEGATIVE: the witness itself does not reduce to the unit. / 否定：该证据本身不能化为单位。 *)
Fail Definition negative_image_unit_witness {G K : GrpObject}
  (h : G ~{Grp}~> K) : `1 (GrpImage_unit h) = grp_unit G := eq_refl.

(** ** Boundary 4, lifted by #450: zero morphisms in [Grp] above [Set] / ** 边界 4，由 #450 提出：在 [Grp] 中高于 [Set] 的零态射 *)

Monomorphic Universe big.
Monomorphic Constraint Set < big.

(*
POSITIVE CONTROL: the quotient machinery itself carries no such pin --
   [QuotientGrp] and its universal element are formable at a group whose
   universes are declared strictly above [Set].  This is the half that
   said the pin belonged to [Grp_Zero] (until #450 lifted it) and not to
   this development.

--------
阳性对照：商结构本身不携带这样的销——[QuotientGrp]及其通用元素可以在其宇宙严格高于[Set]的群上形成。这是说该销属于[Grp_Zero]（直到#450将其解除）而不属于此开发部分的一半。
*)
Section BigCarrier.

Context {G : GrpObject@{big big big}}.
Context (N : NormalSubgroup@{big big big big} G).

Definition control_big_quotient : GrpObject@{big big big} := QuotientGrp N.

Definition control_big_projection : G ~{Grp}~> control_big_quotient :=
  quot_proj N.

Definition control_big_universal :
  AUniversalElement (KillsFunctor N) (QuotientGrp N) :=
  quot_universal_element N.

Definition control_big_kernel {K : GrpObject@{big big big}}
  (h : G ~{Grp}~> K) : NormalSubgroup G := KernelNS h.

Definition control_big_first_iso {K : GrpObject@{big big big}}
  (h : G ~{Grp}~> K) :
  QuotientGrp (KernelNS h) ≅[Grp] ImageGrp h :=
  first_isomorphism_theorem h.

End BigCarrier.

(*
CONTROL, formerly the NEGATIVE of boundary (4): the zero morphism at the
   same universes.  Until #450 this was the guarded negative
   [negative_big_zero], and stripping the guard reported "Cannot enforce
   Set = big"; since
   #450 annotated [Grp_Zero] it is accepted.

--------
控制，原先的边界的负数（4）：在相同宇宙的零态射。在 #450 之前，这是受保护的负数 [negative_big_zero]，去掉保护会报告“无法强制 Set = big”；自 #450 为 [Grp_Zero] 添加注解后，它被接受。
*)
Section BigZero.

Context {G K : GrpObject@{big big big}}.

Definition control_big_zero : G ~{Grp}~> K := @zero_mor Grp Grp_Zero G K.

End BigZero.

(** ** Positive controls for the strict identifications that DO hold / ** 严格鉴定中确实成立的阳性对照 *)

Section Positive.

(*
The comparison isomorphism of the first isomorphism theorem has the two
   mediators as its legs, by convertibility: the universal-element
   machinery of Theory/Universal/Element.v rebuilds neither.

--------
第一同构定理的比较同构具有两个中介作为其两条支柱，通过可转换性：Theory/Universal/Element.v 的通用元素机制两者都未重建。
*)
Example positive_first_iso_to {G K : GrpObject} (h : G ~{Grp}~> K) :
  to (first_isomorphism_theorem h) = quot_med (KernelNS h) (image_elem h).
Proof. reflexivity. Qed.

Example positive_first_iso_from {G K : GrpObject} (h : G ~{Grp}~> K) :
  from (first_isomorphism_theorem h) = image_med h (quot_elem (KernelNS h)).
Proof. reflexivity. Qed.

(* The universal element's underlying homomorphism IS the projection. / 泛元素的基础同态是投影。 *)
Example positive_universal_elem {G : GrpObject} (N : NormalSubgroup G) :
  `1 (@aue_elem _ (KillsFunctor N) (QuotientGrp N) (quot_universal_element N))
    = quot_proj N.
Proof. reflexivity. Qed.

(*
THE STRENGTH THAT WAS SAVED, AND THE RELATION THAT CARRIES IT.

   The PR "algebraic carriers are sets" (2026-09-17) truncated three
   relations in the Grp layer -- Test/ProbeGrpProp.v pins those from both
   sides -- and deliberately left Instance/Grp/Epi.v's [grp_coset_rel]
   alone, because truncating it would have cost
   [transposition_decides_image] its conclusion: the full
   [GrpImageDecidable f], and not a double negation of it.  Nothing in
   the tree guarded that decision until these two controls; an earlier
   revision of Test/ProbeGrpProp.v deferred it to "Test/ProbeGrpEpi*.v",
   a file that has never existed.

   The first control pins the relation's SORT -- a [Type]-valued
   [crelation], measured as [grp_coset_rel ... : crelation@{u u} H] by
   [About] under [Set Printing Universes] -- and the second pins the
   theorem's WHOLE statement, hypothesis and conclusion together, so that
   a later truncation of [grp_coset_rel], or a weakening of the
   conclusion to a [¬¬] form, breaks this file rather than passing
   silently.

--------
被保存的力量，以及承载它的关系。

PR“代数承载体是集合”（2026-09-17）截断了 Grp 层中的三个关系——Test/ProbeGrpProp.v 固定了两边的关系——并故意保留了 Instance/Grp/Epi.v 中的 [grp_coset_rel]，因为截断它会让 [transposition_decides_image] 失去其结论：完整的 [GrpImageDecidable f]，而不是它的双重否定。在这棵树中没有任何东西守护这个决定，直到这两个控制点；Test/ProbeGrpProp.v 的早期版本将其推迟到“Test/ProbeGrpEpi*.v”，该文件从未存在过。

第一个控制固定关系的排序——一个 [Type] 值的 [crelation]，由 [About] 在 [Set Printing Universes] 下测量为 [grp_coset_rel ... : crelation@{u u} H]——第二个则将定理的整体陈述、假设和结论固定在一起，以便稍后对 [grp_coset_rel] 进行截断，或者将结论削弱为 [¬¬] 形式时，会破坏此文件，而不是静默通过。
*)
Example positive_grp_coset_rel_is_type_valued
  {G H : GrpObject} (f : G ~{Grp}~> H) : crelation H :=
  grp_coset_rel f.

Example positive_transposition_decides_image_full
  {G H : GrpObject} (f : G ~{Grp}~> H)
  (t : SetoidPermutation (CosetPlusPtSetoid f))
  (Hbase : ∀ c, GrpImage f c →
             @equiv _ (is_setoid (CosetPlusPtSetoid f))
               (sperm_to t (inl c)) (inr ttt)) :
  GrpImageDecidable f :=
  transposition_decides_image f t Hbase.

End Positive.
