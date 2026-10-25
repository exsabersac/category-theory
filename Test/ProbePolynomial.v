(**
* Boundary probes for the polynomial ring

    Companion to Instance/Rng/Polynomial.v and Instance/Rng/Pointed.v
    (issue #309, Mac Lane §III.1 Exercise 7, Awodey §9.3 Example 9.10,
    Riehl §2.1 Example 2.1.5(v) and §2.3 Example 2.3.4).  Those files
    make strength claims of two different grades — some definitional,
    some only up to [≈] — and the negative side of each is a boundary no
    in-tree consumer would notice breaking.  They are pinned here.  **If
    the [Fail] commands below stop failing, this file breaks the build.**

    Every negative is paired with a positive control that must SUCCEED: a
    [Fail] alone passes just as happily when a name has been renamed out
    from under it.  The instrument itself was checked out of band —
    wrapping [Fail] around a succeeding command reports "The command has
    not failed!" and stops compilation — and each negative below was
    compiled once with the [Fail] stripped, to confirm the error is the
    intended one and not a syntax, scope or resolution error.  Where the
    stripped error is NOT of the form "cannot unify" or "Unable to
    unify", the actual message is quoted at the probe.

    The import list below is Instance/Rng/Pointed.v's, in that file's
    order: a shortened or reordered prefix produces different errors and
    would make the probes report the wrong thing.

    THE THREE BOUNDARIES.

    (1) THE EXTENSION PRESERVES + AND · DEFINITIONALLY, BUT 0 AND 1 ONLY
    UP TO [≈].  [peval] is a fixpoint whose clauses ARE the additive and
    multiplicative homomorphism laws, so those two obligations close by
    [reflexivity].  The zero of K[x] is [pt_const (rig_zero K)], not a
    former of its own, so the fold returns the structure map's value at
    K's zero and reaching the target's zero is that map's own
    preservation law.  The header of Instance/Rng/Polynomial.v measures
    this; §1 pins it.  NOTE the probe is stated at a VARIABLE ring and
    structure map: over ℤ with the initial map the equation does close by
    [eq_refl], because [zring S 0] reduces to [rig_zero S], so a probe
    instantiated at ℤ would report the opposite of the truth.

    (2) THE ADJUNCTION'S BACKWARD TRANSPOSE DOES NOT COMPUTE.  It is
    [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows]
    (Theory/Universal/Arrow.v) is [Qed]-opaque, so
    [poly_pointed_adj_transpose_evaluates] is stated up to [≈] and no
    [eq_refl] is claimed.  This is the same seam Instance/Mod/Free.v
    records for the counit of the free-module adjunction.

    (3) THE FREE OBJECT COMPUTES; THE UNIT COMPUTES ONLY IN ITS ACTION.
    The other side of the same boundary, and the reason (2) is a
    measurement rather than a blanket disclaimer: the left adjoint's
    object part, the point it carries and the universal arrow are all
    [eq_refl].  The unit is not — [poly_pointed_unit A] is
    [fmap[U] id ∘ arrow], a composite record — but its value at every
    coefficient is, which is the strength Instance/Rng/Pointed.v claims
    and no more.

--------
* 多项式环的边界探测

Instance/Rng/Polynomial.v 和 Instance/Rng/Pointed.v 的配套文件
（问题 #309，Mac Lane §III.1 练习 7，Awodey §9.3 示例 9.10，
Riehl §2.1 示例 2.1.5(v) 和 §2.3 示例 2.3.4）。这些文件
对强度进行了两种不同等级的声明——一些是定义性的，
一些仅达到 [≈]——每种声明的负面情况都是树内消费者
不会注意到破坏的边界。这些文件在此被固定。**如果下面的 [Fail]
命令不再失败，则此文件会破坏构建。**

每个负测试都配有一个必须成功的正向控制测试：仅使用 [Fail] 当一个名称被重命名时也能顺利通过。仪器本身已在带外检查——在一个成功的命令周围包裹 [Fail] 会报告“命令未失败！”并停止编译——下列每个负测试在去掉 [Fail] 后都只编译过一次，以确认错误是预期的，而不是语法、作用域或解析错误。当去掉的错误不是“无法统一”或“Unable to unify”形式时，实际消息已在探测处引用。

下面的导入列表是 Instance/Rng/Pointed.v 的，在该文件中的顺序：缩短或重新排序前缀会产生不同的错误，并会导致探测报告错误的信息。

三界。

(1) 扩展从定义上保留 + 和 ·，但 0 和 1 仅限于 [≈]。[peval] 是一个不动点，其条款是加法和乘法同态律，因此这两个义务在 [reflexivity] 时闭合。K[x] 的零是 [pt_const (rig_zero K)]，而不是它自己的前一个元素，因此 fold 返回结构映射在 K 的零上的值，而到达目标零则是该映射自身的保持律。Instance/Rng/Polynomial.v 的头部测量了这一点；§1 固定了它。注意，该探测在一个可变环和结构映射下陈述：在 ℤ 上使用初始映射，这个方程在 [eq_refl] 时闭合，因为 [zring S 0] 简化为 [rig_zero S]，因此在 ℤ 上实例化的探测将报告与事实相反的结果。

(2) 附加的逆转置无法计算。它是 [unique_obj (ump_universal_arrows …)] 和 [ump_universal_arrows]（Theory/Universal/Arrow.v）是 [Qed] 不透明的，所以 [poly_pointed_adj_transpose_evaluates] 被声明至 [≈]，没有主张 [eq_refl]。这与 Instance/Mod/Free.v 中自由模附加的余单位记录相同。

(3) 自由对象进行计算；单元仅在其动作中进行计算。
同一边界的另一面，以及(2)是测量而不是全面免责声明的原因：左伴随的对象部分、它所携带的点以及通用箭头都是 [eq_refl]。单元不是——[poly_pointed_unit A] 是 [fmap[U] id ∘ arrow]，一个复合记录——但它在每个系数的值是的，这就是 Instance/Rng/Pointed.v 所声明的强度，仅此而已。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Instance.Rng.Pointed.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(**
** Instrument check

    A deliberately true conversion in the very context the negatives use.
    If this stops holding, the negatives below are measuring the context
    and not the boundary.

--------
** 仪器检查

在消极使用的具体语境中进行有意为真的转换。如果这种情况不再成立，下面的消极因素就是在测量语境，而不是边界。
*)

Example probe_instrument (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s) :
  rig_map (poly_extend phi s Kc Hc) (@poly_x K) = s := eq_refl.

(** ** (1) Addition and multiplication compute; zero and one do not / ** (1) 加法和乘法可以计算；零和一不能 *)

(* POSITIVE CONTROLS. / 阳性对照。 *)

Example probe_extend_add (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s)
  (t u : @PTerm K) :
  rig_map (poly_extend phi s Kc Hc) (rig_add (PolyRing K) t u)
    = rig_add S (rig_map (poly_extend phi s Kc Hc) t)
                (rig_map (poly_extend phi s Kc Hc) u) := eq_refl.

Example probe_extend_mul (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s)
  (t u : @PTerm K) :
  rig_map (poly_extend phi s Kc Hc) (rig_mul (PolyRing K) t u)
    = rig_mul S (rig_map (poly_extend phi s Kc Hc) t)
                (rig_map (poly_extend phi s Kc Hc) u) := eq_refl.

(*
NEGATIVES.  Stripped of [Fail], the first reports
     (cannot unify "poly_extend phi s Kc Hc (rig_zero (PolyRing K))" and
     "rig_zero S")
   and the second the corresponding statement for [rig_one].  What is on
   the left of each is the fold's value, [phi (rig_zero K)] after one
   step of reduction; what is on the right is the target's own zero.

--------
负面。去掉 [Fail] 后，第一条报告（无法统一 "poly_extend phi s Kc Hc (rig_zero (PolyRing K))" 和 "rig_zero S"）以及第二条对应 [rig_one] 的陈述。每条左边的是折叠的值，[phi (rig_zero K)] 经过一步简化后的值；右边的是目标自身的零。
*)

Fail Example probe_extend_zero_not_eq_refl
  (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s) :
  rig_map (poly_extend phi s Kc Hc) (rig_zero (PolyRing K))
    = rig_zero S := eq_refl.

Fail Example probe_extend_one_not_eq_refl
  (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s) :
  rig_map (poly_extend phi s Kc Hc) (rig_one (PolyRing K))
    = rig_one S := eq_refl.

(* ... and both DO hold up to [≈], which is what the file claims. / ... 并且两者确实都符合 [≈]，这正是该文件所声称的。 *)

Example probe_extend_zero_up_to_equiv
  (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s) :
  rig_map (poly_extend phi s Kc Hc) (rig_zero (PolyRing K)) ≈ rig_zero S.
Proof. exact (rig_map_zero (poly_extend phi s Kc Hc)). Qed.

(*
The ℤ instance behaves the OTHER way, which is why the probes above
   are stated at a variable ring: [zring S 0] reduces to [rig_zero S].

--------
ℤ 实例的行为相反，这就是为什么上述探针在可变环上被说明：[zring S 0] 缩减为 [rig_zero S]。
*)

Example probe_zpoly_zero_does_compute :
  rig_map (zpoly_eval Int_Ring 3%Z) (rig_zero ZPoly) = rig_zero Int_Ring
  := eq_refl.

(** ** (2) The backward transpose does not compute / ** (2) 反向转置无法计算 *)

(*
Stripped of [Fail], this reports
     (cannot unify "projT1 (projT1 ((adj[poly_pointed_adjunction])⁻¹ h)) t"
     and "peval `1 (h) `2 (Q) t")
   — the opaque transpose against the evaluation fixpoint.

--------
去掉 [Fail] 后，这个报告
    （无法统一 "projT1 (projT1 ((adj[poly_pointed_adjunction])⁻¹ h)) t"
     和 "peval `1 (h) `2 (Q) t"）
   — 针对评估不动点的不透明转置。
*)

Fail Example probe_transpose_not_eq_refl (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q) (t : @PTerm (`1 A)) :
  rig_map (`1 (`1 (from (@adj _ _ _ _ poly_pointed_adjunction A Q) h))) t
    = peval (`1 h) (`2 Q) t := eq_refl.

(* POSITIVE CONTROL: the same statement up to [≈] is a theorem. / 阳性对照：同样的陈述直到 [≈] 是一个定理。 *)

Example probe_transpose_up_to_equiv (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q) (t : @PTerm (`1 A)) :
  rig_map (`1 (`1 (from (@adj _ _ _ _ poly_pointed_adjunction A Q) h))) t
    ≈ peval (`1 h) (`2 Q) t.
Proof. exact (poly_pointed_adj_transpose_evaluates A Q h t). Qed.

(** ** (3) The free object, its point, the arrow and the unit do compute / ** (3) 自由物体、其点、箭头和单位确实计算 *)

Example probe_free_object (A : CRng) : PolyPointed A = PolyPt A := eq_refl.

Example probe_free_point (A : CRng) :
  `2 (PolyPointed A) = @poly_x (`1 A) := eq_refl.

Example probe_universal_arrow (A : CRng) :
  @arrow _ _ A CRngPt_Forget (poly_pointed_universal_arrow A)
    = poly_pointed_arrow A := eq_refl.

Example probe_unit (A : CRng) (c : carrier (rig_setoid (`1 A))) :
  rig_map (`1 (poly_pointed_unit A)) c = @pt_const (`1 A) c := eq_refl.

(*
... but only its ACTION.  The unit is [fmap[U] id ∘ arrow], whose
   underlying homomorphism is the composite RECORD
   [rig_hom_compose rig_hom_id (poly_const _)], and no amount of
   agreement on elements makes that the inclusion's own record.
   Stripped of [Fail] this reports
     (cannot unify "poly_pointed_unit A" and "poly_pointed_arrow A").

--------
... 但只有它的动作。该单元是 [fmap[U] id ∘ arrow]，其底层同态是复合 RECORD [rig_hom_compose rig_hom_id (poly_const _)]，且无论对元素达成多少一致，都不能使其成为该包含自身的记录。去掉 [Fail] 后，这会报告 (无法统一 "poly_pointed_unit A" 和 "poly_pointed_arrow A")。
*)

Fail Example probe_unit_not_the_arrow (A : CRng) :
  poly_pointed_unit A = poly_pointed_arrow A := eq_refl.

(*
POSITIVE CONTROL for that negative: the two ARE equal as morphisms of
   [CRng], which is an equation up to [≈] and holds.

--------
对于那个阴性样本的阳性对照：作为 [CRng] 的态射，这两个是相等的，这是一个在 [≈] 下的方程，并且成立。
*)

Example probe_unit_equiv_arrow (A : CRng) :
  poly_pointed_unit A ≈ poly_pointed_arrow A.
Proof. intro c; reflexivity. Qed.

(**
** A closing negative of a different kind

    The universal element of [Rng_Forget] is the indeterminate on the
    nose, but the indeterminate is NOT the zero of ℤ[x] — the
    construction does not collapse.  The first is [eq_refl]; the second
    is a refutation, not a conversion, so it is stated as a theorem and
    not as a [Fail]: a [Fail] would only record that the two terms are
    not convertible, which is far weaker than their being provably
    distinct in the setoid.

--------
** 一种不同类型的结论性否定

[Rng_Forget] 的普遍元素是在鼻子上的不确定量，但该不确定量并不是 ℤ[x] 的零——该构造不会塌缩。前者是 [eq_refl]；后者是一个反驳，而不是一个转换，因此它被陈述为定理，而不是 [Fail]：[Fail] 只会记录两个项不可互换，这远不如它们在集合体中可证明为不同那么强。
*)

Example probe_universal_element_is_x :
  @aue_elem Rng Rng_Forget ZPoly zpoly_universal_element = @poly_x Int_Ring
  := eq_refl.

Example probe_x_is_not_zero :
  (@poly_x Int_Ring ≈ rig_zero ZPoly) → False.
Proof. exact zpoly_x_nonzero. Qed.
