Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

(*
   * * Rng: the category of unital rings

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.7
   (printed p. 25): the roll-call of large categories includes Rng, all
   small (unital) rings with the ring homomorphisms preserving the
   multiplicative unit [maclane:I.7:def1, maclane:I.7:construction2];
   §I.5 Exercise 4 (printed p. 21): the inclusion ℤ → ℚ is an epi of
   Rng that is not surjective [maclane:I.5:ex4].
   nLab: https://ncatlab.org/nlab/show/Ring
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_rings

   NAMING (per the issue's QA audit).  This category keeps Mac Lane's
   name [Rng] — his abbreviation for the category of UNITAL rings — and
   it IS Theory/Algebra/Rig.v's category [Ring], definitionally: a
   [RingObject] there is a rig with additive inverses, i.e. exactly a
   unital (not necessarily commutative) ring over a setoid carrier, and
   its homomorphisms are the [RigHom]s, which preserve 0, +, 1 and · —
   unit preservation is a FIELD, as Mac Lane requires — while
   preservation of negation is the theorem [RigHom_neg].  The set-level
   CLASS keeps the name [Ring]/[RingObject] (seventeen Seven Sketches
   issues consume it under that name); the CATEGORY answers to both,
   with [Rng] the Mac Lane-side entry point.  The category of
   NON-unital rings is Instance/Rg.v's [Rg], with the forgetful
   functor [Rng_Forget_Rg : Rng ⟶ Rg] there, so the direction is
   unambiguous.  That file also proves the two categories are not
   interchangeable: [Rg] has a ZERO object (the zero rng is initial
   AND terminal, a rng homomorphism not being required to preserve 1)
   where [Rng] has ℤ initial and the zero ring terminal, which do not
   coincide.

   CONTENT.  Beyond the category itself: the forgetful functors to [Ab]
   (the additive abelian group, Instance/Ab.v) and to [Sets]; the zero
   ring is terminal ([Rng_Terminal_zero]); the integers are initial
   ([Rng_Initial_Z] — the ring-side counterpart of Rig.v's ℕ-initiality,
   with the unique homomorphism z ↦ z·1 built by sign case analysis and
   verified through the hand-rolled Type-valued recursor [Z_peano_rect]
   below — the stdlib offers only the Prop-valued [Z.peano_ind]); the
   full subcategory
   [CRng] of commutative rings (needed downstream by the matrix-category
   and GL_n issues); injections are monic and surjections are epi; and
   the headline separation, Mac Lane's Exercise I.5.4:

   [ZtoQ_epi_not_surjective] — the inclusion ℤ → ℚ is an epimorphism
   of [Rng] although it is not surjective.

   The epi half is the standard argument made constructive: a ring
   homomorphism out of ℚ is determined by its values on the image of ℤ,
   because g (1/b) is a two-sided multiplicative inverse of g b and
   two-sided inverses are unique; no fraction ever needs to be chosen,
   only cancelled.  The non-surjectivity half exhibits 1/2.

   SCOPE NOTE, disclosed, and a DEFERRAL SINCE DISCHARGED.  "Monics are
   exactly the injections" ships here in the direction that needs no new
   machinery: injective ⇒ monic ([rng_injective_monic]), plus
   surjective ⇒ epi ([rng_surjective_epic], whose converse is REFUTED by
   the headline theorem).  The converse monic ⇒ injective requires
   probing with the free ring on one generator — the polynomial ring
   ℤ[x] — exactly as Instance/Sets.v probes with the singleton and
   Instance/Top.v with the point space.  That probe did not exist when
   this file was written and the result was deferred here; it exists
   now, and the result is PROVED, in Instance/Rng/Polynomial.v.

   What landed is STRONGER than what was deferred, in two respects worth
   stating rather than leaving for a reader to notice.  First, it is a
   BICONDITIONAL: [rng_monic_iff_injective] pairs the new
   [rng_monic_injective] with this file's [rng_injective_monic], so
   "monics are exactly the injections" is now the whole sentence and not
   half of it.  Second, it holds over ALL of [Rng] and not merely over
   [CRng].  The evaluation homomorphism out of ℤ[x] needs its target
   element to commute with the image of the coefficients, which over an
   arbitrary non-commutative ring is not automatic; Polynomial.v's
   [zring_central] supplies it, the integers being central in every
   unital ring, so ℤ[x] is free on one generator in the category of all
   unital rings and the probe is available at every object of [Rng].

   The statement cannot live in this file: ℤ[x] is built downstream of
   [Rng_Initial_Z] and [CRng], both of which it consumes, so it lives
   where its probe does.  (The issue's own verification list names
   [Rng], [CRng], [Rng_Initial_Z], [Rng_Terminal_zero] and
   [ZtoQ_epi_not_surjective] as the audited artifacts.) 

   --------
   * * Rng：幺环的范畴

   Mac Lane，《为工作数学家准备的范畴论》，第二版，第 I.7 节
   （印刷版第 25 页）：大范畴的点名包含 Rng，即所有小型（幺）环及保持乘法单位的环同态  [maclane:I.7:def1, maclane:I.7:construction2]；
   第 I.5 节练习 4（印刷版第 21 页）：包含映射 ℤ → ℚ 是 Rng 的一个满射（epi），但不是满函数  [maclane:I.5:ex4]。
   nLab： https://ncatlab.org/nlab/show/Ring
   维基百科： https://en.wikipedia.org/wiki/Category_of_rings命名（根据该问题的质量审核）。该类别保留了 Mac Lane 的名称 [Rng]——他对单元环类别的缩写——它是 Theory/Algebra/Rig.v 的类别 [Ring]，从定义上讲：那里的一 个 [RingObject] 是一个具有加法逆元的 rig，也就是说，它恰好是一个在集合体承载上的单元（不一定可交换）环，并且它的同态是 [RigHom]，它们保持 0、+、1 和 ·——单位保持是一个 FIELD，正如 Mac Lane 所要求的——而保持取负则是定理 [RigHom_neg]。集合级别的 CLASS 保留名称 [Ring] / [RingObject]（在 Seventeen Seven Sketches 的问题中以该名称使用）；CATEGORY 对两者都有响应，其中 [Rng] 是 Mac Lane 侧的入口点。非幺环的范畴是 Instance/Rg.v 中的 [Rg]，其处有遗忘函子 [Rng_Forget_Rg : Rng ⟶ Rg]，因此方向是明确的。该文件还证明了这两个范畴不能互换：[Rg] 具有零对象（零环既是初对象又是终对象，并且环同态不要求保持 1），而 [Rng] 以 ℤ 为初对象，零环为终对象，它们不重合。内容。超越类别本身：到 [Ab]（加性阿贝尔群，Instance/Ab.v）和 [Sets] 的遗忘函子；零环是终对象（[Rng_Terminal_zero]）；整数是初对象（[Rng_Initial_Z] —— 对应于 Rig.v 中 ℕ 的初性，在环的一侧，通过符号分情况分析构建唯一同态 z ↦ z·1，并通过下面自制的类型值递归器 [Z_peano_rect] 验证 —— 标准库仅提供命题值的 [Z.peano_ind]）；交换环的完全子类别 [CRng]（后续矩阵类别和 GL_n 问题需要）；单射是单态，满射是余单态；以及重点分离，Mac Lane 的练习 I.5.4：

   [ZtoQ_epi_not_surjective] —— 包含映射 ℤ → ℚ 是 [Rng] 的一个余单态，尽管它不是满射。上同态部分是构造性地提出的标准论证：来自 ℚ 的环同态由其在 ℤ 的像上的取值确定，因为 g(1/b) 是 g b 的双边乘法逆元，而双边逆元是唯一的；从不需要选择分数，只需约掉即可。非满射部分展示了 1/2。范围说明，已披露，并且在出院后延期。 "Monics 就是注射" 在这里的方向不需要新机械：单射 ⇒ monic（[rng_injective_monic]），再加上满射 ⇒ epi（[rng_surjective_epic]，其逆命题已被标题定理驳斥）。逆命题 monic ⇒ 单射需要使用单生成元的自由环进行探测——多项式环 ℤ [x]——正如 Instance/Sets.v 使用单元集合进行探测，Instance/Top.v 使用点空间进行探测一样。在编写此文件时，该探测尚不存在，因此结果在此处被延期；现在它已经存在，结果已在 Instance/Rng/Polynomial.v 中被证明。已经实现的比被推迟的在两个值得说明的方面更强，而不是留给读者去注意。首先，它是一个双向条件：[rng_monic_iff_injective] 将新的 [rng_monic_injective] 与这个文件的 [rng_injective_monic] 配对，因此“单子完全是注入”现在是整个句子，而不是其一半。第二，它适用于整个 [Rng]，而不仅仅是 [CRng]。从 ℤ [x] 出发的评价同态需要其目标元素与系数的像交换，这在任意非交换环上并非自动成立；Polynomial.v 的 [zring_central] 提供了它，因为整数在每个含单位环中都是中心元素，所以 ℤ [x] 在所有含单位环的范畴中是单生成自由对象，并且在 [Rng] 的每个对象上探针都是可用的。该语句不能存在于此文件中：ℤ [x] 是在 [Rng_Initial_Z] 和 [CRng] 之后构建的，它会使用这两个，所以它存在于其探针所在的位置。（该问题自身的验证列表将 [Rng]、[CRng]、[Rng_Initial_Z]、[Rng_Terminal_zero] 和 [ZtoQ_epi_not_surjective] 列为审计工件。）
*)

(* * ** The category, under Mac Lane's name / * ** 这个范畴，以麦克莱恩的名字命名 *)

Definition Rng : Category := Ring.

(** ** The forgetful functors / ** 忘记函子 *)

(*
 The additive part of a ring is an abelian group: Rig.v's [rig_cmon]
 supplies the commutative monoid, [ring_neg] the inverses. 

 --------
 一个环的加法部分是一个阿贝尔群：Rig.v 的 [rig_cmon] 提供了交换幺半群，[ring_neg] 提供了逆元。
*)
Definition ring_ab (R : RingObject) : AbObject := {|
  ab_cmon := rig_cmon R;
  ab_neg := ring_neg R;
  ab_neg_respects := ring_neg_respects R;
  ab_neg_left := ring_neg_l R
|}.

#[local] Obligation Tactic := idtac.

Program Definition Rng_Forget_Ab : Rng ⟶ Ab := {|
  fobj := ring_ab;
  fmap := fun R S f => {|
    cmon_map := rig_map f;
    cmon_map_zero := rig_map_zero f;
    cmon_map_plus := rig_map_add f
  |}
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

Program Definition Rng_Forget : Rng ⟶ Sets := {|
  fobj := fun R : RingObject => rig_setoid R;
  fmap := fun R S f => rig_map f
|}.
Next Obligation. intros R S f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros R a; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g a; simpl; reflexivity. Qed.

(** ** The zero ring is terminal / ** 零环是终端环 *)

(*
 The one-element ring: every operation returns the point.  In a ring
 with 0 ≈ 1 every element is 0, and this is it. 

 --------
 单元素环：每个运算都返回该点。在一个 0 ≈ 1 的环中，每个元素都是 0，而这就是全部。
*)
(*
 The carrier setoid is NAMED rather than written inline inside [Zero_Rig]:
 [rig_prop] below has to mention the setoid it is a [PropEquiv] of, and
 inside a [Program] record literal that setoid is still an evar when the
 field is elaborated, so the two implications cannot be checked. 

 --------
 载体集合被命名，而不是写在 [Zero_Rig] 内联：
 下面的 [rig_prop] 必须提到它是 [PropEquiv] 的集合，并且
 在 [Program] 记录字面值内部，当字段被展开时，该集合仍然是一个 evar，因此无法检查这两个蕴含关系。
*)
Program Definition zero_rig_setoid : SetoidObject := {|
  carrier := poly_unit
  ; is_setoid := {| Setoid.equiv := fun _ _ => True
                  ; Setoid.setoid_equiv := _ |}
|}.
Next Obligation. equivalence. Qed.

Program Definition Zero_Rig : RigObject := {|
  rig_setoid := zero_rig_setoid;
  rig_zero := ttt;
  rig_add := fun _ _ => ttt;
  rig_one := ttt;
  rig_mul := fun _ _ => ttt;

  (*
 The relation is [fun _ _ => True], which is already a [Prop]; the two
 implications are the identity. 

 --------
 该关系是 [fun _ _ => True]，它已经是一个 [Prop]；这两个蕴涵是恒等的。
*)
  rig_prop := @PropEquiv_of_relation poly_unit (is_setoid zero_rig_setoid)
                (fun _ _ => True) (fun _ _ h => h) (fun _ _ h => h)
|}.
Next Obligation. repeat intro; constructor. Qed.
Next Obligation. repeat intro; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.

Program Definition Zero_Ring : RingObject := {|
  ring_rig := Zero_Rig;
  ring_neg := fun _ => ttt
|}.
Next Obligation. repeat intro; constructor. Qed.
Next Obligation. intros; constructor. Qed.

(*
 The unique homomorphism into the zero ring sends everything to the
 point; every clause holds trivially in the trivial codomain. 

 --------
 到零环的唯一同态将所有元素映射到该点；在平凡的余域中，每个条款都显然成立。
*)
Program Definition rng_to_zero (R : RingObject) : RigHom R Zero_Ring := {|
  rig_map := {| morphism := fun _ => ttt |}
|}.
Next Obligation. repeat intro; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.
Next Obligation. intros; constructor. Qed.

#[export] Program Instance Rng_Terminal_zero : @Terminal Rng := {
  terminal_obj := Zero_Ring;
  one := rng_to_zero
}.
Next Obligation. intros R f g a; constructor. Qed.

(** ** The integers are initial / ** 整数是初始的 *)

(* The candidate ring ℤ is Rig.v's [Int_Ring]. The unique homomorphism sends z to the z-fold sum of 1, by sign case analysis over the n-fold sum [rig_iter] of Rig.v. / 候选环 ℤ 是 Rig.v 的 [Int_Ring]。唯一的同态将 z 映射为 1 的 z 倍和，通过对 Rig.v 的 n 倍和 [rig_iter] 进行符号情况分析。 *)

Definition zring (R : RingObject) (z : Z) : carrier (rig_setoid R) :=
  match z with
  | Z0 => rig_zero R
  | Zpos p => rig_iter R (Pos.to_nat p)
  | Zneg p => ring_neg R (rig_iter R (Pos.to_nat p))
  end.

(* Negation commutes with the candidate map — by construction on the positives, and by involutivity (through the Ab layer) on the negatives. / 否定与候选映射交换——在正数上通过构造实现，在负数上通过自反性（通过 Ab 层）实现。 *)
Lemma ring_neg_involutive (R : RingObject) (a : carrier (rig_setoid R)) :
  ring_neg R (ring_neg R a) ≈ a.
Proof.
  symmetry.
  apply (ab_neg_unique (ring_ab R)); simpl.
  apply (ab_neg_right (ring_ab R)).
Qed.

Lemma zring_opp (R : RingObject) (z : Z) :
  zring R (- z) ≈ ring_neg R (zring R z).
Proof.
  destruct z; simpl.
  - symmetry.
    apply (ab_neg_zero (ring_ab R)).
  - reflexivity.
  - symmetry; apply ring_neg_involutive.
Qed.

(* The Ab-layer facts, restated in ring vocabulary once so the rewrites below match syntactically. / Ab层的事实，用环的词汇重新表述一次，以便下面的重写在语法上匹配。 *)
Lemma ring_neg_r (R : RingObject) (a : carrier (rig_setoid R)) :
  rig_add R a (ring_neg R a) ≈ rig_zero R.
Proof. exact (ab_neg_right (ring_ab R) a). Qed.

Lemma ring_neg_add (R : RingObject) (a b : carrier (rig_setoid R)) :
  ring_neg R (rig_add R a b)
    ≈ rig_add R (ring_neg R a) (ring_neg R b).
Proof. exact (ab_neg_plus (ring_ab R) a b). Qed.

(* The successor law, the engine of every preservation proof below. / 继承法，是下面每个保存证明的引擎。 *)
Lemma zring_succ (R : RingObject) (z : Z) :
  zring R (Z.succ z) ≈ rig_add R (rig_one R) (zring R z).
Proof.
  destruct z; simpl.
  - reflexivity.
  - now rewrite Pos.add_1_r, Pos2Nat.inj_succ; simpl.
  - destruct p; simpl.
    + (* Zneg p~1: simpl has already exposed the successor; cancel 1 against -1 through the negation of the sum / Zneg p~1: simpl 已经暴露了继任者；取消 1 对 -1 通过求和的否定 *)
      symmetry.
      rewrite (ring_neg_add R).
      rewrite <- rig_add_assoc.
      rewrite (ring_neg_r R).
      now rewrite rig_add_zero_l.
    + (* Zneg p~0: express p~0 as succ (pred_double p) and cancel / Zneg p~0：将 p~0 表示为 succ (pred_double p) 并消去 *)
      rewrite <- Pos.succ_pred_double.
      rewrite Pos2Nat.inj_succ; simpl.
      symmetry.
      rewrite (ring_neg_add R).
      rewrite <- rig_add_assoc.
      rewrite (ring_neg_r R).
      now rewrite rig_add_zero_l.
    + (* Zneg 1: succ is 0 / Zneg 1：succ 是 0 *)
      symmetry.
      rewrite rig_add_zero_r.
      apply (ring_neg_r R).
Qed.

Lemma zring_pred (R : RingObject) (z : Z) :
  zring R (Z.pred z)
    ≈ rig_add R (ring_neg R (rig_one R)) (zring R z).
Proof.
  apply (ab_cancel_l (ring_ab R) (rig_one R)); simpl.
  rewrite <- (zring_succ R (Z.pred z)).
  rewrite Z.succ_pred.
  rewrite <- rig_add_assoc.
  rewrite (ring_neg_r R).
  now rewrite rig_add_zero_l.
Qed.

(*
 A Type-valued Peano recursor for ℤ, assembled from the positive one:
 the stdlib's [Z.peano_ind] eliminates only into [Prop], and the goals
 below are ≈-valued (Type).  The successor/predecessor conversions are
 definitional: [Z.succ (Zpos q)] computes to [Zpos (q + 1)] and
 [Pos.add q 1] to [Pos.succ q], dually on the negatives. 

 --------
 一个针对 ℤ 的类型值皮亚诺递归器，由正数 1 组装而成：
 标准库的 [Z.peano_ind] 仅消解为 [Prop] ，下面的目标为 ≈ 值（类型）。
 后继/前驱转换是定义性的：[Z.succ (Zpos q)] 计算为 [Zpos (q + 1)]，
 [Pos.add q 1] 计算为 [Pos.succ q]，对负数亦然。
*)
Definition Z_peano_rect (P : Z → Type)
  (H0 : P 0%Z)
  (HS : ∀ z, P z → P (Z.succ z))
  (HP : ∀ z, P z → P (Z.pred z)) (z : Z) : P z :=
  match z with
  | Z0 => H0
  | Zpos p => Pos.peano_rect (fun q => P (Zpos q)) (HS 0%Z H0)
                (fun q IH =>
                   eq_rect _ P (HS (Zpos q) IH) _
                     (eq_sym (Pos2Z.inj_succ q))) p
  | Zneg p => Pos.peano_rect (fun q => P (Zneg q)) (HP 0%Z H0)
                (fun q IH =>
                   eq_rect _ P (HP (Zneg q) IH) _
                     (f_equal Z.neg (Pos.add_1_r q))) p
  end.

Lemma zring_add (R : RingObject) (a b : Z) :
  zring R (a + b) ≈ rig_add R (zring R a) (zring R b).
Proof.
  revert b.
  apply (Z_peano_rect
           (fun a => ∀ b, zring R (a + b)
                            ≈ rig_add R (zring R a) (zring R b))).
  - intro b; simpl.
    now rewrite rig_add_zero_l.
  - intros x IH b.
    rewrite Z.add_succ_l.
    rewrite !zring_succ.
    rewrite IH.
    now rewrite rig_add_assoc.
  - intros x IH b.
    rewrite Z.add_pred_l.
    rewrite !zring_pred.
    rewrite IH.
    now rewrite rig_add_assoc.
Qed.

(* (-1) · x ≈ - x, needed for the multiplicative Peano step. / (-1) · x ≈ - x，这是乘法佩亚诺步骤所需的。 *)
Lemma rig_mul_neg_one (R : RingObject) (x : carrier (rig_setoid R)) :
  rig_mul R (ring_neg R (rig_one R)) x ≈ ring_neg R x.
Proof.
  apply (ab_neg_unique (ring_ab R)); simpl.
  rewrite <- (rig_mul_one_l R x) at 2.
  rewrite <- rig_distr_r.
  rewrite (ab_neg_left (ring_ab R)); simpl.
  apply rig_mul_zero_l.
Qed.

Lemma zring_mul (R : RingObject) (a b : Z) :
  zring R (a * b) ≈ rig_mul R (zring R a) (zring R b).
Proof.
  revert b.
  apply (Z_peano_rect
           (fun a => ∀ b, zring R (a * b)
                            ≈ rig_mul R (zring R a) (zring R b))).
  - intro b; simpl.
    now rewrite rig_mul_zero_l.
  - intros x IH b.
    rewrite Z.mul_succ_l.
    rewrite zring_add, IH.
    rewrite zring_succ.
    rewrite rig_distr_r.
    rewrite rig_mul_one_l.
    apply rig_add_comm.
  - intros x IH b.
    rewrite Z.mul_pred_l.
    unfold Z.sub.
    rewrite zring_add, IH.
    rewrite zring_opp.
    rewrite zring_pred.
    rewrite rig_distr_r.
    rewrite rig_mul_neg_one.
    apply rig_add_comm.
Qed.

Program Definition rng_from_Z (R : RingObject) : RigHom Int_Ring R := {|
  rig_map := {| morphism := zring R |}
|}.
Next Obligation. intros R; proper. Qed.
Next Obligation. intros R a b; apply zring_add. Qed.
Next Obligation. intros R; simpl; now rewrite rig_add_zero_r. Qed.
Next Obligation. intros R a b; apply zring_mul. Qed.

Lemma rng_from_Z_unique (R : RingObject) (h : RigHom Int_Ring R) (z : Z) :
  rig_map h z ≈ zring R z.
Proof.
  apply (Z_peano_rect (fun z => rig_map h z ≈ zring R z)).
  - apply (rig_map_zero h).
  - intros x IH.
    rewrite <- Z.add_1_l.
    rewrite (rig_map_add h 1%Z x).
    rewrite IH.
    rewrite zring_add.
    apply rig_add_respects; [| reflexivity ].
    etransitivity; [ apply (rig_map_one h) |].
    simpl; now rewrite rig_add_zero_r.
  - intros x IH.
    rewrite <- Z.sub_1_r.
    unfold Z.sub.
    rewrite (rig_map_add h x (-1)%Z).
    rewrite IH.
    rewrite zring_add.
    apply rig_add_respects; [ reflexivity |].
    (* h (-1) ≈ zring (-1) = -1 *)
    change (zring R (-1)) with (ring_neg R (rig_iter R 1)).
    transitivity (ring_neg R (rig_map h 1%Z)).
    + apply (RigHom_neg Int_Ring R h 1%Z).
    + apply ring_neg_respects.
      etransitivity; [ apply (rig_map_one h) |].
      simpl; now rewrite rig_add_zero_r.
Qed.

#[export] Program Instance Rng_Initial_Z : @Initial Rng := {
  terminal_obj := Int_Ring;
  one := rng_from_Z
}.
Next Obligation.
  intros R f g z; simpl.
  rewrite (rng_from_Z_unique R f z).
  now rewrite (rng_from_Z_unique R g z).
Qed.

(* * ** The commutative full subcategory / * ** 交换的全子范畴 *)

Definition CRng_Sub : Subcategory Rng :=
  @Build_Subcategory Rng
    (fun R : RingObject => ∀ a b, rig_mul R a b ≈ rig_mul R b a)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition CRng : Category := Sub Rng CRng_Sub.

Lemma CRng_Full : Category.Construction.Subcategory.Full Rng CRng_Sub.
Proof. intros x y ox oy g; exact I. Qed.

(*
 Non-vacuity: the integers are commutative, so [CRng] contains ℤ —
 as an actual object, not just a predicate instance. 

 --------
 非空性：整数是可交换的，因此 [CRng] 包含 ℤ——作为一个实际的对象，而不仅仅是一个谓词实例。
*)
Example Int_Ring_commutative : ∀ a b, rig_mul Int_Ring a b ≈ rig_mul Int_Ring b a.
Proof. intros a b; simpl; apply Z.mul_comm. Qed.

Definition Int_CRng : CRng := (Int_Ring; Int_Ring_commutative).

(* * ** Injections are monic; surjections are epi / * ** 单射是单态；满射是满态 *)

Lemma rng_injective_monic {R S : RingObject} (f : R ~{Rng}~> S) :
  (∀ a b : carrier (rig_setoid R), rig_map f a ≈ rig_map f b → a ≈ b) →
  Monic f.
Proof.
  intros Hinj.
  constructor; intros T g1 g2 Hg a.
  exact (Hinj (rig_map g1 a) (rig_map g2 a) (Hg a)).
Qed.

Lemma rng_surjective_epic {R S : RingObject} (f : R ~{Rng}~> S) :
  (∀ b : carrier (rig_setoid S), ∃ a, rig_map f a ≈ b) →
  Epic f.
Proof.
  intros Hsurj.
  constructor; intros T g1 g2 Hg b.
  destruct (Hsurj b) as [a Ha].
  rewrite <- Ha.
  exact (Hg a).
Qed.

(* * ** Mac Lane I.5, Exercise 4: ℤ → ℚ is epi and not surjective / * ** Mac Lane I.5, 练习 4：ℤ → ℚ 是满射（epi）但不是全射 *)

(* The rationals as a ring, over the stdlib [Qeq] setoid. / 有理数作为一个环，基于标准库 [Qeq] 集合等价关系。 *)
(* Named for the same reason as [zero_rig_setoid] above. / 命名的原因与上面的 [zero_rig_setoid] 相同。 *)
Program Definition q_rig_setoid : SetoidObject := {|
  carrier := Q
  ; is_setoid := {| Setoid.equiv := Qeq
                  ; Setoid.setoid_equiv := _ |}
|}.
Next Obligation.
  constructor; [ exact Qeq_refl | exact Qeq_sym | exact Qeq_trans ].
Qed.

Program Definition Q_Rig : RigObject := {|
  rig_setoid := q_rig_setoid;
  rig_zero := 0%Q;
  rig_add := Qplus;
  rig_one := 1%Q;
  rig_mul := Qmult;

  (* [Qeq] is the stdlib's [Prop]-valued equality of rationals. / [Qeq] 是 stdlib 的 [Prop] 值有理数的相等性。 *)
  rig_prop := @PropEquiv_of_relation Q (is_setoid q_rig_setoid) Qeq
                (fun _ _ h => h) (fun _ _ h => h)
|}.
Next Obligation. repeat intro; now apply Qplus_comp. Qed.
Next Obligation. repeat intro; now apply Qmult_comp. Qed.
Next Obligation. intros a b c; simpl; symmetry; apply Qplus_assoc. Qed.
Next Obligation. intros a b; simpl; apply Qplus_comm. Qed.
Next Obligation. intros a; simpl; apply Qplus_0_l. Qed.
Next Obligation. intros a b c; simpl; symmetry; apply Qmult_assoc. Qed.
Next Obligation. intros a; simpl; apply Qmult_1_l. Qed.
Next Obligation. intros a; simpl; apply Qmult_1_r. Qed.
Next Obligation. intros a b c; simpl; apply Qmult_plus_distr_r. Qed.
Next Obligation. intros a b c; simpl; apply Qmult_plus_distr_l. Qed.
Next Obligation. intros a; simpl; apply Qmult_0_l. Qed.
Next Obligation. intros a; simpl; apply Qmult_0_r. Qed.

Program Definition Q_Ring : RingObject := {|
  ring_rig := Q_Rig;
  ring_neg := Qopp
|}.
Next Obligation. repeat intro; now apply Qopp_comp. Qed.
Next Obligation.
  intros a; simpl.
  rewrite Qplus_comm; apply Qplus_opp_r.
Qed.

(* The inclusion, as a ring homomorphism. / 作为环同态的包含。 *)
Program Definition ZtoQ : Int_Ring ~{Rng}~> Q_Ring := {|
  rig_map := {| morphism := inject_Z |}
|}.
Next Obligation. intros; simpl; reflexivity. Qed.
Next Obligation.
  intros a b; simpl; unfold inject_Z, Qplus; simpl; unfold Qeq; simpl; ring.
Qed.
Next Obligation. intros; simpl; reflexivity. Qed.
Next Obligation.
  intros a b; simpl; unfold inject_Z, Qmult; simpl; unfold Qeq; simpl; ring.
Qed.

(*
 One-sided inverses on opposite sides agree in any rig: the monoid
 argument, with exactly the two hypotheses the proof consumes. 

 --------
 在任何幂半群中，两边的单侧逆是一致的：幺半群论证，恰好使用了证明所需的两个假设。
*)
Lemma rig_inv_unique (S : RigObject)
  (x u v : carrier (rig_setoid S)) :
  rig_mul S u x ≈ rig_one S → rig_mul S x v ≈ rig_one S →
  u ≈ v.
Proof.
  intros Hux Hxv.
  rewrite <- (rig_mul_one_r S u).
  rewrite <- Hxv.
  rewrite <- rig_mul_assoc.
  rewrite Hux.
  apply rig_mul_one_l.
Qed.

(* Every rational is (a/b)·b ≈ a with b := its positive denominator, and 1/b is a two-sided inverse of b in ℚ. / 每一个有理数可以表示为 (a/b)·b ≈ a，其中 b := 它的正分母，并且 1/b 是 b 在有理数集 ℚ 中的双边逆元。 *)
Lemma Q_num_den (q : Q) :
  (q * inject_Z (Z.pos (Qden q)) == inject_Z (Qnum q))%Q.
Proof.
  unfold Qeq, Qmult, inject_Z; simpl.
  rewrite Pos.mul_1_r.
  ring.
Qed.

Lemma Q_inv_den (q : Q) :
  (/ inject_Z (Z.pos (Qden q)) * inject_Z (Z.pos (Qden q)) == 1)%Q.
Proof.
  rewrite Qmult_comm.
  apply Qmult_inv_r.
  discriminate.
Qed.

(* The heart of the exercise: a homomorphism out of ℚ is determined by its values on the integers, because it must carry 1/b to the unique two-sided inverse of the image of b. / 练习的核心：从 ℚ 出发的同态由其在整数上的取值决定，因为它必须将 1/b 映射到 b 的像的唯一双边逆元。 *)
Theorem ZtoQ_epic : Epic ZtoQ.
Proof.
  constructor; intros S g1 g2 Hg q.
  (* both maps agree on every inject_Z z / 两个映射在每个 inject_Z z 上都一致 *)
  assert (HZ : ∀ z : Z, rig_map g1 (inject_Z z) ≈ rig_map g2 (inject_Z z)).
  { intro z; exact (Hg z). }
  (* both images of 1/b invert the common image of b / 1/b 的两张图像颠倒了 b 的常见图像 *)
  set (b := inject_Z (Z.pos (Qden q))).
  assert (Hinv1l : rig_mul S (rig_map g1 (/ b)%Q) (rig_map g1 b)
                     ≈ rig_one S).
  { rewrite <- rig_map_mul.
    etransitivity; [| apply (rig_map_one g1) ].
    apply (proper_morphism (rig_map g1)).
    apply Q_inv_den. }
  assert (Hinv2r : rig_mul S (rig_map g2 b) (rig_map g2 (/ b)%Q)
                     ≈ rig_one S).
  { rewrite <- rig_map_mul.
    etransitivity; [| apply (rig_map_one g2) ].
    apply (proper_morphism (rig_map g2)).
    rewrite Qmult_comm.
    apply Q_inv_den. }
  (* hence the images of 1/b coincide: g1(1/b) left-inverts the common image of b, which g2(1/b) right-inverts / 因此 1/b 的图像是重合的：g1(1/b) 对 b 的共同图像做左逆，而 g2(1/b) 做右逆 *)
  assert (Hinv : rig_map g1 (/ b)%Q ≈ rig_map g2 (/ b)%Q).
  { apply (rig_inv_unique S (rig_map g1 b)).
    - exact Hinv1l.
    - unfold b; rewrite (HZ (Z.pos (Qden q))).
      unfold b in Hinv2r; auto. }
  (* decompose q = (num q) · (1/b) and conclude / 分解 q = (num q) · (1/b) 并得出结论 *)
  assert (Hq : (q == inject_Z (Qnum q) * / b)%Q).
  { rewrite <- (Q_num_den q).
    fold b.
    rewrite <- Qmult_assoc.
    rewrite Qmult_inv_r.
    - now rewrite Qmult_1_r.
    - intro H; unfold b, inject_Z, Qeq in H; simpl in H; discriminate H. }
  rewrite (proper_morphism (rig_map g1) _ _ Hq).
  rewrite (proper_morphism (rig_map g2) _ _ Hq).
  rewrite !rig_map_mul.
  apply rig_mul_respects.
  - apply (HZ (Qnum q)).
  - exact Hinv.
Qed.

(*
 ...and it is not surjective: 1/2 has no preimage, since inject_Z z
 ≈ 1/2 would force 2·z = 1 in ℤ.  Stated with the PROPOSITIONAL
 existential — the strongest form: refuting mere existence also
 refutes the library's data-valued ∃ (the corollary below), which is
 the exact negation of [rng_surjective_epic]'s hypothesis shape. 

 --------
 ...并且它不是满射：1/2 没有原像，因为 inject_Z z ≈ 1/2 会迫使 2·z = 1 在 ℤ 中成立。 用命题存在量词来表述 —— 最强形式：否定单纯存在也同时否定库中的带值 ∃（见下列推论），这正好是否定了 [rng_surjective_epic] 的假设形式。
*)
Theorem ZtoQ_not_surjective :
  (∀ q : Q, exists z : Z, inject_Z z == q)%Q → False.
Proof.
  intro Hsurj.
  destruct (Hsurj (1 # 2)%Q) as [z Hz].
  unfold Qeq, inject_Z in Hz; simpl in Hz.
  lia.
Qed.

Corollary ZtoQ_not_surjective_sigT :
  (∀ q : Q, ∃ z : Z, inject_Z z == q)%Q → False.
Proof.
  intro Hsurj.
  apply ZtoQ_not_surjective.
  intro q.
  destruct (Hsurj q) as [z Hz].
  now exists z.
Qed.

(* Mac Lane I.5 Exercise 4, packaged. / Mac Lane I.5 练习 4，已打包。 *)
Definition ZtoQ_epi_not_surjective :=
  (ZtoQ_epic,
   ZtoQ_not_surjective).

(** ** Acceptance tests / ** 验收测试 *)

(* The initial homomorphism computes on both signs. / 初始同态在两个符号上进行计算。 *)
Example zring_Z_3 : rig_map (rng_from_Z Int_Ring) 3%Z = 3%Z := eq_refl.
Example zring_Z_neg2 :
  rig_map (rng_from_Z Int_Ring) (-2)%Z = (-2)%Z := eq_refl.

(* The forgetful functors return the carrier on the nose. / 遗忘函子准确地返回承载对象。 *)
Example rng_forget_ab_carrier (R : RingObject) :
  cmon_setoid (ab_cmon (Rng_Forget_Ab R)) = rig_setoid R := eq_refl.
Example rng_forget_carrier (R : RingObject) :
  Rng_Forget R = rig_setoid R := eq_refl.

(* ℚ really contains the non-integer the separation uses. / ℚ 确实包含分离使用的非整数。 *)
Example half_times_two : ((1 # 2) * inject_Z 2 == 1)%Q := eq_refl.
