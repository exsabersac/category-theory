(**
* Probe for quotients as coequalizers split under U (issue #479)

    Pins the measured boundaries of Instance/Grp/Coequalizer.v and
    Instance/Rng/Coequalizer.v (Mac Lane, §VI.6, book p. 150, PDF p. 159,
    items maclane:VI.6:remark2 and maclane:VI.6:ex1, read from the page
    image: "if we apply the standard forgetful functor U: Grp→Set, the
    resulting fork in Set is split") and of Instance/Mon/Presentation.v
    (Awodey, 2005 pre-print, §3.4 Proposition 3.22 and §3.5 Exercise 3,
    items awodey:3.4:prop22 and awodey:3:ex3).  Donors named by a
    refusal: Instance/Grp/TwoFunctors.v ([S3], R3) and Instance/Mon/
    Free.v (the free functor's action on arrows, R5); by a control:
    Instance/Sets/Propositional/Full.v ([choice_of_untr] and
    [untr_of_choice], C19 and C20).

    THE IMPORT LIST, checked by a script over the [Require] lines.
    Target by target in dependency order: the fifteen lines of
    Instance/Grp/Coequalizer.v and that target; the nine lines
    Instance/Rng/Coequalizer.v adds and that target; the thirteen lines
    Instance/Mon/Presentation.v adds and that target: forty lines.  A
    shorter list is what makes a probe pass for no reason.

    DISCIPLINE.  Every negative other than the instrument is an
    [Example] or a [Definition], never a [Check].  Each of the seven
    refutation lines (the instrument and R1 to R6) was stripped of its
    refutation keyword in a copy of this WHOLE file, one at a time, and
    each copy stops inside the stripped command (seven of seven, by
    loop-tools' swcheck.py, comparing the File line of the error with the
    command's extent); each of the twenty controls, wrapped in the
    keyword in a whole-file copy, stops at that command with the message
    Rocq prints for a refutation whose command succeeds (twenty of
    twenty, by the same script).  Quotations are Rocq 9.1.1's under
    this file's import list, the environment block left out and
    universe serials written u0, u1, ..., distinct serials distinctly.

    KINDS.  NAME-ABSENCE: the instrument.  CONVERSION, [eq_refl] refused
    with a "cannot unify" parenthetical, every statement well typed: R1,
    R4, R5.  UNIVERSE, "universe inconsistency" between levels this file
    declares: R2, R3, R6.  CAUSES, read from the terms.  R1 and R4 are
    law 4 of the splitting after U, ∂₁ (t x) against s (p x), equal at
    ≈ (C1, C8) by a group or ring law of a variable G or R.  R5 is the
    free functor's action on arrows at a variable word of words, equal
    at ≈ (C12) and read through universal arrows, where the counit
    computes (C11).  R2 and R6 are ∂₀ at a membership level m above the
    carrier level p: an element of G ×₀ N carries a membership witness,
    and the pair lives in [Grp@{_ p}] (resp. [Rng@{_ p}]), while G ×₀ N
    as a group and a transversal's untruncation are formable there (C14,
    C5; C16, C15).  Below the carrier the readbacks of the pair are
    accepted (C17, C18): their binders keep N's membership level apart
    from the carrier level, which bare binders, left to minimization,
    identified.  R3 is S₃'s own pin, Instance/Grp/TwoFunctors.v's
    [S3@{u} : GrpObject@{u Set Set}]: the S₃/A₃ splitting is refused in
    [Grp@{u p}] above [Set], where the Z/4 refutation is accepted (C6);
    at [Set] it is accepted (C7).  C19 and C20 put the untruncation
    principle at the membership level m, written out as Full.v writes
    Instance/Sets/Classifier/OneLevel.v's [Untruncate@{m}], against the
    untruncation of the coset relation of every N at that level: Full.v's
    [choice_of_untr] composed with [choice_untruncates] one way, and
    [NS_untruncates_chooses] composed with [untr_of_choice] the other.

    LABELS.  Each refutation and control carries its label in a comment
    on the line above it; the constants are [p479_cN_…] and [p479_rN_…].

    RESTATEMENTS.  C4 is [transversal_round_trip], C9 [rsdp_mul_snd],
    C10 [EvenIdeal_transversal_fun], C11 [Mon_flatten_fun] and C13
    [Mon_canonical_split_s]; C17 and C18 are [transversal_split_e] and
    [rtransversal_split_e] at a membership level below the carrier.  C2
    and C3 are two readbacks the files do not state: t's second
    component with p x reduced to x, and the descent's underlying map,
    h's own, both at [eq_refl].

    THE REFUSALS, with the message each stripped copy prints.
      The instrument: The reference p479_absent_name was not found in
        the current environment.
      R1: (cannot unify "semidirect_d1 N (scoeq_t (transversal_split N
        T) x)" and "transversal_map T x").
      R2: The term "N" has type "NormalSubgroup@{m p p p} G" while it is
        expected to have type "NormalSubgroup@{u0 u1 u1 u1} ?G"
        (universe inconsistency: Cannot enforce m = u0 because
        u0 <= u1 < m).
      R3: The term "semidirect_d0 A3" has type "SemidirectGrp@{…}
        A3@{u0 Set} ~{ Grp@{u1 Set} }~> S3@{Set}" while it is
        expected to have type "?x ~{ Grp@{u p} }~> ?y" (universe
        inconsistency: Cannot enforce Set = p).
      R4: (cannot unify "rsemidirect_d1 A (scoeq_t (rtransversal_split A
        T) r)" and "rtransversal_map T r").
      R5: (cannot unify "mon_fun (Mon_free_evaluate M) ww" and "wmap (λ w
        : mon_ob (fobj[FreeMonSets] (fobj[Mon_Forget] M)), mon_fun
        (Mon_evaluate M) w) ww").
      R6: The term "A" has type "Ideal@{m p p p} R" while it is expected
        to have type "Ideal@{u0 u1 u1 u1} ?R" (universe inconsistency:
        Cannot enforce m = u0 because u0 <= u1 < m).
    In R2 and R6 the two serials are distinct: the expected type is ∂₀'s
    binder, membership u0 at or below carrier u1, the bound the two
    refusals pin; written as one u it would read as an identification.

--------
* 探查商作为在 U 下分裂的余等化器（问题 #479）

固定了 Instance/Grp/Coequalizer.v 和 Instance/Rng/Coequalizer.v（Mac Lane, §VI.6, 书本页 150, PDF 页 159, 条目 maclane:VI.6:remark2 和 maclane:VI.6:ex1, 从页面图像读取：“如果我们应用标准的遗忘函子 U: Grp→Set，Set 中产生的叉是分裂的”）以及 Instance/Mon/Presentation.v（Awodey, 2005 预印本, §3.4 命题 3.22 和 §3.5 练习 3, 条目 awodey:3.4:prop22 和 awodey:3:ex3）的测量边界。捐赠者由拒绝命名：Instance/Grp/TwoFunctors.v ([S3], R3) 和 Instance/Mon/Free.v（自由函子对箭头的作用, R5）；由控制命名：Instance/Sets/Propositional/Full.v ([choice_of_untr] 和 [untr_of_choice], C19 和 C20)。

导入列表，由一个脚本在 [Require] 行上检查。
按照依赖顺序逐个目标：Instance/Grp/Coequalizer.v 的十五行及该目标；Instance/Rng/Coequalizer.v 的九行新增及该目标；Instance/Mon/Presentation.v 的十三行新增及该目标：共四十行。一个较短的列表会无缘无故让探针通过。

纪律。除了工具之外，所有负面项都是 [Example] 或 [Definition]，从不使用 [Check]。七条反驳线（工具和 R1 到 R6）中的每一条，都在这个完整文件的副本中依次去掉了它们的反驳关键字，并且每个副本都在被去掉命令的地方停止（七条中的七条，通过 loop-tools 的 swcheck.py，比对错误的文件行与命令的范围）；二十个控制项，每个在整个文件副本中用关键字包裹，在该命令处停止，并显示 Rocq 为命令成功的反驳打印的消息（二十条中的二十条，通过同一个脚本）。引号是 Rocq 9.1.1 在这个文件的导入列表下的内容，环境块被省略，宇宙序列标记为 u0、u1、…，不同的序列有不同的标记。

种类。名称缺失：该工具。转换，[eq_refl] 被拒绝，带有“无法统一”的括号，每个语句类型正确：R1、R4、R5。宇宙，该文件声明的各级之间存在“宇宙不一致”：R2、R3、R6。原因，从术语中读取。R1 和 R4 是 U 后分裂的定律 4，∂₁ (t x) 对 s (p x)，通过变量 G 或 R 的群或环定律在 ≈ (C1, C8) 上相等。R5 是自由函子的箭头作用在词的变量词上，在 ≈ (C12) 上相等，并通过通用箭头读取，其中協單元计算 (C11)。R2 和 R6 是在载体层 p 之上的会员层 m 的 ∂₀：G ×₀ N 的一个元素具有会员证明，并且该对存在于 [Grp@{_ p}]（分别为 [Rng@{_ p}]），而 G ×₀ N 作为一个群以及横截面的未截断可以在那里形成 (C14、C5；C16、C15)。
在载体下，该对的回读被接受（C17, C18）：其绑定器保持 N 的成员级别与载体级别分开，而载体级别的绑定器，在最小化下，被识别。R3 是 S₃ 自身的 pin，Instance/Grp/TwoFunctors.v 的 [S3@{u} : GrpObject@{u Set Set}]：在 [Grp@{u p}] 高于 [Set] 处，S₃/A₃ 的拆分被拒绝，其中 Z/4 的反驳被接受（C6）；在 [Set] 处被接受（C7）。C19 和 C20 将未截断原则置于成员级别 m，如 Full.v 在 Instance/Sets/Classifier/OneLevel.v 中的 [Untruncate@{m}] 所写，对抗该级别上每个 N 的陪集关系的未截断：Full.v 的 [choice_of_untr] 与 [choice_untruncates] 一方向组合，[NS_untruncates_chooses] 与 [untr_of_choice] 另一方向组合。

标签。每个反驳和控制在其上方的注释中都有标签；常量是 [p479_cN_…] 和 [p479_rN_…]。

重述。C4 是 [transversal_round_trip]，C9 是 [rsdp_mul_snd]，C10 是 [EvenIdeal_transversal_fun]，C11 是 [Mon_flatten_fun]，C13 是 [Mon_canonical_split_s]；C17 和 C18 分别是 [transversal_split_e] 和 [rtransversal_split_e]，处于低于承运人的会员等级。C2 和 C3 是文件中未说明的两个回读：第二个组件，其 p x 降至 x，以及下降的底层地图，h 自身的地图，两者均处于 [eq_refl]。

拒绝，每个打印的副本都会显示该消息。工具：在当前环境中未找到参考 p479_absent_name。R1：（无法统一 "semidirect_d1 N (scoeq_t (transversal_split N T) x)" 和 "transversal_map T x"）。R2：项 "N" 的类型是 "NormalSubgroup@{m p p p} G"，而预期类型是 "NormalSubgroup@{u0 u1 u1 u1} ?G"（宇宙不一致性：无法强制 m = u0 因为 u0 <= u1 < m）。R3：项 "semidirect_d0 A3" 的类型是 "SemidirectGrp@{…} A3@{u0 Set} ~{ Grp@{u1 Set} }~> S3@{Set}"，而预期类型是 "?x ~{ Grp@{u p} }~> ?y"（宇宙不一致性：无法强制 Set = p）。R4：（无法统一 "rsemidirect_d1 A (scoeq_t (rtransversal_split A T) r)" 和 "rtransversal_map T r"）。
R5: （无法统一 "mon_fun (Mon_free_evaluate M) ww" 和 "wmap (λ w : mon_ob (fobj[FreeMonSets] (fobj[Mon_Forget] M)), mon_fun (Mon_evaluate M) w) ww"）。R6: 项 "A" 的类型是 "Ideal@{m p p p} R"，但期望的类型是 "Ideal@{u0 u1 u1 u1} ?R"（宇宙不一致：无法强制 m = u0，因为 u0 <= u1 < m）。在 R2 和 R6 中，这两个序列是不同的：期望的类型是 ∂₀ 的绑定器，成员资格 u0 在或小于承载 u1，两次拒绝的边界固定；如果写作一个 u，则会被理解为一个标识。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Coequalizer.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Category.Instance.Rng.Coequalizer.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Instance.Mon.Coproduct.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Mon.Word.
Require Import Category.Instance.Mon.Presentation.

Generalizable All Variables.

(* The instrument / 乐器 *)
Fail Definition p479_instrument : True := p479_absent_name.

(** ** Groups *)

Section GrpProbe.

Universe p.
Context {G : GrpObject@{p p p}} (N : NormalSubgroup G).
Context (T : Transversal N) (x : carrier G).

(* R1 *)
Fail Example p479_r1_law4 :
  grp_map (semidirect_d1 N) (scoeq_t (transversal_split N T) x)
    = transversal_map T x := eq_refl.

(* C1 *)
Example p479_c1_law4 :
  grp_map (semidirect_d1 N) (scoeq_t (transversal_split N T) x)
    ≈ transversal_map T x.
Proof. exact (scoeq_law4 (transversal_split N T) x). Qed.

(* C2 *)
Example p479_c2_t_snd :
  `1 (snd (scoeq_t (transversal_split N T) x))
    = grp_mul G (grp_inv G x) (transversal_map T x) := eq_refl.

(* C3 *)
Example p479_c3_desc {K : GrpObject@{p p p}} (h : G ~{Grp}~> K)
  (Hh : h ∘ semidirect_d0 N ≈ h ∘ semidirect_d1 N) (a : carrier G) :
  grp_map (unique_obj (coeq_desc (quot_proj_IsCoequalizer N) h Hh)) a
    = grp_map h a := eq_refl.

(* C4 *)
Example p479_c4_round_trip (a : carrier G) :
  transversal_map (split_transversal N (transversal_split N T)) a
    = transversal_map T a := eq_refl.

End GrpProbe.

(*
Membership above the carrier: the pair is refused there; G ×₀ N is
   formable as a group, and a transversal still untruncates.

--------
在载体之上的从属：该对在那里被拒绝；G ×₀ N 可以作为一个群形成，并且一个横截面仍然不会截断。
*)
Section GrpMembershipAbove.

Universes p m.
Constraint p < m.
Context {G : GrpObject@{p p p}} (N : NormalSubgroup@{m p p p} G).

(* R2 *)
Fail Definition p479_r2_pair := semidirect_d0 N.

(* C5 *)
Definition p479_c5_transversal (T : Transversal N) : CosetUntruncates N :=
  transversal_untruncates N T.

(* C14 *)
Definition p479_c14_sdp : GrpObject := SemidirectGrp N.

End GrpMembershipAbove.

(*
Carriers above Set: Z/4's refutation is accepted there, the S3/A3
   splitting is refused.

--------
高于设定的运载工具：Z/4 的反驳在那里被接受，S3/A3 拆分被拒绝。
*)
Section AboveSet.

Universes u p.
Constraint Set < p.
Constraint p < u.

(* C6 *)
Definition p479_c6_Z4 :
  @SplitCoequalizer Grp@{u p} _ _ (semidirect_d0 Z4_two)
    (semidirect_d1 Z4_two) → False := Z4_two_not_split_in_Grp.

(* R3 *)
Fail Definition p479_r3_S3 :
  @SplitCoequalizer Grp@{u p} _ _ (semidirect_d0 A3) (semidirect_d1 A3)
  := S3_A3_Grp_split.

End AboveSet.

(* C7 *)
Definition p479_c7_S3 :
  SplitCoequalizer (semidirect_d0 A3) (semidirect_d1 A3) := S3_A3_Grp_split.

(** ** Rings *)

Section RngProbe.

Universe p.
Context {R : RingObject@{p p p}} (A : Ideal R).
Context (T : RTransversal A) (r : carrier (rig_setoid R)).

(* R4 *)
Fail Example p479_r4_law4 :
  rig_map (rsemidirect_d1 A) (scoeq_t (rtransversal_split A T) r)
    = rtransversal_map T r := eq_refl.

(* C8 *)
Example p479_c8_law4 :
  rig_map (rsemidirect_d1 A) (scoeq_t (rtransversal_split A T) r)
    ≈ rtransversal_map T r.
Proof. exact (scoeq_law4 (rtransversal_split A T) r). Qed.

(* C9 *)
Example p479_c9_mul_snd (q q' : carrier (rig_setoid (SemidirectRing A))) :
  `1 (snd (rig_mul (SemidirectRing A) q q'))
    = rig_add R (rig_add R (rig_mul R (fst q) (`1 (snd q')))
                           (rig_mul R (`1 (snd q)) (fst q')))
                (rig_mul R (`1 (snd q)) (`1 (snd q'))) := eq_refl.

End RngProbe.

Section RngMembershipAbove.

Universes p m.
Constraint p < m.
Context {R : RingObject@{p p p}} (A : Ideal@{m p p p} R).

(* R6 *)
Fail Definition p479_r6_pair := rsemidirect_d0 A.

(* C15 *)
Definition p479_c15_transversal (T : RTransversal A) : RCosetUntruncates A :=
  rtransversal_untruncates A T.

(* C16 *)
Definition p479_c16_sdp : RingObject := SemidirectRing A.

End RngMembershipAbove.

(* C10 *)
Example p479_c10_even (a : Z) :
  rtransversal_map EvenIdeal_transversal a = Z.modulo a 2 := eq_refl.

(*
Membership below the carrier: the readbacks of the pair are accepted
   there, and the untruncation principle at the membership level is
   OneLevel.v's [Untruncate] at that level, against every N.

--------
承运人以下的成员：在那里的对偶重读是被接受的，成员级别的非截断原则是 OneLevel.v 在该级别的 [Untruncate]，对每一个 N 都有效。
*)
Section MembershipBelow.

Universes p m.
Constraint m < p.

(* C17 *)
Definition p479_c17_readback {G : GrpObject@{p p p}}
  (N : NormalSubgroup@{m p p p} G) (T : Transversal N) :=
  transversal_split_e T.

(* C18 *)
Definition p479_c18_rreadback {R : RingObject@{p p p}}
  (A : Ideal@{m p p p} R) (T : RTransversal A) :=
  rtransversal_split_e T.

(* C19 *)
Definition p479_c19_untruncate {G : GrpObject@{p p p}}
  (N : NormalSubgroup@{m p p p} G)
  (U : ∀ P : Type@{m}, (∀ Q : Prop, (P → Q) → Q) → P) :
  CosetUntruncates N := choice_untruncates N (choice_of_untr U).

(* C20 *)
Definition p479_c20_untruncate
  (D : ∀ S : Type@{m}, CosetUntruncates (NS S)) :
  ∀ P : Type@{m}, (∀ Q : Prop, (P → Q) → Q) → P :=
  untr_of_choice (fun S => NS_untruncates_chooses S (D S)).

End MembershipBelow.

(** ** Monoids *)

Section MonProbe.

Universes o so.

Local Notation MonOS :=
  (@Mon@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).

Context (M : MonOS) (ww : list (list (mon_ob M))).

(* C11 *)
Example p479_c11_flatten :
  mon_fun (Mon_flatten M) ww = wconcat ww := eq_refl.

(* R5 *)
Fail Example p479_r5_evaluate :
  mon_fun (Mon_free_evaluate M) ww
    = wmap (fun w => mon_fun (Mon_evaluate M) w) ww := eq_refl.

(* C12 *)
Example p479_c12_evaluate :
  mon_fun (Mon_free_evaluate M) ww
    ≈ wmap (fun w => mon_fun (Mon_evaluate M) w) ww.
Proof.
  exact (free_mon_fmap_is_wmap (fmap[Mon_Forget] (Mon_evaluate M)) ww).
Qed.

(* C13 *)
Example p479_c13_s :
  scoeq_s (Mon_canonical_split M) = free_mon_insert (Mon_Forget M) := eq_refl.

End MonProbe.
