(*
Boundary probe for issue #367: Mac Lane §IV.3 Theorem 1 and its lemma.

   Targets: Functor/Hom/Transfer.v and Adjunction/FullFaithful.v.  This
   file mirrors BOTH targets' full Require lists, then requires the
   targets themselves, then the extra modules the non-vacuity witnesses
   need.  The short-prefix hazard is real and is what this discipline
   exists to avoid: a probe compiled against fewer imports can fail for a
   missing coercion or a missing reference and look like a clean
   refutation.

   WHY A SEPARATE FILE.  An in-file [Fail] renames in lockstep with the
   constant it guards, so it cannot detect a rename.  Every negative here
   names target constants from OUTSIDE the targets, and every constant a
   negative names also appears outside a [Fail] elsewhere in this file.

   CONTENTS

   - An instrument check: a [Fail Check] on a reference that does not
     exist, so that a [Fail] which passes for the wrong reason is
     visible.
   - SEVEN negatives of THREE kinds, kept lexically apart and told apart
     by the error TEXT rather than by label:
       CONVERSION   ends "cannot unify" between two terms of one type;
       TYPING       a plain "has type ... while it is expected to have
                    type", with no "cannot unify" and no universe clause;
       FORMABILITY  ends "universe inconsistency".
     Each was stripped ONE AT A TIME, with the others left as [Fail], and
     compiled alone; the whole error was read and the place it fires
     confirmed.
   - Positive controls beside each negative.
   - Non-vacuity for one of the two quadrants of Theorem 1, and the
     honest scope of the other.

   NOTE on what "not a Section" can mean.  Theorem 1(ii) is a
   biconditional between [Full U] and the FAMILY (∀ a, Section (ε a)).
   Refuting fullness therefore refutes the FAMILY, not a named component:
   a single ε_a may still split while U is not full.  The two witnesses
   below are stated at exactly that strength and no stronger.

--------
针对问题 #367 的边界探测：Mac Lane §IV.3 定理 1 及其引理。

目标：Functor/Hom/Transfer.v 和 Adjunction/FullFaithful.v。此文件镜像了两个目标的完整 Require 列表，然后再 require 目标本身，以及非空性证据所需的额外模块。短前缀的风险是真实存在的，这正是该规范存在的原因：针对较少导入编译的探针可能因缺少类型转换或缺少引用而失败，并看起来像一个干净的反驳。

为什么使用单独的文件。文件内的 [Fail] 会与它所保护的常量同步重命名，因此无法检测重命名。这里的每个否定都命名来自目标之外的常量，并且每个否定所命名的常量也出现在该文件其他地方的 [Fail] 之外。

目录

- 仪器检查：在不存在的参考上使用 [Fail Check]，因此可以看到一个 [Fail] 错误地通过的情况。  
- 七个三种类型的负面案例，在词汇上保持分离，并通过错误文本而不是标签区分：  
  CONVERSION（转换）以“cannot unify”结束，表示两个相同类型的项不能统一；  
  TYPING（类型检查）为简单的“has type ... while it is expected to have type”，没有“cannot unify”也没有宇宙条款；  
  FORMABILITY（可形成性）以“universe inconsistency”结束。  
  每个案例单独剥离一次，其余被替换为 [Fail] 并单独编译；阅读完整错误并确认触发位置。  
- 每个负面案例旁边有正面对照。  
- 定理 1 的两个象限之一的非空性，以及另一个象限的真实范围。

关于“非截面”可能意味着什么的说明。定理1(ii)是在 [Full U] 和 FAMILY (∀ a, Section (ε a)) 之间的双条件。 因此，反驳满性会反驳 FAMILY，而不是某个命名的组件：单个 ε_a 仍可能分裂，而 U 并非满。下面的两个证据正是在这种强度下陈述的，并无更强。
*)

(* The Require list of Functor/Hom/Transfer.v. / Functor/Hom/Transfer.v 的 Require 列表。 *)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Functor.Hom.

(* The extra Requires of Adjunction/FullFaithful.v. / 附加/全忠诚的额外需求.v *)
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Fullness.
Require Import Category.Adjunction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.

(* The two targets. / 这两个目标。 *)
Require Import Category.Functor.Hom.Transfer.
Require Import Category.Adjunction.FullFaithful.

(* Prior art the probe checks against the targets, and the witnesses. / 先前技术探针检查目标和证人。 *)
Require Import Category.Instance.Coq.Monoid.Free.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.One.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.Pointed.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* ------------------------------------------------------------------ *)
(** ** Instrument check / ** 仪表检查 *)

(*
If this ever stops failing, the [Fail]s below are not measuring
   anything.

--------
如果这停止失败，下面的 [Fail] 根本没有测量任何东西。
*)

Fail Check probe_367_no_such_reference.

(* ------------------------------------------------------------------ *)
(** ** (1) The transfer transformation against [fmap[Curried_Hom]] / ** (1) 针对 [fmap[Curried_Hom] 的传输变换 *)

Section TransferComparison.

Context {A : Category}.
Context {a b : A}.
Context (f : b ~> a).

(*
CONTROL.  The values agree at Leibniz equality, and the two
   transformations agree at [≈] in the functor category.  Both of these
   are the targets' own shipped constants, named here outside any
   [Fail].

--------
控制。 这些值在莱布尼茨等式下是一致的，并且在函子范畴中，两个变换在 [≈] 处是一致的。 这两者都是目标自身提供的常量，这里在任何 [Fail] 之外命名。
*)

Check @hom_transfer.
Check @Curried_Hom.
Check (@hom_transfer_is_fmap_value A a b f).
Check (@hom_transfer_is_fmap A a b f).

Example ctrl_transfer_value (c : A) (h : a ~> c) :
  transform[hom_transfer f] c h
    = transform[fmap[Curried_Hom A] (f : a ~{Opposite A}~> b)] c h
  := eq_refl.

(*
NEGATIVE 1 (CONVERSION).  The whole [Transform] record is NOT
   [fmap[Curried_Hom A] f]: [Transform] carries [naturality] and
   [naturality_sym], which the two definitions elaborate as separate
   obligations.  Stripped and compiled alone, this reports
   `The term "eq_refl" has type "hom_transfer f = hom_transfer f" while
   it is expected to have type "hom_transfer f = fmap[A] f" (cannot unify
   "hom_transfer f" and "fmap[A] f")`.  Note the display: the coercion
   [Curried_Hom : Category >-> Functor] makes the functor print as its
   CATEGORY.

--------
否定 1（转换）。整个 [Transform] 记录不是 [fmap[Curried_Hom A] f]: [Transform] 携带 [naturality] 和 [naturality_sym]，这两个定义将其作为独立的义务来详细说明。单独剥离并编译时，它会报告 `术语 "eq_refl" 的类型为 "hom_transfer f = hom_transfer f"，而期望的类型为 "hom_transfer f = fmap[A] f"（无法统一 "hom_transfer f" 和 "fmap[A] f"）`。注意显示：强制转换 [Curried_Hom : Category >-> Functor] 使函子以其类别打印。
*)

Fail Example neg1_whole_record :
  hom_transfer f = fmap[Curried_Hom A] (f : a ~{Opposite A}~> b)
  := eq_refl.

(*
NEGATIVE 2 (CONVERSION).  Neither is the COMPONENT record, one rung
   lower: a [SetoidMorphism] carries a [proper_morphism] certificate, and
   the two are separately elaborated.  The control above shows the
   underlying values agree, so this locates the difference exactly at the
   certificate — the whole-record failure is not only about naturality.

--------
否定 2（转换）。组件记录也不是，更低一层：一个 [SetoidMorphism] 拥有一个 [proper_morphism] 证书，并且两者被单独展开。上方的控制显示底层值一致，因此这将差异精确定位在证书上——整个记录失败不仅仅是关于自然性的问题。
*)

Fail Example neg2_component_record (c : A) :
  transform[hom_transfer f] c
    = transform[fmap[Curried_Hom A] (f : a ~{Opposite A}~> b)] c
  := eq_refl.

(* CONTROL.  The Yoneda-side readback holds at [≈]. / 控制。Yoneda 端的回读保持在 [≈]。 *)

Check (@hom_transfer_at_id A a b f).

(*
NEGATIVE 3 (CONVERSION).  It does not hold at [eq_refl]: the value is
   `id ∘ f`, and [id_left] is a law field of [Category], so no amount of
   conversion removes it.

--------
负 3（转换）。它在 [eq_refl] 上不成立：值是 `id ∘ f`，并且 [id_left] 是 [Category] 的法律字段，所以无论多少转换都无法去掉它。
*)

Fail Example neg3_transfer_at_id :
  transform[hom_transfer f] a id = f := eq_refl.

End TransferComparison.

(* ------------------------------------------------------------------ *)
(** ** (2) Split monic is not plain monic / ** (2) 可分首一不是普通首一 *)

Section SplitVersusMonic.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

(*
CONTROL.  Theorem 1(ii) delivers a [Section] — the library's split
   monomorphism — and that is what the reviewer check for this issue
   asks for.

--------
控制。定理 1(ii) 提供了一个 [Section] —— 库的拆分单态射 —— 这正是评论者在此问题中要求检查的内容。
*)

Check @right_adjoint_full_iff_counit_split_monic.

Definition ctrl_section (HU : Functor.Full U) (a : C) :
  Section (@counit C D F U A a) :=
  fst right_adjoint_full_iff_counit_split_monic HU a.

(*
NEGATIVE 4 (TYPING).  [Section] and [Monic] are two different classes,
   so the conclusion of (ii) is not a [Monic] statement even though every
   [Section] is monic ([sections_are_monic]).  Stripped and compiled
   alone, this reports a plain `has type ... while it is expected to have
   type ...` with NO "cannot unify" and no universe clause — the mark
   that separates it from negatives 1-3 and 5.

--------
负面 4（打字）。[Section] 和 [Monic] 是两个不同的类，所以（ii）的结论并不是 [Monic] 语句，尽管每个 [Section] 都是单射的（[sections_are_monic]）。单独剥离和编译时，这会报告一个普通的 `具有类型 ... 而预期类型为 ...`，没有“无法统一”也没有宇宙子句——这是将其与负面 1-3 和 5 区分开的标志。
*)

Fail Definition neg4_section_is_not_monic (HU : Functor.Full U) (a : C) :
  Monic (@counit C D F U A a) :=
  fst right_adjoint_full_iff_counit_split_monic HU a.

(*
CONTROL that the implication is nevertheless available, by the
   in-tree passage rather than by conversion.

--------
控制该蕴涵仍然可用，通过树内通路而不是通过转换。
*)

Definition ctrl_section_gives_monic (HU : Functor.Full U) (a : C) :
  Monic (@counit C D F U A a) :=
  sections_are_monic _ _ _ (ctrl_section HU a).

End SplitVersusMonic.

(* ------------------------------------------------------------------ *)
(** ** (3) The reflective donor is opaque / ** (3) 反射性供体是不透明的 *)

Section ReflectiveOpacity.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context (x : Sub C S).

(*
CONTROL.  Section (G) of the target derives the conclusion of
   Construction/Reflective.v from Theorem 1(iii), and the existing
   lemma is nameable here.

--------
控制。目标的第(G)节从定理1(iii)推导出Construction/Reflective.v的结论，现有的引理在这里是可命名的。
*)

Check (@reflective_counit_IsIsomorphism_general C S R x).
Check (@reflective_counit_iso C S R x).
Check (to (@reflective_counit_iso C S R x)).
Check @reflector.
Check @Incl.
Check @reflective_adj.

(*
NEGATIVE 5 (CONVERSION).  [reflective_counit_iso] produces DATA and is
   closed with [Qed] (Construction/Reflective.v), so its [to] does not
   reduce to the counit although the proof script supplies exactly that.
   Stripped and compiled alone this reports "cannot unify".  The [≈] form
   is unavailable for the same reason and is therefore not shipped
   either: there is nothing to rewrite with.

--------
NEGATIVE 5（转换）。[reflective_counit_iso] 生成数据，并由 [Qed]（Construction/Reflective.v）关闭，因此它的 [to] 并不会约化到余单位，尽管证明脚本正好提供了这一点。单独剥离和编译时，会报告“无法统一”。[≈] 形式由于同样的原因不可用，因此也不会被发布：没有任何内容可供改写。
*)

Fail Example neg5_reflective_to_is_counit :
  to (@reflective_counit_iso C S R x)
  = @counit (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x
  := eq_refl.

End ReflectiveOpacity.

(* ------------------------------------------------------------------ *)
(** ** (4) Universes: what the headlines inherit / ** (4) 宇宙：头条所继承的 *)

(*
The measurement, for the record: every headline of both targets is
   over categories whose hom and proof universes are identified IN THE
   BINDER (`Category@{u u0 u0}`), and the theorem file's headlines carry
   in addition the single BLOCK equation `u0 = u2`, identifying C's and
   D's hom-and-proof universes.  Neither file has a `Set` in any binder
   or block.  The two probes below isolate a donor for each.

--------
测量结果，供记录：两个目标的每个标题都位于其同构和证明宇宙在活页夹中标识的类别之上（`Category@{u u0 u0}`），并且定理文件的标题另外还包含单个 BLOCK 方程 `u0 = u2`，用于标识 C 和 D 的同构与证明宇宙。两个文件中都没有任何活页夹或块中有 `Set`。下面的两个探针分别为每个目标隔离出一个捐赠者。
*)

Section HomProofDonor.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (u v : Cu).
Context (g : u ~{Cu}~> v).

(*
CONTROLS accepted at these very levels: naming a hom, an identity, and
   a composite.

--------
在这些层次上接受的控制：命名同质体、身份和复合体。
*)

Check (u ~{Cu}~> v).
Check (@id Cu u).
Check (g ∘ @id Cu u).
Check @Retraction.

(*
NEGATIVE 6 (FORMABILITY).  [Epic] alone identifies hom with proof, so
   it is rejected where the hom and proof universes are declared strictly
   apart.  Stripped and compiled alone it ends "universe inconsistency".
   [Monic], [Section] and [Retraction] are rejected at the same levels;
   they are listed here as further [Fail]s rather than as separate
   numbered negatives, since they measure the same identification.

--------
负面 6（可形成性）。单独使用 [Epic] 可以识别 hom 并提供证明，因此在 hom 和证明宇宙被严格分开声明的情况下会被拒绝。单独剥离和编译时会显示“宇宙不一致”。[Monic]、[Section] 和 [Retraction] 在相同级别被拒绝；这里将它们列为进一步的 [Fail]，而不是单独编号的负面，因为它们测量的是相同的识别。
*)

Fail Check (@Epic Cu u v g).
Fail Check (@Monic Cu u v g).
Fail Check (@Section Cu u v g).
Fail Check (@Retraction Cu u v g).

End HomProofDonor.

Section AdjunctionHomDonor.

Universes ao ah bo bh.
Constraint ah < bh.

Context (Cu : Category@{ao ah ah}).
Context (Du : Category@{bo bh bh}).

(*
CONTROL accepted at these levels: a functor in the direction the
   constraint allows.

--------
在这些级别上接受控制：沿约束允许的方向的函子。
*)

Check (Cu ⟶ Du).

(*
NEGATIVE 7 (FORMABILITY).  The other direction is rejected, because
   [Functor] forces the source's hom universe below the target's.  So the
   block equation `u0 = u2` on the theorem file's headlines needs no
   appeal to [Adjunction] at all: the mere presence of functors in BOTH
   directions already forces it, and [Adjunction] cannot be tested apart
   from that, since its very type mentions both.  Stripped and compiled
   alone this ends "universe inconsistency".

--------
负面 7（可形成性）。 另一方向被拒绝，因为 [Functor] 强制源同域低于目标同域。因此，定理文件标题上的块方程 `u0 = u2` 根本不需要诉诸 [Adjunction]：仅在两个方向上存在函子就已经强制了它，并且 [Adjunction] 也无法单独测试，因为它的类型本身涉及两者。单独剥离和编译会以“宇宙不一致”结束。
*)

Fail Check (Du ⟶ Cu).

End AdjunctionHomDonor.

(* ------------------------------------------------------------------ *)
(** ** (5) The prior art, checked against the target at one type / ** (5) 将现有技术与目标在一种类型下进行比较 *)

(*
Instance/Coq/Monoid/Free.v's [adjunction_counit_epic] already
   proves the forward half of Theorem 1(i) for an ARBITRARY adjunction.
   The target restates it (by a different proof, through the transfer
   lemma) rather than consuming it, because that constant lives in the
   `Instance/Coq` layer.  That the two STATEMENTS are the same is
   machine-checked here: both are ascribed to one type.

--------
Instance/Coq/Monoid/Free.v 的 [adjunction_counit_epic] 已经证明了定理 1(i) 的前半部分，对于任意的伴随。目标是重新表述它（通过一个不同的证明，通过转移引理）而不是直接使用它，因为该常量位于 `Instance/Coq` 层。这里机器检查了两个陈述是相同的：两者都被归属于同一个类型。
*)

Section PriorArt.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Definition ctrl_prior_art_free (HU : Functor.Faithful U) (a : C) :
  Epic (@counit C D F U A a) :=
  adjunction_counit_epic A HU a.

Definition ctrl_prior_art_target (HU : Functor.Faithful U) (a : C) :
  Epic (@counit C D F U A a) :=
  @counit_epic_of_faithful C D F U A HU a.

(*
And the two [Retraction] readings of `U ε` agree in type as well:
   Free.v and Fullness.v's whiskered development.

--------
而两个 [Retraction] 对 `U ε` 的读数在类型上也一致：
   Free.v 和 Fullness.v 的带须发展。
*)

Check (@adjunction_counit_underlying_retraction C D F U A).

End PriorArt.

(* ------------------------------------------------------------------ *)
(** ** (6) Non-vacuity, quadrant one: full and NOT faithful / ** （6）非空性，第一象限：完整且不忠实 *)

(*
#368's witness, read through Theorem 1.  [Erase PointedSets] is the
   right adjoint of [zero_erase_adjunction], it is FULL because
   [PointedSets] has a zero object (Fullness.v), and it is provably
   NOT faithful (Fullness.v).  So by (ii) every counit component
   splits, and by (i) — contrapositive — the counit family is NOT
   componentwise epi.  The second is new content: Fullness.v refutes only
   invertibility of the component at [PointedTwo].

   DEGENERACY, labelled: the target of [Erase] is the terminal category
   [_1], so fullness holds for a reason unrelated to the theorem (every
   hom-set of [_1] is a singleton, and the zero morphism hits it).  What
   the witness exercises is the CONTRAPOSITIVE of (i) and the forward half
   of (ii), not a subtle adjunction.

--------
#368 的证人，通读定理 1。[Erase PointedSets] 是 [zero_erase_adjunction] 的右伴随，它是全的，因为 [PointedSets] 有零对象（Fullness.v），并且可以证明它不是忠实的（Fullness.v）。所以根据 (ii) 每个余单位分量都是可分裂的，并且根据 (i) — 逆否命题 — 余单位族不是分量层面的满射。第二点是新的内容：Fullness.v 仅否定 [PointedTwo] 处分量的可逆性。

退化性，标记为：[Erase] 的目标是终类别 [_1]，因此全性成立的原因与定理无关（[_1] 的每个 Hom 集都是单元素集，并且零态射命中它）。证人所展示的是 (i) 的逆否命题和 (ii) 的正向部分，而不是一个微妙的伴随关系。
*)

Definition pointed_erase_adj :
  @Diagonal PointedSets _1
    (@initial_obj PointedSets (@zero_initial PointedSets PointedSets_Zero))
  ⊣ Erase PointedSets :=
  zero_erase_adjunction PointedSets_Zero.

Definition pointed_counit_Section (a : PointedSets) :
  Section (@counit PointedSets _1 _ (Erase PointedSets)
             pointed_erase_adj a) :=
  fst (@right_adjoint_full_iff_counit_split_monic PointedSets _1 _
         (Erase PointedSets) pointed_erase_adj)
      (Full_Erase_of_ZeroObject PointedSets_Zero) a.

Lemma pointed_counit_family_not_Epic :
  (∀ a : PointedSets,
      Epic (@counit PointedSets _1 _ (Erase PointedSets)
              pointed_erase_adj a)) → False.
Proof.
  intros H.
  apply Erase_PointedSets_not_Faithful.
  exact (snd (@right_adjoint_faithful_iff_counit_epic PointedSets _1 _
                (Erase PointedSets) pointed_erase_adj) H).
Qed.

(*
The pre-existing refutation of invertibility at [PointedTwo], recorded
   beside them so the three readings sit together.

--------
在 [PointedTwo] 对可逆性的先前反驳，记录在它们旁边，以便这三个读数放在一起。
*)

Check pointed_counit_not_IsIsomorphism.

(* ------------------------------------------------------------------ *)
(** ** (7) Non-vacuity, quadrant two: faithful and NOT full / ** (7) 非空性，象限二：忠实而非完整 *)

(*
The free-monoid adjunction over [Coq] (Instance/Coq/Monoid/Free.v).
   Its right adjoint is the forgetful functor to [Coq]; it is faithful
   because a monoid morphism there IS a function paired with a property
   and the hom-setoid compares the functions, and it is NOT full because
   a function between underlying sets need not preserve the unit.  By (i)
   every counit component is epi; by (ii) — contrapositive — the counit
   family does NOT split.

   NON-DEGENERACY: the refutation of fullness evaluates the recovered
   homomorphism at the UNIT, where the chosen non-homomorphism
   `fun _ => cons true nil` provably differs from it, so the witness is
   not the empty-hom-set kind.

--------
自由幺半群伴随于 [Coq]（实例/Coq/Monoid/Free.v）。
它的右伴随是到 [Coq] 的遗忘函子；它是忠实的，因为那里的幺半群态射是带有属性的函数，并且同态集类比较的是函数；它不是满的，因为基础集合之间的函数不一定保持单位元。根据（i）每个余单位分量都是满射；根据（ii）—逆否命题—余单位族不分裂。

非退化性：对满性的反驳在单位元处对恢复的同态进行评估，其中选择的非同态 `fun _ => cons true nil` 可证明与其不同，因此证据不是空同态集类型。
*)

Definition mon_coq_forget : @Mon Coq Coq_Monoidal ⟶ Coq :=
  @Mon_Forget Coq Coq_Monoidal.

Definition free_mon_faithful : Functor.Faithful mon_coq_forget.
Proof. constructor; intros x y f g H; exact H. Qed.

Definition free_mon_counit_Epic (L : @Mon Coq Coq_Monoidal) :
  Epic (@counit (@Mon Coq Coq_Monoidal) Coq FreeMonoid mon_coq_forget
          free_monoid_adjunction L) :=
  fst (@right_adjoint_faithful_iff_counit_epic
         (@Mon Coq Coq_Monoidal) Coq FreeMonoid mon_coq_forget
         free_monoid_adjunction) free_mon_faithful L.

Lemma free_mon_forget_not_Full : Functor.Full mon_coq_forget → False.
Proof.
  intros HFull.
  pose (W := FreeMon bool).
  pose (k := (fun _ : list bool => Datatypes.cons true Datatypes.nil)
             : mon_coq_forget W ~{Coq}~> mon_coq_forget W).
  pose proof (@fmap_sur _ _ mon_coq_forget HFull W W k) as Hs.
  pose proof (hom_mone (@prefmap _ _ mon_coq_forget HFull W W k)) as Hu.
  specialize (Hs (@mone W)).
  simpl in Hs, Hu.
  rewrite Hu in Hs.
  discriminate Hs.
Qed.

Lemma free_mon_counit_family_not_Section :
  (∀ L : @Mon Coq Coq_Monoidal,
      Section (@counit (@Mon Coq Coq_Monoidal) Coq FreeMonoid
                 mon_coq_forget free_monoid_adjunction L)) → False.
Proof.
  intros H.
  apply free_mon_forget_not_Full.
  exact (snd (@right_adjoint_full_iff_counit_split_monic
                (@Mon Coq Coq_Monoidal) Coq FreeMonoid mon_coq_forget
                free_monoid_adjunction) H).
Qed.

(*
And the combined reading: by (iii), the counit of this adjunction is
   not a componentwise isomorphism either.

--------
以及综合理解：根据（iii），该伴随关系的余单位也不是按组分的同构。
*)

Lemma free_mon_counit_family_not_iso :
  (∀ L : @Mon Coq Coq_Monoidal,
      IsIsomorphism (@counit (@Mon Coq Coq_Monoidal) Coq FreeMonoid
                       mon_coq_forget free_monoid_adjunction L)) → False.
Proof.
  intros H.
  apply free_mon_forget_not_Full.
  exact (fst (snd (@right_adjoint_fully_faithful_iff_counit_iso
                     (@Mon Coq Coq_Monoidal) Coq FreeMonoid
                     mon_coq_forget free_monoid_adjunction) H)).
Qed.

(* ------------------------------------------------------------------ *)
(** ** (8) The remaining headline names, checked from outside / ** (8) 其余的标题名称，从外部检查 *)

(*
Every target constant that a negative above names appears in a
   succeeding command; these [Check]s cover the rest of the two files'
   headline surface, so that a rename of any of them breaks this file at
   a NON-[Fail] line.

--------
每个负数以上命名的目标常量出现在随后的命令中；这些 [Check] 覆盖了另外两文件的标题表面，因此重命名其中的任何一个都会在非 [Fail] 行破坏此文件。
*)

Check @hom_transfer_monic_iff_epic.
Check @hom_transfer_epic_iff_section.
Check @hom_transfer_component.
Check @hom_transfer_component_injective_iff.
Check @hom_transfer_component_surjective_iff.
Check @epic_of_hom_transfer_monic.
Check @hom_transfer_monic_of_epic.
Check @section_of_hom_transfer_epic.
Check @hom_transfer_epic_of_section.
Check @Epic_Section_IsIsomorphism.
Check @counit_precomp_is_from_adj_fmap_U.
Check @transfer_at_counit_is_precomp.
Check @fmap_U_is_transfer_then_transpose.
Check @counit_transfer_monic_of_faithful.
Check @counit_epic_of_faithful.
Check @faithful_of_counit_epic.
Check @right_adjoint_faithful_iff_counit_epic.
Check @counit_transfer_epic_of_full.
Check @counit_section_via_transfer.
Check @full_data_of_counit_section.
Check @full_of_counit_section.
Check @right_adjoint_fully_faithful_iff_counit_iso.
Check @from_adj_id_is_counit.
Check @from_adj_epic_of_epic_direct.
Check @from_adj_epic_of_epic.
Check @right_adjoint_faithful_iff_from_adj_epic.
Check @op_counit_is_unit.
Check @op_unit_is_counit.
Check @left_adjoint_faithful_iff_unit_monic.
Check @left_adjoint_full_iff_unit_split_epic.
Check @left_adjoint_fully_faithful_iff_unit_iso.
Check @unit_retract_agrees.
Check @reflective_incl_Full.
Check @reflective_incl_Faithful.
Check @reflective_counit_Isomorphism_general.
Check @reflection_counit_Epic.
