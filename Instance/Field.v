Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Rng.
Require Import Category.Instance.FdVect.
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

Generalizable All Variables.

(*
   * * Field: the category of fields, and the determination of its monos

   Riehl, “Category Theory in Context”, §1.2 Exercise 1.2.iii (printed
   p. 15): “show that every morphism in the category of fields is a
   monomorphism” [riehl:1.2:exiii], and §1.6 Example 1.6.15 (printed
   p. 38), the field half: the category of fields has NEITHER an
   initial NOR a terminal object [riehl:1.6:example15].  These are the
   one entry of the standard roster (Mac Lane §I.7, Awodey §1.4, Riehl
   1.1.3) that asks for mathematics rather than bookkeeping: the roster
   entries around it — Grp, Ab, Rng, RMod, Top — are constructions,
   whereas these are theorems about the category once built.
   nLab: https://ncatlab.org/nlab/show/field
   Wikipedia: https://en.wikipedia.org/wiki/Field_(mathematics)

   OBJECTS AND MORPHISMS.  [FieldObject] is Instance/FdVect.v's record —
   a [RingObject] with commutative multiplication, a separated unit
   (1 ≉ 0), and a TOTAL inverse operation [finv] whose defining law
   [finv_l] is asserted only away from zero.  Totality is forced by the
   setoid discipline (a partial operation is not a setoid map), so
   [finv (rig_zero F)] is a junk value, constrained by nothing except
   [finv_respects]; every statement below that mentions [finv] carries
   the nonzeroness hypothesis that makes it meaningful.

   Morphisms are the ring homomorphisms of Instance/Rng.v, i.e. the
   [RigHom]s of Theory/Algebra/Rig.v, which preserve 0, +, 1 and ·.  No
   further preservation is demanded, and none may be: preservation of
   negation is Rig.v's theorem [RigHom_neg], and preservation of
   inverses is the theorem [field_hom_finv] below, holding at every
   nonzero argument by uniqueness of two-sided inverses.  At zero it is
   NOT claimed — both sides are junk values of two unrelated [finv]s,
   and nothing relates them.

   THE DETERMINATION, and its exact constructive strength.  The
   classical argument is short: a homomorphism of fields carrying
   a and b to a common value carries a − b to 0; were a − b nonzero it
   would be invertible, and its image would be an invertible zero,
   forcing 1 ≈ 0 in the target.  That argument is available here
   verbatim and is [field_hom_distinct], stated in the form the
   argument actually produces:

   a ≉ b  →  f a ≉ f b

   — distinct elements have distinct images, unconditionally and
   axiom-free.  What the argument does NOT produce is the strict
   cancellation form [f a ≈ f b → a ≈ b].  Running it under the
   hypothesis [f a ≈ f b] yields ¬¬(a ≈ b), and no field axiom carries
   that back to a ≈ b: the record supplies [finv] together with a law
   holding away from zero, not a decision between “zero” and
   “invertible”.  This is exactly the shape of Instance/Grp/Epi.v,
   where surjectivity of a group epimorphism is delivered as the
   unconditional density theorem [grp_epic_image_dense] and the
   classical biconditional is its double-negation elimination; the
   same discipline is followed here, and for the same reason.

   So the hypothesis is named rather than smuggled: [FieldStable F]
   says that ≈ on F is ¬¬-stable.  It is discharged by decidable
   equality ([field_dec_stable]), hence holds for both fields in the
   tree ([Q_Field_stable], [F2_Field_stable]).  Two results say where
   it sits.  [stability_is_the_conclusion] shows that under the
   premise [f a ≈ f b] the hypothesis INSTANCE at (a, b) and the
   conclusion a ≈ b inter-derive — a single-instance statement, not
   the quantified biconditional Instance/Grp/Epi.v proves, and it is
   labelled as such where it is stated.  [FieldStableAtZero], with
   [field_stable_at_zero_suffices] and the two inter-derivability
   lemmas, locates the obstruction: stability is ever used only at
   zero, which is precisely the guard on [finv_l], and the zero-only
   form is equivalent to the pairwise one.  With either,
   [field_monic] gives Riehl's conclusion per morphism and
   [field_every_monic] gives it in the blanket form the exercise
   states.  No countermodel is offered: whether some field has
   unstable equality is left open, not asserted either way.

   NO INITIAL AND NO TERMINAL OBJECT.  Riehl's Example 1.6.15 is
   delivered as [Field_no_initial] and [Field_no_terminal], with the
   object-level readings [Field_no_initial_obj] and
   [Field_no_terminal_obj] — no object of [Field] is initial, and none
   is terminal — obtained through Structure/Terminal.v's
   [IsTerminalObj]/[IsInitialObj] bundling.  The separating pair is ℚ
   against [F2_Field], the two-element field built here on [bool]:
   characteristic 0 against characteristic 2.  Both proofs are
   CONSTRUCTIVE and consult no decision procedure — the guard on
   [finv_l] is a negation, so the negative fact “1 + 1 is not zero
   here” is itself the licence to invert, and neither [FieldStable]
   nor decidability appears in either proof.  The same pair also gives
   [no_hom_Q_F2] and [no_hom_F2_Q]: there is no homomorphism in either
   direction, so [Field] is not even connected.

   THE CONVERSE IS NOT CLAIMED.  “Monic ⟺ injective” would need the
   monic ⇒ injective direction, and that needs a probe object — the
   free field on one generator, which does not exist in this tree.  The
   analogous probes elsewhere show what is missing rather than that the
   pattern is unavailable: Instance/Sets.v probes with the singleton,
   and Instance/Rng.v's own monic ⇒ injective — deferred there when this
   was written, pending the polynomial ring ℤ[x] — is now proved, as
   [rng_monic_injective] in Instance/Rng/Polynomial.v, using exactly
   that probe.  No such object is available for fields.  Riehl's
   exercise concludes that every morphism is monic, and that is what is
   delivered.

   WITNESSES.  ℚ is an object ([Q_Field], from FdVect.v) and F₂ is a
   second one, built here; the identity is a morphism; every
   homomorphism out of either is monic with no hypothesis at all
   ([Q_hom_monic], [F2_hom_monic]); and ℚ is rigid — its only ring
   endomorphism is the identity ([Q_endo_id]), by initiality of ℤ
   followed by cancellation of the denominator.

   AXIOMS.  Everything here is axiom-free, counted the way
   docs/AXIOMS.md counts: all 76 constants the module declares — the
   50 source-level definitions and theorems, the 2 [Faithful]
   instances, and the 24 [Program] obligations, which no [.glob] sweep
   sees — report “Closed under the global context”.  The arithmetic is
   Theory/Algebra/Rig.v's, the concrete carriers are [bool] and stdlib
   [QArith], and neither needs an axiom.  In particular nothing in
   this file touches the reals. 

   --------
   * * 域：域的范畴及其单态的判定

   Riehl，《上下文中的范畴论》，§1.2 练习 1.2.iii（印刷第 15 页）：“证明域的范畴中的每个态射都是单态射” [riehl:1.2:exiii]，以及 §1.6 示例 1.6.15（印刷第 38 页），半域：域的范畴既没有初对象也没有末对象 [riehl:1.6:example15]。这些是标准清单（Mac Lane §I.7, Awodey §1.4, Riehl 1.1.3）中的唯一条目，它要求数学推导而不是记账：其周围的清单条目 — Grp, Ab, Rng, RMod, Top — 是构造，而这些是在构建后关于该范畴的定理。
   nLab: https://ncatlab.org/nlab/show/field
   维基百科: https://en.wikipedia.org/wiki/Field_(mathematics)对象与态射。[FieldObject] 是 Instance/FdVect.v 的记录——一个具有交换乘法的 [RingObject]，具有分离单位（1 ≉ 0），以及一个总逆操作 [finv]，其定义律 [finv_l] 仅在非零时成立。总性是由集合体纪律强制的（部分操作不是集合体映射），因此 [finv (rig_zero F)] 是一个垃圾值，仅受 [finv_respects] 约束；下面提到 [finv] 的每个陈述都带有使其有意义的非零假设。态射是 Instance/Rng.v 的环同态，即 Theory/Algebra/Rig.v 中的 [RigHom]，它们保持 0、+、1 和 ·。不要求也不能要求进一步的保持：保持取反是 Rig.v 的定理 [RigHom_neg]，而保持逆元是下文定理 [field_hom_finv]，通过双边逆的唯一性在每个非零自变量上成立。在零点不作任何声明——两边都是两个不相关 [finv] 的无用值，彼此之间没有任何联系。决定性及其确切的构造强度。经典论证很简短：一个将 a 和 b 映射到相同值的域同态会把 a − b 映射到 0；若 a − b 非零，则它是可逆的，而它的像会是可逆的零，从而在目标中导致 1 ≈ 0。这里可以逐字使用该论证，并且在论证实际上产生的形式中表述为 [field_hom_distinct]：

   a ≉ b  →  f a ≉ f b— 不同的元素有不同的图像，无条件且无公理限制。论证并不会产生严格的消去形式 [f a ≈ f b → a ≈ b]。在假设 [f a ≈ f b] 下运行它，会得到 ¬¬(a ≈ b)，而没有任何域公理可以将其推回到 a ≈ b：记录提供了 [finv] 以及一个在零点以外成立的定律，而不是在“零”和“可逆”之间做出决定。这正是 Instance/Grp/Epi.v 的形式，其中群上满射的满射性作为无条件的稠密性定理 [grp_epic_image_dense] 给出，而经典的双条件式则是其双重否定消去；这里遵循的是相同的规律，原因也相同。因此，该假设是被命名而不是被走私的：[FieldStable F] 说 F 上的 ≈ 是 ¬¬-稳定的。它可以通过可判定的等式 ([field_dec_stable]) 消解，因此在树中的两个字段上都成立 ([Q_Field_stable], [F2_Field_stable])。两个结果说明了它的位置。[stability_is_the_conclusion] 表明在前提 [f a ≈ f b] 下，假设 INSTANCE 在 (a, b) 处与结论 a ≈ b 可以相互推导——这是单一实例的语句，而不是 Instance/Grp/Epi.v 中的量化等值，并且在其陈述处标记为此类。[FieldStableAtZero]，结合 [field_stable_at_zero_suffices] 和两个相互可推导性引理，定位了障碍：稳定性仅在零处使用，这正是 [finv_l] 的保护条件，而仅零形式等价于两两形式。无论哪种情况，[field_monic] 都根据态射给出了 Riehl 的结论，而 [field_every_monic] 则以习题中所述的通用形式给出该结论。没有提供反例模型：某个域是否具有不稳定的等式仍未确定，也没有进行任何断言。没有初始对象也没有终端对象。Riehl 的例 1.6.15 被表示为 [Field_no_initial] 和 [Field_no_terminal]，其对象级读数为 [Field_no_initial_obj] 和 [Field_no_terminal_obj] —— [Field] 的对象既不是初始对象，也不是终端对象 —— 通过 Structure/Terminal.v 的 [IsTerminalObj] / [IsInitialObj] 捆绑获得。分离对是 ℚ 和 [F2_Field] ，这里在 [bool] 上构建了一个二元素域：特征 0 对特征 2。两个证明都是构造性的，并且不参考任何判定过程 —— [finv_l] 上的守卫是一个否定，因此负事实“这里 1 + 1 不为零”本身就是反演的许可，并且 [FieldStable] 和可判定性都没有出现在任一证明中。同一对还给出了 [no_hom_Q_F2] 和 [no_hom_F2_Q]：在任一方向上都不存在同态，所以 [Field] 甚至都不是连通的。逆命题未被断言。“Monic ⟺ injective”需要 monic ⇒ injective 方向，而这需要一个探针对象——一个生成元上的自由域，而这个在这个树中不存在。其他地方的类似探针展示了缺失的内容，而不是该模式不可用：Instance/Sets.v 使用单元素进行探针，而 Instance/Rng.v 中自己的 monic ⇒ injective——在编写时被推迟，等候多项式环 ℤ [x]——现在已经证明，如 Instance/Rng/Polynomial.v 中的 [rng_monic_injective]，使用的正是该探针。域没有这样的对象可用。Riehl 的练习结论是每个态射都是 monic，这正是给出的结果。证据。ℚ 是一个对象（[Q_Field]，来自 FdVect.v），F₂ 是第二个对象，这里构建的；恒等映射是一个态射；从任意一个对象到外部的每个同态都是单射，且无需任何假设（[Q_hom_monic]，[F2_hom_monic]）；并且 ℚ 是刚性的——它唯一的环自同态是恒等映射（[Q_endo_id]），通过 ℤ 的初始性然后消去分母得出。公理。这里的一切都是无公理的，计数方式与 docs/AXIOMS.md 一致：模块声明的所有 76 个常量——50 个源级别定义和定理，2 个 [Faithful] 实例，以及 24 个 [Program] 义务，没有 [.glob] 清扫会看到——报告“在全局上下文下封闭”。算术使用的是 Theory/Algebra/Rig.v 的，具体载体是 [bool] 和 stdlib [QArith]，而且都不需要公理。特别是，本文件中的内容不涉及实数。
*)

#[local] Obligation Tactic := idtac.

(** ** The category / ** 类别 *)

(*
 Objects are fields, morphisms are ring homomorphisms of the
 underlying rings, and the hom-setoid is Rig.v's — pointwise
 equivalence of the underlying setoid maps.  The shape mirrors
 Instance/Rng.v's [Ring] exactly, since a field homomorphism IS a ring
 homomorphism: see the header on why no inverse-preservation clause is
 demanded. 

 --------
 对象是域，态射是底层环的环同态，而同态集则是 Rig.v 的 —— 底层集同态映射的按点等价。这个结构完全镜像了 Instance/Rng.v 的 [Ring]，因为域同态本身就是环同态：参见头部说明为什么不要求逆映射保持条款。
*)
Program Definition Field : Category := {|
  obj     := FieldObject;
  hom     := fun F K => RigHom F K;
  homset  := fun F K => @RigHom_Setoid F K;
  id      := fun F => @rig_hom_id F;
  compose := fun _ _ _ f g => rig_hom_compose f g;

  compose_respects := fun _ _ _ => @rig_hom_compose_respects _ _ _
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

(* * ** The evident forgetful functors / * ** 明显的忘记函子 *)

(*
 To rings: identity on morphisms, since the two hom notions coincide.
 This is the inclusion of the roster entry into its neighbour, and it
 is faithful for the same definitional reason [Rng_Forget] is. 

 --------
 对于环：在态射上的恒等，因为这两个同态的概念是相同的。这是名册条目进入其邻居的包含，并且出于与 [Rng_Forget] 相同的定义原因，它是忠实的。
*)
Program Definition Field_Rng : Field ⟶ Rng := {|
  fobj := fun F : FieldObject => field_ring F;
  fmap := fun _ _ f => f
|}.
Next Obligation. intros F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F a; simpl; reflexivity. Qed.
Next Obligation. intros F K T f g a; simpl; reflexivity. Qed.

#[export] Instance Field_Rng_Faithful : Faithful Field_Rng.
Proof. constructor; intros F K f g E; exact E. Qed.

(* To setoids: the underlying set, Mac Lane's roster column. / 对于宿结构：基础集合，麦克莱恩的名册栏。 *)
Program Definition Field_Forget : Field ⟶ Sets := {|
  fobj := fun F : FieldObject => rig_setoid F;
  fmap := fun F K f => rig_map f
|}.
Next Obligation. intros F K f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros F a; simpl; reflexivity. Qed.
Next Obligation. intros F K T f g a; simpl; reflexivity. Qed.

#[export] Instance Field_Forget_Faithful : Faithful Field_Forget.
Proof. constructor; intros F K f g E; exact E. Qed.

(* * ** Homomorphisms reflect nothing into zero / * ** 同态不将任何东西映射为零 *)

(*
 The engine of the whole file.  If x is nonzero it is invertible, so
 1 ≈ f (x⁻¹ · x) ≈ f (x⁻¹) · f x; were f x zero the right-hand side
 would be zero, and the target's [field_one_neq_zero] refutes 1 ≈ 0.
 Unconditional: no stability, no decidability, no choice. 

 --------
 整个文件的引擎。如果 x 非零，它是可逆的，所以
 1 ≈ f (x⁻¹ · x) ≈ f (x⁻¹) · f x；如果 f x 为零，右边将为零，而目标的 [field_one_neq_zero] 否定 1 ≈ 0。
 无条件：没有稳定性，没有可判定性，没有选择。
*)
Lemma field_hom_nonzero {F K : FieldObject} (f : RigHom F K)
  (x : carrier (rig_setoid F)) :
  (x ≈ rig_zero F → False) → (rig_map f x ≈ rig_zero K → False).
Proof.
  intros Hx Hfx.
  apply (field_one_neq_zero K).
  transitivity (rig_map f (rig_one F)).
  - symmetry; apply (rig_map_one f).
  - transitivity (rig_map f (rig_mul F (finv F x) x)).
    + apply (proper_morphism (rig_map f)).
      symmetry; now apply finv_l.
    + rewrite (rig_map_mul f).
      rewrite Hfx.
      apply rig_mul_zero_r.
Qed.

(*
 Preservation of inverses is a theorem, not a clause of the morphism
 notion: f (x⁻¹) left-inverts f x, and (f x)⁻¹ right-inverts it — the
 latter by [finv_r], which needs f x to be nonzero, which is the
 previous lemma — so Rng.v's [rig_inv_unique] identifies them.  At
 x ≈ 0 no claim is made; see the header. 

 --------
 逆元的保持是一个定理，而不是态射概念的一个条款：f (x⁻¹) 左逆 f x，而 (f x)⁻¹ 右逆它——后者通过 [finv_r]，这需要 f x 非零，这是前一个引理——因此 Rng.v 的 [rig_inv_unique] 识别了它们。在 x ≈ 0 时没有任何主张；参见标题。
*)
Lemma field_hom_finv {F K : FieldObject} (f : RigHom F K)
  (x : carrier (rig_setoid F)) (Hx : x ≈ rig_zero F → False) :
  rig_map f (finv F x) ≈ finv K (rig_map f x).
Proof.
  apply (rig_inv_unique K (rig_map f x)).
  - rewrite <- (rig_map_mul f).
    transitivity (rig_map f (rig_one F)).
    + apply (proper_morphism (rig_map f)); now apply finv_l.
    + apply (rig_map_one f).
  - apply finv_r.
    now apply (field_hom_nonzero f x Hx).
Qed.

(* * ** Riehl 1.2.iii: distinct elements have distinct images / * ** Riehl 1.2.iii：不同的元素有不同的像 *)

(*
 A difference vanishing forces the two elements to agree — pure ring
 arithmetic, isolated so the field argument below reads cleanly. 

 --------
 一个差异消失迫使两个元素一致——纯环算术，孤立，因此下面的域论证读起来清晰。
*)
Lemma ring_sub_zero (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_add R a (ring_neg R b) ≈ rig_zero R → a ≈ b.
Proof.
  intro H.
  transitivity (rig_add R (rig_add R a (ring_neg R b)) b).
  - rewrite rig_add_assoc.
    rewrite (ring_neg_l R b).
    symmetry; apply rig_add_zero_r.
  - rewrite H.
    apply rig_add_zero_l.
Qed.

(* ... and the converse, which the stability analysis below needs. / ... 以及相反的情况，这是下面的稳定性分析所需要的。 *)
Lemma ring_zero_sub (R : RingObject) (a b : carrier (rig_setoid R)) :
  a ≈ b → rig_add R a (ring_neg R b) ≈ rig_zero R.
Proof.
  intro H.
  rewrite H.
  rewrite rig_add_comm.
  apply ring_neg_l.
Qed.

(* Agreement of the images sends the difference to zero. Isolated because both [field_hom_distinct] and [field_stable_at_zero_suffices] consume exactly this step and nothing else. / 图像的一致性将差值归零。孤立，因为 [field_hom_distinct] 和 [field_stable_at_zero_suffices] 都仅消耗这一步而不消耗其他步骤。 *)
Lemma field_hom_sub_zero {F K : FieldObject} (f : RigHom F K)
  (a b : carrier (rig_setoid F)) :
  rig_map f a ≈ rig_map f b →
  rig_map f (rig_add F a (ring_neg F b)) ≈ rig_zero K.
Proof.
  intro Hab.
  rewrite (rig_map_add f).
  rewrite (RigHom_neg F K f b).
  rewrite Hab.
  rewrite rig_add_comm.
  apply (ring_neg_l K (rig_map f b)).
Qed.

(*
 The exercise's argument, in the form it actually produces.  Given
 a ≉ b, the difference a − b is nonzero, so by [field_hom_nonzero] its
 image is nonzero; but that image is f a − f b, which any agreement of
 f a with f b would send to zero. 

 --------
 练习的论证，以它实际产生的形式。给定 a ≉ b，差 a − b 非零，因此根据 [field_hom_nonzero] 它的像是非零的；但这个像是 f a − f b，任何 f a 与 f b 的一致都会使其变为零。
*)
Theorem field_hom_distinct {F K : FieldObject} (f : RigHom F K)
  (a b : carrier (rig_setoid F)) :
  (a ≈ b → False) → (rig_map f a ≈ rig_map f b → False).
Proof.
  intros Hne Hab.
  (* the difference is nonzero, since a vanishing difference gives a ≈ b / 差值是非零的，因为消失的差值意味着 a ≈ b *)
  assert (Hd : rig_add F a (ring_neg F b) ≈ rig_zero F → False).
  { intro H; apply Hne; exact (ring_sub_zero F a b H). }
  (* yet its image vanishes / 然而它的影像消失了 *)
  exact (field_hom_nonzero f _ Hd (field_hom_sub_zero f a b Hab)).
Qed.

(* The same content stated positively: the double negation of injectivity holds outright. This is the exact unconditional strength — cf. Instance/Grp/Epi.v's [grp_epic_image_dense]. / 以积极的方式陈述相同的内容：单射性的双重否定直接成立。这就是精确的无条件强度——参见 Instance/Grp/Epi.v 的 [grp_epic_image_dense]。 *)
Corollary field_hom_injective_nn {F K : FieldObject} (f : RigHom F K)
  (a b : carrier (rig_setoid F)) :
  rig_map f a ≈ rig_map f b → ((a ≈ b → False) → False).
Proof.
  intros Hab Hne.
  exact (field_hom_distinct f a b Hne Hab).
Qed.

(* * ** The named hypothesis, and that it is exactly the missing step / * ** 所谓的假设，以及它正好是缺失的步骤 *)

(* Stability of ≈ under double negation. Named rather than assumed silently, and discharged below for every field with decidable equality. / 在双重否定下 ≈ 的稳定性。命名而非假设，静默处理，并在下面对每个具有可判定等式的域进行释放。 *)
Definition FieldStable (F : FieldObject) : Type :=
  ∀ a b : carrier (rig_setoid F), ((a ≈ b → False) → False) → a ≈ b.

Lemma field_dec_stable (F : FieldObject)
  (dec : ∀ a b : carrier (rig_setoid F), (a ≈ b) + (a ≈ b → False)) :
  FieldStable F.
Proof.
  intros a b Hnn.
  destruct (dec a b) as [H | H].
  - exact H.
  - destruct (Hnn H).
Qed.

(*
 Nothing weaker can serve, for a reason that needs no proof of
 independence: under the premise [f a ≈ f b] the hypothesis INSTANCE
 at (a, b) and the conclusion a ≈ b inter-derive — forward by feeding
 the instance the theorem above, backward by discarding its argument.
 Read it as exactly that, a single-instance inter-derivation under the
 premise, and not as the quantified biconditional Instance/Grp/Epi.v's
 [stability_is_the_conclusion] proves; no claim is made here about the
 quantified forms. 

 --------
 没有更弱的条件可以适用，这是不需要独立性证明的理由：在前提 [f a ≈ f b] 下，假设 INSTANCE 在 (a, b) 处和结论 a ≈ b 相互推导——向前是通过给该实例提供上面的定理，向后是通过丢弃它的参数。正是按这个意思理解，把它看作在前提下的单实例相互推导，而不是量化的等价条件 Instance/Grp/Epi.v 中 [stability_is_the_conclusion] 所证明的那样；这里对量化形式不作任何声明。
*)
Theorem stability_is_the_conclusion {F K : FieldObject} (f : RigHom F K)
  (a b : carrier (rig_setoid F)) (Hab : rig_map f a ≈ rig_map f b) :
  ((((a ≈ b → False) → False) → a ≈ b) → a ≈ b) *
  ((a ≈ b) → (((a ≈ b → False) → False) → a ≈ b)).
Proof.
  split.
  - intro Hstab.
    apply Hstab.
    exact (field_hom_injective_nn f a b Hab).
  - intros H _; exact H.
Qed.

(* * ** The hypothesis is only ever used at zero / * ** 这个假设只在零时使用 *)

(*
 [FieldStable] quantifies over pairs, but every use below reduces the
 pair (a, b) to the single element a − b through [ring_sub_zero].  So
 the weaker-looking hypothesis “≈ is ¬¬-stable AT ZERO” already
 suffices — and it is not in fact weaker, the two being
 inter-derivable ([field_stable_stable_at_zero] and
 [field_stable_at_zero_stable]).  This turns what the header would
 otherwise have to assert into a proved statement, and it locates the
 obstruction exactly: it is about deciding “is this element zero?”,
 which is the guard on [finv_l], and about nothing else. 

 --------
 [FieldStable] 对成对元素进行量化，但下面的每一次使用通过 [ring_sub_zero] 将对 (a, b) 简化为单个元素 a − b。因此，看起来较弱的假设“≈ 在零点是 ¬¬-稳定的”已经足够——事实上它并不比原假设弱，这两者是可相互推导的（[field_stable_stable_at_zero] 和 [field_stable_at_zero_stable]）。这将原本标题需要断言的内容变成了一个已经证明的陈述，而且它准确地找到阻碍所在：它关乎于决定“该元素是否为零？”，这正是 [finv_l] 的控制条件，而与其他无关。
*)
Definition FieldStableAtZero (F : FieldObject) : Type :=
  ∀ a : carrier (rig_setoid F),
    ((a ≈ rig_zero F → False) → False) → a ≈ rig_zero F.

Definition field_stable_stable_at_zero (F : FieldObject) :
  FieldStable F → FieldStableAtZero F :=
  fun HF a => HF a (rig_zero F).

Lemma field_stable_at_zero_stable (F : FieldObject) :
  FieldStableAtZero F → FieldStable F.
Proof.
  intros HF a b Hnn.
  apply (ring_sub_zero F a b).
  apply HF.
  intro Hd.
  apply Hnn.
  intro Hab.
  exact (Hd (ring_zero_sub F a b Hab)).
Qed.

(* Cancellation from the zero-only form directly, spending no more than [field_hom_sub_zero] and [field_hom_nonzero]. / 直接从仅零表单取消，花费不超过 [field_hom_sub_zero] 和 [field_hom_nonzero]。 *)
Theorem field_stable_at_zero_suffices {F K : FieldObject} (f : RigHom F K)
  (HF : FieldStableAtZero F) (a b : carrier (rig_setoid F)) :
  rig_map f a ≈ rig_map f b → a ≈ b.
Proof.
  intro Hab.
  apply (ring_sub_zero F a b).
  apply HF.
  intro Hd.
  exact (field_hom_nonzero f _ Hd (field_hom_sub_zero f a b Hab)).
Qed.

(* * ** Injectivity and Riehl's conclusion / * ** 单射性与Riehl的结论 *)

Theorem field_hom_injective {F K : FieldObject} (f : RigHom F K)
  (HF : FieldStable F) (a b : carrier (rig_setoid F)) :
  rig_map f a ≈ rig_map f b → a ≈ b.
Proof.
  intro Hab.
  apply HF.
  exact (field_hom_injective_nn f a b Hab).
Qed.

(*
 Injective ⇒ monic, in the shape Instance/Rng.v's
 [rng_injective_monic] and Instance/Grp.v's [Grp_injectivity_is_monic]
 use: cancellation in the hom-setoid is pointwise, so left
 cancellation of f is injectivity of f evaluated at the two competing
 images. 

 --------
 单射 ⇒ 单的，在 Instance/Rng.v 的 [rng_injective_monic] 和 Instance/Grp.v 的 [Grp_injectivity_is_monic] 形式中 使用：在同态集合等价类中的消去是逐点的，因此 f 的左消去性就是在两个竞争的像上对 f 的评估为单射。
*)
Theorem field_monic {F K : FieldObject} (f : F ~{Field}~> K)
  (HF : FieldStable F) : Monic f.
Proof.
  constructor; intros T g1 g2 Hg a.
  exact (field_hom_injective f HF (rig_map g1 a) (rig_map g2 a) (Hg a)).
Qed.

(* Riehl's blanket statement, with its hypothesis in view. / 考虑其假设的赖尔的笼统说法。 *)
Theorem field_every_monic :
  (∀ F : FieldObject, FieldStable F) →
  ∀ (F K : FieldObject) (f : F ~{Field}~> K), Monic f.
Proof.
  intros Hstab F K f.
  exact (field_monic f (Hstab F)).
Qed.

(** ** ℚ: the witness / ** ℚ: 证人 *)

(*
 [Qeq] is decidable, so ℚ's equality is stable and every homomorphism
 out of ℚ is monic with no hypothesis whatsoever. 

 --------
 [Qeq] 是可判定的，因此 ℚ 的相等性是稳定的，并且从 ℚ 出发的每一个同态都是单射，没有任何假设。
*)
Lemma Q_Field_dec (a b : carrier (rig_setoid Q_Field)) :
  (a ≈ b) + (a ≈ b → False).
Proof.
  destruct (Qeq_dec a b) as [H | H].
  - left; exact H.
  - right; exact H.
Qed.

Definition Q_Field_stable : FieldStable Q_Field :=
  field_dec_stable Q_Field Q_Field_dec.

Theorem Q_hom_monic (K : FieldObject) (f : Q_Field ~{Field}~> K) : Monic f.
Proof. exact (field_monic f Q_Field_stable). Qed.

(*
 The identity is a morphism, and ℚ is an object: the category is
 inhabited.  A second object, F₂, is built below, and the two are
 shown to have no morphism between them in either direction. 

 --------
 恒等映射是一个态射，而 ℚ 是一个对象：该范畴是有对象的。下面构造了第二个对象 F₂，并证明它们之间在任一方向上都没有态射。
*)
Example Q_Field_object : obj[Field] := Q_Field.

Example Q_Field_id : Q_Field ~{Field}~> Q_Field := @id Field Q_Field.

Example Q_Field_id_monic : Monic (@id Field Q_Field) := Q_hom_monic _ _.

(** ** ℚ is rigid *)

(* Denominators are nonzero as rationals — the one arithmetic fact the cancellation below needs. / 分母作为有理数不为零——这是下面约简所需的一个算术事实。 *)
Lemma Q_den_nonzero (q : Q) : ~ (inject_Z (Z.pos (Qden q)) == 0)%Q.
Proof. unfold Qeq, inject_Z; simpl; discriminate. Qed.

Lemma Q_cancel_r (x y b : Q) :
  ~ (b == 0)%Q → (x * b == y * b)%Q → (x == y)%Q.
Proof.
  intros Hb H.
  rewrite <- (Qmult_1_r x), <- (Qmult_1_r y).
  rewrite <- (Qmult_inv_r b Hb).
  rewrite (Qmult_assoc x b (/ b)), (Qmult_assoc y b (/ b)).
  now rewrite H.
Qed.

(*
 Every ring endomorphism of ℚ is the identity.  On the image of ℤ this
 is initiality of ℤ in Rng ([rng_from_Z_unique], applied twice: once
 to the composite with the inclusion and once to the inclusion
 itself); a general rational is then pinned by multiplying through by
 its denominator, which the endomorphism fixes, and cancelling.  No
 fraction is ever chosen — the same discipline as Rng.v's
 [ZtoQ_epic]. 

 --------
 ℚ 的每一个环自同构都是恒等映射。在 ℤ 的像上，这是 ℤ 在 Rng 中的初态性（[rng_from_Z_unique]，应用两次：一次对与包含的复合映射，一次对包含本身）；然后，通过乘以分母（自同构固定分母）并约掉，确定了一般有理数。没有选择任何分数——这与 Rng.v 中的 [ZtoQ_epic] 的方法相同。
*)
Theorem Q_endo_id (f : Q_Field ~{Field}~> Q_Field) (q : Q) :
  (rig_map f q == q)%Q.
Proof.
  (* f respects Qeq, and preserves products — both by conversion / f 尊重 Qeq，并保留积 — 两者都通过转换 *)
  assert (Hresp : ∀ x y : Q, (x == y)%Q → (rig_map f x == rig_map f y)%Q).
  { intros x y H; exact (proper_morphism (rig_map f) x y H). }
  assert (Hmul : ∀ x y : Q,
             (rig_map f (x * y) == rig_map f x * rig_map f y)%Q).
  { intros x y; exact (rig_map_mul f x y). }
  (* f fixes every integer, by initiality of ℤ used on both sides / f 固定每个整数，由 ℤ 在两边使用的初始性 *)
  assert (Hz : ∀ z : Z, (rig_map f (inject_Z z) == inject_Z z)%Q).
  { intro z.
    transitivity (zring Q_Ring z).
    - exact (rng_from_Z_unique Q_Ring (rig_hom_compose f ZtoQ) z).
    - symmetry; exact (rng_from_Z_unique Q_Ring ZtoQ z). }
  (* multiply through by the denominator and cancel / 两边同时乘以分母并约去 *)
  apply (Q_cancel_r _ _ (inject_Z (Z.pos (Qden q))) (Q_den_nonzero q)).
  transitivity (rig_map f (q * inject_Z (Z.pos (Qden q)))%Q).
  - rewrite Hmul.
    now rewrite (Hz (Z.pos (Qden q))).
  - transitivity (inject_Z (Qnum q)).
    + transitivity (rig_map f (inject_Z (Qnum q))).
      * apply Hresp, Q_num_den.
      * apply Hz.
    + symmetry; apply Q_num_den.
Qed.

(* ...hence the identity is the only endomorphism, in the hom-setoid. / ...因此，在同态集合中，恒等映射是唯一的自同态。 *)
Corollary Q_endo_unique (f : Q_Field ~{Field}~> Q_Field) :
  f ≈ @id Field Q_Field.
Proof. intro q; exact (Q_endo_id f q). Qed.

(* * ** F₂: the second object, and a second characteristic / * ** F₂：第二个对象，以及第二个特征 *)

(*
 The two-element field, on [bool] with Leibniz equality (Sets.v's
 [bool_setoid_object]): addition is exclusive or, multiplication is
 conjunction, negation and inversion are both the identity.  Every law
 is a case analysis over at most three booleans.  The point of the
 object is that its characteristic is 2 while ℚ's is 0, which is what
 separates the two below. 

 --------
 这个二元域，在 [bool] 上，具有莱布尼茨等式（Sets.v 的 [bool_setoid_object]）：加法是异或，乘法是合取，否定和取反都是恒等。每条律都是对至多三个布尔值的情况分析。该对象的重点在于其特征是 2，而 ℚ 的特征是 0，这正是区分下面两者的原因。
*)
Program Definition F2_Rig : RigObject := {|
  rig_setoid := bool_setoid_object;
  rig_zero := false;
  rig_add := xorb;
  rig_one := true;
  rig_mul := andb;

  (*
 [bool_setoid_object]'s `≈` IS [eq]: the two implications are the
 identity.  See Lib/Setoid/Propositional.v for why the relation must be
 named rather than ascribed. 

 --------
 [bool_setoid_object] 的 `≈` 是 [eq]：这两个蕴含是相同的。请参见 Lib/Setoid/Propositional.v，了解为什么该关系必须被命名而不是赋值。
*)
  rig_prop := @PropEquiv_of_relation _ (is_setoid bool_setoid_object) (@eq bool)
                (fun _ _ h => h) (fun _ _ h => h)
|}.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|] [|] [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.
Next Obligation. intros [|]; reflexivity. Qed.

Program Definition F2_Ring : RingObject := {|
  ring_rig := F2_Rig;
  ring_neg := fun b => b
|}.
Next Obligation. intros [|]; reflexivity. Qed.

Program Definition F2_Field : FieldObject := {|
  field_ring := F2_Ring;
  finv := fun b => b
|}.
Next Obligation. intros [|] [|]; reflexivity. Qed.
Next Obligation. discriminate. Qed.
Next Obligation.
  (* the only nonzero boolean is [true], and true · true ≈ true / 唯一非零布尔值是 [true]，并且 true · true ≈ true *)
  intros [|] Hx; [ reflexivity | destruct (Hx eq_refl) ].
Qed.

(*
 Leibniz equality on [bool] is decidable, so F₂ is stable and every
 homomorphism out of it is monic with no hypothesis. 

 --------
 [bool] 上的莱布尼茨等式是可判定的，因此 F₂ 是稳定的，并且从它出发的每个同态在没有假设的情况下都是单射的。
*)
Lemma F2_Field_dec (a b : carrier (rig_setoid F2_Field)) :
  (a ≈ b) + (a ≈ b → False).
Proof.
  destruct a, b;
    solve [ left; reflexivity | right; discriminate ].
Qed.

Definition F2_Field_stable : FieldStable F2_Field :=
  field_dec_stable F2_Field F2_Field_dec.

Theorem F2_hom_monic (K : FieldObject) (f : F2_Field ~{Field}~> K) :
  Monic f.
Proof. exact (field_monic f F2_Field_stable). Qed.

(* * ** The two fields are not connected, in either direction / * ** 这两个字段在任一方向上都不相连 *)

(*
 1 + 1 in an arbitrary field.  Named because both non-existence
 theorems below run through it: it is zero in F₂ and nonzero in ℚ,
 and a homomorphism must carry it to the corresponding element. 

 --------
 在任意域中的 1 + 1。之所以如此命名，是因为下面的两个不存在定理都适用于它：它在 F₂ 中为零，而在 ℚ 中为非零，并且同态必须将其映射到对应的元素。
*)
Definition ftwo (F : FieldObject) : carrier (rig_setoid F) :=
  rig_add F (rig_one F) (rig_one F).

Lemma ftwo_map {F K : FieldObject} (f : RigHom F K) :
  rig_map f (ftwo F) ≈ ftwo K.
Proof.
  unfold ftwo.
  rewrite (rig_map_add f).
  now rewrite (rig_map_one f).
Qed.

(* In ℚ, 2 ≉ 0 — the whole content of “characteristic zero” that is needed here. / 在ℚ中，2 ≉ 0 —— 这就是此处所需的“零特征”的全部内容。 *)
Lemma Q_ftwo_nonzero : ftwo Q_Field ≈ rig_zero Q_Field → False.
Proof.
  intro H.
  assert (Hq : (2 # 1 == 0)%Q) by exact H.
  unfold Qeq in Hq; simpl in Hq; discriminate Hq.
Qed.

(*
 In F₂, 2 ≈ 0 — and definitionally so, since [xorb true true] computes
 to [false]. 

 --------
 在 F₂ 中，2 ≈ 0——从定义上来说是这样的，因为 [xorb true true] 计算结果为 [false]。
*)
Lemma F2_ftwo_zero : ftwo F2_Field ≈ rig_zero F2_Field.
Proof. reflexivity. Qed.

(* No homomorphism ℚ → F₂: it would have to carry the invertible 2 to the zero of F₂, which [field_hom_nonzero] refutes. / 没有从 ℚ 到 F₂ 的同态：它必须把可逆的 2 映射到 F₂ 的零元，这一点被 [field_hom_nonzero] 驳斥。 *)
Theorem no_hom_Q_F2 (f : Q_Field ~{Field}~> F2_Field) : False.
Proof.
  apply (field_hom_nonzero f (ftwo Q_Field) Q_ftwo_nonzero).
  rewrite (ftwo_map f).
  exact F2_ftwo_zero.
Qed.

(* ...and none the other way: g would have to carry the zero of F₂, which is 1 + 1 there, to 1 + 1 = 2 in ℚ, forcing 2 ≈ 0. / ...而没有反过来的情况：g 必须将 F₂ 中的零，也就是 1 + 1，映射到 ℚ 中的 1 + 1 = 2，从而导致 2 ≈ 0。 *)
Theorem no_hom_F2_Q (g : F2_Field ~{Field}~> Q_Field) : False.
Proof.
  apply Q_ftwo_nonzero.
  rewrite <- (ftwo_map g).
  (* [ftwo F2_Field] IS [rig_zero F2_Field], by computation / [ftwo F2_Field] 通过计算是 [rig_zero F2_Field] *)
  apply (rig_map_zero g).
Qed.

(*
   * ** riehl:1.6:example15: fields have neither an initial nor a
   terminal object 

   --------
   * ** riehl:1.6:example15: 域既没有初始对象也没有终结对象
*)

(*
 Both proofs are constructive and case-split-free.  They are the
 standard characteristic argument, and the only subtlety is that the
 guard on [finv_l] is a NEGATION, so the negative fact “2 is not zero
 here” is exactly what licenses inverting it — no decision procedure
 is consulted, and neither [FieldStable] nor decidability is used.

 An initial field I would map to both ℚ and F₂.  The ℚ-map shows
 1 + 1 is nonzero in I, since a zero there would be carried to a zero
 in ℚ; the F₂-map then carries that nonzero element to
 1 + 1 = 0 in F₂, which [field_hom_nonzero] refutes. 

 --------
 这两个证明都是构造性的，并且没有分情况讨论。它们是标准的特征论证，唯一的微妙之处在于 [finv_l] 上的守卫是一个否定，因此负事实“这里的 2 不为零”正是允许将其取反的理由——没有使用任何判定过程，也没有使用 [FieldStable] 或可判定性。

 我最初会将一个域 I 映射到 ℚ 和 F₂。ℚ 映射显示在 I 中 1 + 1 非零，因为 I 中的零会被映射为 ℚ 中的零；然后 F₂ 映射将该非零元素映射为 F₂ 中的 1 + 1 = 0，而 [field_hom_nonzero] 否定了这一点。
*)
Theorem Field_no_initial (I : @Initial Field) : False.
Proof.
  pose (f := @zero Field I Q_Field).
  pose (g := @zero Field I F2_Field).
  (* 1 + 1 is nonzero in the initial field, because its ℚ-image is 2 / 1 + 1 在初始域中非零，因为它的 ℚ 映像是 2 *)
  assert (Hnz : ftwo (@initial_obj Field I)
                  ≈ rig_zero (@initial_obj Field I) → False).
  { intro H.
    apply Q_ftwo_nonzero.
    transitivity (rig_map f (ftwo (@initial_obj Field I))).
    - symmetry; apply (ftwo_map f).
    - transitivity (rig_map f (rig_zero (@initial_obj Field I))).
      + apply (proper_morphism (rig_map f)); exact H.
      + apply (rig_map_zero f). }
  (* yet its F₂-image is zero / 然而它的 F₂-像为零 *)
  apply (field_hom_nonzero g _ Hnz).
  rewrite (ftwo_map g).
  exact F2_ftwo_zero.
Qed.

(* Dually, a terminal field T receives both. The F₂-map forces 1 + 1 ≈ 0 in T, because 1 + 1 already is 0 in F₂; the ℚ-map then carries the nonzero 2 of ℚ onto that same zero. / 同样，终端域 T 接收两者。F₂ 映射迫使 1 + 1 ≈ 0 在 T 中，因为在 F₂ 中 1 + 1 已经是 0；然后 ℚ 映射将 ℚ 中非零的 2 映射到同样的 0 上。 *)
Theorem Field_no_terminal (T : @Terminal Field) : False.
Proof.
  pose (f := @one Field T Q_Field).
  pose (g := @one Field T F2_Field).
  (* 1 + 1 vanishes in the terminal field, being the g-image of 0 / 1 + 1 在终端域中消失，是 0 的 g-像 *)
  assert (H0 : ftwo (@terminal_obj Field T)
                 ≈ rig_zero (@terminal_obj Field T)).
  { transitivity (rig_map g (ftwo F2_Field)).
    - symmetry; apply (ftwo_map g).
    - apply (rig_map_zero g). }
  (* yet it is the f-image of the invertible 2 of ℚ / 然而它是可逆 2 在 ℚ 中的 f-像 *)
  apply (field_hom_nonzero f (ftwo Q_Field) Q_ftwo_nonzero).
  rewrite (ftwo_map f).
  exact H0.
Qed.

(*
 The object-level readings, which are what “the category has no
 initial object” says without choosing one: NO object of [Field] is
 initial, and none is terminal. 

 --------
 对象层面的读法，也就是“该类别没有初始对象”所表达的意思而不进行选择：[Field] 没有初始对象，也没有终端对象。
*)
Corollary Field_no_initial_obj (c : Field) (H : IsInitialObj c) : False.
Proof. exact (Field_no_initial (Initial_from_IsInitialObj H)). Qed.

Corollary Field_no_terminal_obj (c : Field) (H : IsTerminalObj c) : False.
Proof. exact (Field_no_terminal (Terminal_from_IsTerminalObj H)). Qed.

(** ** Acceptance tests / ** 验收测试 *)

(* The forgetful functors return the underlying data on the nose. / 遗忘函子直接返回底层数据。 *)
Example field_forget_carrier (F : FieldObject) :
  Field_Forget F = rig_setoid F := eq_refl.

Example field_rng_object (F : FieldObject) :
  Field_Rng F = field_ring F := eq_refl.

(* ℚ's inverse computes, and its unit is separated from its zero. / ℚ 的逆运算被计算，其单位被从零中分离出来。 *)
Example q_inv_three : finv Q_Field (3 # 1) = (1 # 3)%Q := eq_refl.

Example q_one_neq_zero : (1 # 1) == 0 → False := field_one_neq_zero Q_Field.
