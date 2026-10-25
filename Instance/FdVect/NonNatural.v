(* * * V ≅ V* is not natural: the variance obstruction made concrete / * * V ≅ V* 不是自然的：方差阻碍具体化 *)

Require Import Coq.QArith.QArith.
Require Import Coq.micromega.Lqa.
Require Import Coq.Vectors.Fin.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.
Require Import Category.Instance.FdVect.
Require Import Category.Instance.FdVect.DoubleDual.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Mac Lane, "Categories for the Working Mathematician",
 2nd ed., §I.4, printed p. 17 (PDF 27) — the remark that
 the finite-dimensional V ≅ V* requires a choice of basis
 and is not natural, in contrast to V ≅ V**.
 Also:      Awodey, "Category Theory" (CMU pre-print, Sept 2005),
 §7.5, Example 7.12 — the same contrast, as the motivating
 example for naturality; Riehl, "Category Theory in
 Context", §1.4, Example 1.4.4(ii) — riehl:1.4:example4,
 the negative clause.
 nLab:      https://ncatlab.org/nlab/show/natural+isomorphism

 THE VARIANCE OBSTRUCTION, and what "natural" can even mean here.
 The single-dual functor [DualFd] is CONTRAVARIANT — its domain is
 (FdVect F)^op — while the identity functor is covariant, so a
 natural transformation Id ⟹ DualFd is not even a well-typed
 assertion: that is Riehl's "the variance clashes", and it is
 already the clean negative statement her example records.  The
 question becomes well posed as in the character-group precedent
 (Instance/Ab/Character/NonNatural.v, Mac Lane's own §I.4 worked
 pair): restrict to isomorphisms and read the dual covariantly
 through inversion, D' f := DualFd (f⁻¹).  Naturality of a family
 σ_V : V ≅ V* over the iso-core then demands, at each automorphism
 α, the square σ ∘ α ≈ DualFd (α⁻¹) ∘ σ.  (The precedent's
 D'-functor machinery is deliberately not rebuilt here: the square
 is stated directly, a weaker hypothesis and so a stronger
 refutation.)

 THE REFUTATION.  One automorphism of one object, at one point,
 suffices: the scaling v ↦ 2·v of the one-dimensional space
 ℚ¹ = StdVect ℚ 1, whose inverse is v ↦ ½·v.  Since [DualFd] acts
 by precomposition, the square evaluated at a vector v and then at
 a vector w reads

 σ(2·v)(w)  ≈  σ(v)(½·w),

 and the SINGLE instance v = w = e₁ (the basis vector) is all the
 proof consumes: writing q := σ(e₁)(e₁) ∈ ℚ, homogeneity of σ and
 of the functional σ(e₁) turns the two sides into 2q and ½q.  So
 2q ≈ ½q in ℚ, hence q ≈ 0; by homogeneity σ(e₁) is then the zero
 functional, i.e. σ(e₁) ≈ σ(0), and applying σ⁻¹ collapses
 e₁ ≈ 0 in ℚ¹ — refuted by evaluating the coordinate: 1 ≉ 0 in ℚ.
 This is Mac Lane's m² ≢ 1 obstruction with m = 2 acting on ℚ
 instead of ℤ/5: over ℚ the scalars 2 and ½ differ and their gap
 is invertible, so the smallest space already separates.

 STRENGTH.  [sigma_not_natural] takes ONE isomorphism
 σ : ℚ¹ ≅ (ℚ¹)* and ONE equation — the pointwise square at the
 single point (e₁, e₁) of the single automorphism 2·(−) —
 refuting the weakest hypothesis is the strongest theorem;
 [sigma_square_pointwise] bridges from the categorical square
 through [DualFd], so the categorical reading is refuted too
 ([sigma_categorical_not_natural]), and
 [sigma_family_not_natural] instantiates the family form.  Unlike
 the character precedent, whose family premise is itself
 uninhabited over all of Ab (its [no_such_sigma_family]), here the
 family premise IS inhabited: [family_premise_inhabited] repackages
 DoubleDual.v's [fd_dual_pointwise_iso] at the [FdVect] hom-level
 (the homs of [FdVect F] ARE the [RModHom]s of the underlying
 modules, so the four fields transfer verbatim), and
 [family_not_natural_applies] feeds it to the corollary, so the
 non-vacuity is machine-checked rather than asserted.  This is
 exactly Awodey's point: the pointwise isomorphisms exist at every
 finite-dimensional object, and what is refuted is only, and
 precisely, their naturality.  The POSITIVE half of the contrast —
 V ≅ V** natural, at any dimension — is DoubleDual.v's
 [double_dual_natural] and [double_dual_iso]; Riehl clause (vii)'s
 no-cloning computation is Instance/FdVect/Tensor.v. 

 --------
 书籍：Mac Lane，《为工作的数学家而设的范畴论》，第2版，第I.4节，第17页印刷版（PDF第27页）——关于有限维V ≅ V* 需要选择基并且不是自然的，与V ≅ V**形成对比的注释。
 另外：Awodey，《范畴论》（CMU预印本，2005年9月），第7.5节，例7.12——作为自然性的动机例子同样的对比；Riehl，《语境中的范畴论》，第1.4节，例1.4.4(ii)——riehl:1.4:example4，否定子句。
 nLab: https://ncatlab.org/nlab/show/natural+isomorphism方差阻碍，以及“自然”在这里甚至可能意味着什么。单-双函子 [DualFd] 是一个逆变函子——它的定义域是 (FdVect F)^op——而恒等函子是顺变的，因此一个自然变换 Id ⟹ DualFd 甚至不是一个类型正确的断言：这就是 Riehl 所说的“方差冲突”，也是她的例子已经记录的清晰负面陈述。问题在类似于字符群先例（Instance/Ab/Character/NonNatural.v，Mac Lane 自己的 §I.4 工作对）中才变得有意义：限制到同构，并通过取逆将对偶函子作为顺变函子来读取，D' f := DualFd (f⁻¹)。在同构核心上，一个族 σ_V : V ≅ V* 的自然性要求在每个自同构 α 处，图表 σ ∘ α ≈ DualFd (α⁻¹) ∘ σ 成立。(这里故意不重建前例的 D'-函子机制：直接给出方框，假设更弱，因此反驳更强。)

 反驳。一个对象在一个点的一个自同构就足够：一维空间 ℚ¹ = StdVect ℚ 1 的缩放 v ↦ 2·v，其逆为 v ↦ ½·v。由于 [DualFd] 通过预合成作用，方框在向量 v 处求值，然后在向量 w 处求值为

 σ(2·v)(w)  ≈  σ(v)(½·w),并且唯一的实例 v = w = e₁（基向量）就是整个证明所使用的：定义 q := σ(e₁)(e₁) ∈ ℚ，σ 的齐次性以及函数 σ(e₁) 的齐次性将等式两边变为 2q 和 ½q。因此 2q ≈ ½q 在 ℚ 中，因此 q ≈ 0；根据齐次性，σ(e₁) 于是是零函数，即 σ(e₁) ≈ σ(0)，应用 σ⁻¹ 将 e₁ 在 ℚ¹ 中折叠为 0 —— 通过评估坐标被驳斥：1 ≉ 0 在 ℚ 中。这是 Mac Lane 的 m² ≢ 1 障碍，m = 2 作用于 ℚ 而不是 ℤ/5：在 ℚ 上，标量 2 和 ½ 不同，并且它们的差距可逆，因此最小的空间已经能区分。力量。[sigma_not_natural] 使用一个同构 σ : ℚ¹ ≅ (ℚ¹)* 和一个方程——在单个自同构 2·(−) 的单点 (e₁, e₁) 处的逐点平方——驳斥最弱假设就是最强定理；[sigma_square_pointwise] 通过 [DualFd] 从范畴平方建立桥梁，因此范畴解读也被驳斥（[sigma_categorical_not_natural]），并且 [sigma_family_not_natural] 实例化了族形式。与字符先例不同，其族前提本身在整个 Ab 上都是无人居住的（它的 [no_such_sigma_family]），这里的族前提是有人居住的：[family_premise_inhabited] 在 hom 级别（[FdVect]）重新打包 DoubleDual.v 的 [fd_dual_pointwise_iso]（[FdVect F] 的 hom 是底层模块的 [RModHom]，所以四个字段逐字转移），并且 [family_not_natural_applies] 将其提供给推论，因此非空性是经过机械检查的，而不是被假定的。这正是 Awodey 的观点：逐点同构在每个有限维对象上都存在，而被反驳的只是、正是它们的自然性。对比的正面一半 — V ≅ V** 自然地，在任意维度下 — 是 DoubleDual.v 的 [double_dual_natural] 和 [double_dual_iso]；Riehl 条款 (vii) 的不可克隆计算是 Instance/FdVect/Tensor.v。
*)

(* * ** The one-dimensional stage over ℚ / * ** 在 ℚ 上的一维阶段 *)

Definition Q1 : FdVectObject Q_Field := StdVect Q_Field 1.

(* The basis vector of ℚ¹. / ℚ¹ 的基向量。 *)
Definition e1 : carrier (cmon_setoid (fdv_mod Q1)) :=
  std_basis Q_Field 1 Fin.F1.

(*
 Scaling by a fixed rational, as a morphism of FdVect ℚ, written
 through the abstract rig interface so every obligation is a rig
 law (the house idiom of Instance/FdVect.v's std layer). 

 --------
 通过固定有理数进行缩放，作为 FdVect ℚ 的一个态射，通过抽象环结构接口书写，因此每个义务都是环律（Instance/FdVect.v 的标准层的常用模式）。
*)
Definition qscale (c : Q) : Q1 ~{FdVect Q_Field}~> Q1.
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring Q_Field) (fdv_mod Q1) (fdv_mod Q1)
       (@Build_CMonHom (std_cmon Q_Field 1) (std_cmon Q_Field 1)
          (@Build_SetoidMorphism _ _ _ _
             (fun v i => rig_mul Q_Field c (v i)) _) _ _)
       _).
  - intros v w Hvw i.
    apply rig_mul_respects; [ reflexivity | exact (Hvw i) ].
  - intro i; apply rig_mul_zero_r.
  - intros v w i; apply rig_distr_l.
  - intros r v i.
    etransitivity;
      [ symmetry; apply rig_mul_assoc | ].
    etransitivity;
      [ apply rig_mul_respects;
        [ apply (field_comm Q_Field c r) | reflexivity ] | ].
    apply rig_mul_assoc.
Defined.

(* 2 · ½ ≈ 1 and ½ · 2 ≈ 1 in ℚ, by computation. / 2 · ½ ≈ 1 和 ½ · 2 ≈ 1 在有理数 ℚ 中，通过计算得到。 *)
Lemma two_half_one : (2 * / 2 == 1)%Q.
Proof. reflexivity. Qed.

Lemma half_two_one : (/ 2 * 2 == 1)%Q.
Proof. reflexivity. Qed.

(* v ↦ 2·v is an automorphism of ℚ¹, with inverse v ↦ ½·v. / v ↦ 2·v 是 ℚ¹ 的一个自同构，其逆映射为 v ↦ ½·v。 *)
Program Definition alpha2 : @Isomorphism (FdVect Q_Field) Q1 Q1 := {|
  to   := qscale 2;
  from := qscale (/ 2)
|}.
Next Obligation.
  intros v i.
  etransitivity; [ symmetry; apply rig_mul_assoc | ].
  etransitivity;
    [ apply rig_mul_respects; [ apply two_half_one | reflexivity ] | ].
  apply rig_mul_one_l.
Qed.
Next Obligation.
  intros v i.
  etransitivity; [ symmetry; apply rig_mul_assoc | ].
  etransitivity;
    [ apply rig_mul_respects; [ apply half_two_one | reflexivity ] | ].
  apply rig_mul_one_l.
Qed.

(* 1 ≉ 0 in ℚ — the coordinate that survives the collapse. / 1 ≉ 0 在 ℚ 中——在坍塌中幸存下来的坐标。 *)
Lemma q_one_neq_zero : (1 == 0)%Q → False.
Proof.
  intro H; discriminate H.
Qed.

(* The arithmetic heart: 2q ≈ ½q in ℚ forces q ≈ 0. / 算术核心：在有理数ℚ中，2q ≈ ½q 会导致 q ≈ 0。 *)
Lemma q_two_half_zero (q : Q) :
  (2 * q == / 2 * q)%Q → (q == 0)%Q.
Proof.
  change (/ 2)%Q with (1 # 2)%Q.
  intro H; lra.
Qed.

(* [qscale c] applied to a vector IS the module action of c — both are the pointwise product. / [qscale c] 应用于向量 IS 是 c 的模作用——两者都是逐点乘积。 *)
Lemma qscale_smul (c : Q) (v : carrier (cmon_setoid (fdv_mod Q1))) :
  cmon_map (rm_hom (qscale c)) v ≈ rm_smul (fdv_mod Q1) c v.
Proof.
  intro i; reflexivity.
Qed.

(* Every vector of ℚ¹ is its first coordinate times e₁. / ℚ¹ 的每个向量都是它的第一个坐标乘以 e₁。 *)
Lemma q1_expand (w : carrier (cmon_setoid (fdv_mod Q1))) :
  w ≈ rm_smul (fdv_mod Q1) (w Fin.F1) e1.
Proof.
  intro i.
  pattern i; apply (Fin.caseS' i); [ | intro j; inversion j ].
  symmetry.
  etransitivity;
    [ apply rig_mul_respects; [ reflexivity | apply delta_refl ] | ].
  apply rig_mul_one_r.
Qed.

(** ** The violation / ** 违规 *)

Section Violation.

Context (s0 : @Isomorphism (FdVect Q_Field) Q1 (DualFdObj Q_Field Q1)).

(*
 The naturality square at [alpha2], read covariantly through
 inversion and evaluated at the single point (e₁, e₁): σ(2·e₁), as
 a functional, agrees at e₁ with σ(e₁) at ½·e₁.  This single
 equation is the entire hypothesis; [sigma_square_pointwise] below
 derives its ∀-form from the categorical square
 σ ∘ α ≈ DualFd(α⁻¹) ∘ σ, so refuting the single instance refutes
 the categorical reading a fortiori. 

 --------
 在 [alpha2] 的自然性方格，通过协变地读取反演，并在单点 (e₁, e₁) 处求值：σ(2·e₁)，作为一个函数，在 e₁ 处与 σ(e₁) 在 ½·e₁ 处一致。这个单一方程就是整个假设；下面的 [sigma_square_pointwise] 从范畴方格 σ ∘ α ≈ DualFd(α⁻¹) ∘ σ 推导其 ∀-形式，因此反驳这个单一实例也就必然地反驳了范畴解读。
*)
Context (Hnat :
  cmon_map (rm_hom (cmon_map (rm_hom (to s0))
                      (cmon_map (rm_hom (qscale 2)) e1))) e1
    ≈ cmon_map (rm_hom (cmon_map (rm_hom (to s0)) e1))
        (cmon_map (rm_hom (qscale (/ 2))) e1)).

Let s : Q1 ~{FdVect Q_Field}~> DualFdObj Q_Field Q1 := to s0.

Let q : Q := cmon_map (rm_hom (cmon_map (rm_hom s) e1)) e1.

(* Left side of the square at (e₁, e₁): homogeneity of σ pushes the scalar out through the dual module's pointwise action — 2q. / 在 (e₁, e₁) 的方形左侧：σ 的齐次性通过对偶模的逐点作用将标量推出——2q。 *)
Lemma sigma_two :
  cmon_map (rm_hom (cmon_map (rm_hom s)
                      (cmon_map (rm_hom (qscale 2)) e1))) e1
    ≈ (2 * q)%Q.
Proof using Type.
  transitivity
    (cmon_map (rm_hom (cmon_map (rm_hom s)
                         (rm_smul (fdv_mod Q1) 2 e1))) e1).
  - exact (proper_morphism (cmon_map (rm_hom s)) _ _
             (qscale_smul 2 e1) e1).
  - exact (rm_map_smul s 2 e1 e1).
Qed.

(*
 Right side of the square at (e₁, e₁): homogeneity of the
 functional σ(e₁) — an [RModHom] into the ring-as-module, whose
 action is multiplication — gives ½q. 

 --------
 在 (e₁, e₁) 的方形右侧：泛函 σ(e₁) 的齐次性——一个 [RModHom] 到作为模的环的映射，其作用是乘法——给出 ½q。
*)
Lemma sigma_half :
  cmon_map (rm_hom (cmon_map (rm_hom s) e1))
    (cmon_map (rm_hom (qscale (/ 2))) e1)
    ≈ (/ 2 * q)%Q.
Proof using Type.
  transitivity
    (cmon_map (rm_hom (cmon_map (rm_hom s) e1))
       (rm_smul (fdv_mod Q1) (/ 2) e1)).
  - apply (proper_morphism (cmon_map (rm_hom (cmon_map (rm_hom s) e1)))).
    apply qscale_smul.
  - exact (rm_map_smul (cmon_map (rm_hom s) e1) (/ 2)%Q e1).
Qed.

(* The single square instance plus the two computations: 2q ≈ ½q. / 单个平方实例加上两个计算：2q ≈ ½q。 *)
Lemma q_zero : (q == 0)%Q.
Proof using Hnat.
  apply q_two_half_zero.
  transitivity
    (cmon_map (rm_hom (cmon_map (rm_hom s)
                         (cmon_map (rm_hom (qscale 2)) e1))) e1).
  - symmetry; exact sigma_two.
  - transitivity
      (cmon_map (rm_hom (cmon_map (rm_hom s) e1))
         (cmon_map (rm_hom (qscale (/ 2))) e1)).
    + exact Hnat.
    + exact sigma_half.
Qed.

(* Hence σ(e₁) is the zero functional. / 因此 σ(e₁) 是零泛函。 *)
Lemma sigma_e1_zero (w : carrier (cmon_setoid (fdv_mod Q1))) :
  cmon_map (rm_hom (cmon_map (rm_hom s) e1)) w ≈ 0%Q.
Proof using Hnat.
  transitivity
    (cmon_map (rm_hom (cmon_map (rm_hom s) e1))
       (rm_smul (fdv_mod Q1) (w Fin.F1) e1)).
  - apply (proper_morphism (cmon_map (rm_hom (cmon_map (rm_hom s) e1)))).
    apply q1_expand.
  - transitivity ((w Fin.F1) * q)%Q.
    + exact (rm_map_smul (cmon_map (rm_hom s) e1) (w Fin.F1) e1).
    + etransitivity;
        [ apply rig_mul_respects; [ reflexivity | exact q_zero ] | ].
      apply rig_mul_zero_r.
Qed.

(*
 σ identifies e₁ and 0, so — σ being an isomorphism — e₁ ≈ 0 in
 ℚ¹, and coordinate 1 of that collapse reads 1 ≈ 0 in ℚ. 

 --------
 σ 标识 e₁ 和 0，因此——σ 是同构——在 ℚ¹ 中 e₁ ≈ 0，并且该坍塌的坐标 1 在 ℚ 中读作 1 ≈ 0。
*)
Theorem sigma_square_violation : False.
Proof using s0 Hnat.
  apply q_one_neq_zero.
  assert (He : e1 ≈ cmon_zero (std_cmon Q_Field 1)).
  { transitivity
      (cmon_map (rm_hom (from s0)) (cmon_map (rm_hom (to s0)) e1)).
    - intro i; symmetry; exact (iso_from_to s0 e1 i).
    - transitivity
        (cmon_map (rm_hom (from s0))
           (cmon_zero (DualMod Q_Field (fdv_mod Q1)))).
      + apply (proper_morphism (cmon_map (rm_hom (from s0)))).
        intro w.
        etransitivity; [ exact (sigma_e1_zero w) | ].
        reflexivity.
      + exact (cmon_map_zero (rm_hom (from s0))). }
  exact (He Fin.F1).
Qed.

End Violation.

(*
 The packaged negative half, in its STRONG form: no isomorphism
 ℚ¹ ≅ (ℚ¹)* satisfies even the single point (e₁, e₁) of the
 pointwise naturality square at the automorphism 2·(−). 

 --------
 封装的负半部分，在其强形式下：没有同构 ℚ¹ ≅ (ℚ¹)*，甚至满足自同构 2·(−) 下逐点自然性方的单个点 (e₁, e₁)。
*)
Theorem sigma_not_natural
        (s0 : @Isomorphism (FdVect Q_Field) Q1 (DualFdObj Q_Field Q1)) :
  cmon_map (rm_hom (cmon_map (rm_hom (to s0))
                      (cmon_map (rm_hom (qscale 2)) e1))) e1
    ≈ cmon_map (rm_hom (cmon_map (rm_hom (to s0)) e1))
        (cmon_map (rm_hom (qscale (/ 2))) e1) →
  False.
Proof.
  intro Hnat.
  exact (sigma_square_violation s0 Hnat).
Qed.

(* The categorical square implies the pointwise ∀-form: [DualFd] acts by precomposition, so σ ∘ α ≈ DualFd(α⁻¹) ∘ σ, unfolded at v and then at w, is literally the pointwise square. / 范畴平方意味着逐点 ∀-形式：[DualFd] 通过预组合作用，因此 σ ∘ α ≈ DualFd(α⁻¹) ∘ σ，在 v 处展开，然后在 w 处展开，字面上就是逐点平方。 *)
Lemma sigma_square_pointwise
      (s0 : @Isomorphism (FdVect Q_Field) Q1 (DualFdObj Q_Field Q1)) :
  (to s0 ∘ to alpha2 ≈ fmap[DualFd Q_Field] (from alpha2) ∘ to s0) →
  ∀ v w,
    cmon_map (rm_hom (cmon_map (rm_hom (to s0))
                        (cmon_map (rm_hom (qscale 2)) v))) w
      ≈ cmon_map (rm_hom (cmon_map (rm_hom (to s0)) v))
          (cmon_map (rm_hom (qscale (/ 2))) w).
Proof.
  intros H v w.
  exact (H v w).
Qed.

(* Hence the categorical reading is refuted too. / 因此，绝对解释也被驳斥了。 *)
Corollary sigma_categorical_not_natural
          (s0 : @Isomorphism (FdVect Q_Field) Q1 (DualFdObj Q_Field Q1)) :
  (to s0 ∘ to alpha2 ≈ fmap[DualFd Q_Field] (from alpha2) ∘ to s0) →
  False.
Proof.
  intro H.
  exact (sigma_not_natural s0 (sigma_square_pointwise s0 H e1 e1)).
Qed.

(*
 The family form: any family σ_V : V ≅ V* over all of FdVect ℚ
 instantiates at ℚ¹.  Unlike the character precedent, this family
 premise is INHABITED (next), so the corollary has applicable
 content: what does not exist is a NATURAL such family. 

 --------
 家族形式：在整个 FdVect ℚ 上，任意家族 σ_V : V ≅ V* 在 ℚ¹ 处实例化。与之前的特征不同，这个家族前提是有实例的（接下来），所以推论有适用的内容：不存在的是自然的这样的家族。
*)
Corollary sigma_family_not_natural
          (σ : ∀ V : FdVectObject Q_Field,
                 @Isomorphism (FdVect Q_Field) V (DualFdObj Q_Field V)) :
  cmon_map (rm_hom (cmon_map (rm_hom (to (σ Q1)))
                      (cmon_map (rm_hom (qscale 2)) e1))) e1
    ≈ cmon_map (rm_hom (cmon_map (rm_hom (to (σ Q1))) e1))
        (cmon_map (rm_hom (qscale (/ 2))) e1) →
  False.
Proof.
  intro Hnat.
  exact (sigma_not_natural (σ Q1) Hnat).
Qed.

(*
 The family premise is inhabited — DoubleDual.v's basis-dependent
 pointwise isomorphism, repackaged at the [FdVect] hom-level.  The
 homs of [FdVect F] ARE the [RModHom]s of the underlying modules,
 so the four fields of [fd_dual_pointwise_iso] transfer verbatim;
 only the record's category index changes. 

 --------
 家庭前提是有人居住的——DoubleDual.v 的依赖于基的逐点同构，在 [FdVect] 同层级被重新打包。[FdVect F] 的 hom 实际上是底层模块的 [RModHom]，所以 [fd_dual_pointwise_iso] 的四个字段完全照搬；只有记录的类别索引发生变化。
*)
Definition family_premise_inhabited (V : FdVectObject Q_Field) :
  @Isomorphism (FdVect Q_Field) V (DualFdObj Q_Field V).
Proof.
  unshelve refine {| to := _; from := _ |}.
  - exact (to (fd_dual_pointwise_iso Q_Field V)).
  - exact (from (fd_dual_pointwise_iso Q_Field V)).
  - exact (iso_to_from (fd_dual_pointwise_iso Q_Field V)).
  - exact (iso_from_to (fd_dual_pointwise_iso Q_Field V)).
Defined.

(*
 And it slots into the corollary — the non-vacuity of the negative
 half is machine-checked, not asserted: pointwise isomorphisms
 V ≅ V* exist at every object, and no family of them survives even
 one point of one naturality square. 

 --------
 它也适用于推论——负半部分的非空性是由机器检查的，而不是声明的：每个对象上都存在点对点的同构 V ≅ V*，而且没有任何一组同构能够跨越哪怕一个自然性方格的一个点。
*)
Definition family_not_natural_applies :=
  sigma_family_not_natural family_premise_inhabited.
