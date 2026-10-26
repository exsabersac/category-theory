(* * * The ring of continuous functions, contravariantly / * * 连续函数的环，逆变 *)

Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Interval.
Require Import Category.Instance.Top.Presheaf.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Interval.v's [Rcases]/[Rlin] split absolute values in the GOAL only;
 the estimates below also carry them in hypotheses.  Like those two,
 these are top-level [Ltac]s, so they are visible to any module that
 requires this one. 

 --------
 Interval.v 的 [Rcases] / [Rlin] 仅在 GOAL 中分割绝对值；下面的估计也将它们包含在假设中。像那两个一样，这些是顶层的 [Ltac]，因此它们对任何需要此模块的模块都是可见的。
*)
Ltac RcasesH :=
  unfold Rabs, Rmin, Rmax in *;
  repeat
    match goal with
    | [ |- context[Rcase_abs ?x] ]         => destruct (Rcase_abs x)
    | [ H : context[Rcase_abs ?x] |- _ ]   => destruct (Rcase_abs x)
    | [ |- context[Rle_dec ?x ?y] ]        => destruct (Rle_dec x y)
    | [ H : context[Rle_dec ?x ?y] |- _ ]  => destruct (Rle_dec x y)
    end.
Ltac RlinH := RcasesH; lra.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §II.3 Exercise 5, printed p. 40 (PDF p. 50) — maclane:II.3:ex5
 Book:      Awodey, “Category Theory” (1st ed., 2005 pre-print), §7.2,
 printed p. 156 (PDF p. 165) —
 awodey:7.2:construction-continuous-real-functions-ring
 nLab:      https://ncatlab.org/nlab/show/Top
 Wikipedia: https://en.wikipedia.org/wiki/Ring_(mathematics)

 Mac Lane's exercise: assigning to each space X the ring C(X) of
 continuous real-valued functions under the pointwise operations, and
 to each continuous map the precomposition homomorphism, is a
 contravariant functor from spaces to rings — the basic object of
 function-algebra dualities.

 - [cr_plus]/[cr_mult]/[cr_neg]/[cr_const]: the pointwise algebra
 of continuous maps X ⟶ R_Top, each with its continuity proof
 - [CRingOb X : RingObject]: C(X), the hom-carrier
 [ContinuousMorphism X R_Top] under the pointwise structure
 - [CRing_precomp]: precomposition along a continuous map is a
 ring homomorphism
 - [ContinuousRingFunctor : Top^op ⟶ Rng]: the contravariant
 functor, in the library's standard encoding

 Design:

 1. CONTINUITY OF THE POINTWISE OPERATIONS IS A UNION OF FINITE
 INTERSECTIONS.  X's topology is abstract — there is no
 epsilon-delta ON X — so the preimage of a metric open under
 f + g is exhibited as an X-open the only way it can be: as the
 union, indexed by the points x it contains, of intersections
 (f ⁻¹ of a small ball around f x) ∩ (g ⁻¹ of a small ball around
 g x), each factor open by f's and g's own continuity, the union
 and intersections by X's axioms, and the pointwise equivalence
 with the actual preimage by the triangle inequality ([Rlin]).
 For the product the radius shrinks by the local bound
 M = |f x| + |g x| + 1 (and is capped at 1 so |f y| ≤ |f x| + 1),
 the standard argument, with [nra] closing the nonlinear
 estimate.  The radius of every ball is DATA, in
 Instance/Top/Interval.v's discipline, so no choice principle
 appears.

 2. C(X) IS THE HOM-CARRIER, BUT THE RING STRUCTURE IS NOT
 TRANSFERRED FROM A RING OBJECT ℝ — THAT PREMISE IS NOT YET
 STATABLE HERE.  Awodey's §7.2 reads C(X) as Hom_Top(X, ℝ) with
 the operations inherited from ℝ as a ring object INTERNAL to
 Top, functoriality then falling out of representability rather
 than being checked by hand.  This tree cannot state that
 premise: an internal ring object needs continuous operations
 ℝ × ℝ ⟶ ℝ, and Top has no categorical products yet
 (Instance/Top.v names the product topology as future work);
 the library's [RingObject] is Sets-level element-wise
 structure, which is what [CRingOb] below inhabits.  So the
 carrier is literally the hom-setoid — [rig_setoid] IS
 Instance/Top/Presheaf.v's [Maps_to_R], not a copy — but the
 operations are built pointwise from R's scalar operations,
 every law is re-proved by [ring], and the three functor laws
 of [ContinuousRingFunctor] are discharged by hand: exactly
 what the representability reading exists to avoid.  The
 general representable-lifting machinery (transferring
 algebraic structure along a representable functor) is issue
 #341's and is not built here — disclosed, not smuggled.

 3. WHAT IT COSTS.  This is the FOURTH file importing Coq.Reals
 (after Interval.v, FundamentalGroupoid.v, Presheaf.v), and it
 inherits the standard library's axioms for R exactly as
 docs/AXIOMS.md's “Stdlib axioms” section documents; the section
 enumerates this file alongside the other three, with the same
 measured per-constant discipline: 36 of the 38 constants carry
 the two axioms ([ClassicalDedekindReals.sig_forall_dec] and
 [functional_extensionality_dep]); the two zero/one-preservation
 obligations of [CRing_precomp], being pointwise reflexivity,
 carry [sig_forall_dec] alone; nothing touches the
 least-upper-bound property. 

 --------
 书籍：Mac Lane，《为工作数学家而设的范畴论》，第二版，§II.3 习题 5，印刷本第 40 页（PDF 第 50 页）—— maclane:II.3:ex5
 书籍：Awodey，《范畴论》（2005 年第一版预印本），§7.2，印刷本第 156 页（PDF 第 165 页）—— awodey:7.2:construction-continuous-real-functions-ring
 nLab：https://ncatlab.org/nlab/show/Top
 维基百科：https://en.wikipedia.org/wiki/Ring_(mathematics)

 Mac Lane 的习题：将每个空间 X 分配给连续实值函数环 C(X)（在逐点操作下），并将每个连续映射分配给前合成同态，是一个从空间到环的逆变函子——函数-代数对偶的基本对象。-  [cr_plus] / [cr_mult] / [cr_neg] / [cr_const]：连续映射 X ⟶ R_Top 的逐点代数，每一个都有其连续性证明
 -  [CRingOb X : RingObject]：C(X)，同态承载
 [ContinuousMorphism X R_Top] 在逐点结构下
 -  [CRing_precomp]：沿着连续映射的预合成是一个环同态
 -  [ContinuousRingFunctor : Top^op ⟶ Rng]：逆变函子，在库的标准编码中

 设计：1. 点操作的连续性是有限交的并。X 的拓扑是抽象的——在 X 上不存在 epsilon-delta——所以 f + g 的一个度量开集的原像只能通过如下方式表现为 X-开集：作为它包含的点 x 指数化的交集的并集，（f⁻¹ 在 f x 周围的小球）∩（g⁻¹ 在 g x 周围的小球），每个因子由于 f 和 g 自身的连续性而开集，按 X 公理进行并与交集，并通过三角不等式与实际原像逐点等价（[Rlin]）。对于乘积，半径通过局部界 M = |f x| + |g x| + 1 收缩（并且上限为 1，以保证 |f y| ≤ |f x| + 1），这是标准论证，[nra] 用于结束非线性估计。每个球的半径都是 DATA，在 Instance/Top/Interval.v 的学科中，所以没有选择原则出现。2. C(X) 是同态载体，但环结构并未从环对象 ℝ 转移——这一前提在此尚无法陈述。Awodey 的 §7.2 将 C(X) 视为 Hom_Top(X, ℝ)，其运算继承自作为 Top 内部环对象的 ℝ，因此函子性来源于可表示性，而不是通过手工验证。此树无法陈述该前提：一个内部环对象需要连续运算 ℝ × ℝ ⟶ ℝ，而 Top 还没有范畴积（Instance/Top.v 将乘积拓扑标注为未来工作）；库中的 [RingObject] 是集合层面逐元素的结构，这正是下面的 [CRingOb] 所包含的。所以载体字面上就是同态集合——[rig_setoid] 是 Instance/Top/Presheaf.v 的 [Maps_to_R]，而不是副本——但是运算是从 R 的标量运算逐点构建的，每条定律都由 [ring] 重新证明，[ContinuousRingFunctor] 的三个函子定律是手动处理的：正是可表示性解读存在的原因以避免这些做法。通用的可表示提升机制（沿着可表示函子转移代数结构）是问题 #341 的内容，这里没有构建——是公开的，而不是偷偷加入的。3. 成本。这是第四个导入 Coq.Reals 的文件（在 Interval.v、FundamentalGroupoid.v、Presheaf.v 之后），它完全继承标准库对 R 的公理，正如 docs/AXIOMS.md 中“Stdlib axioms”部分所记录的；该部分将此文件与其他三个文件列在一起，并采用相同的每个常量的度量方法：38 个常量中有 36 个都带有两个公理（[ClassicalDedekindReals.sig_forall_dec] 和 [functional_extensionality_dep]）；[CRing_precomp] 的两个零/一保持义务，是逐点自反性的，只带 [sig_forall_dec]；没有任何内容涉及最上界性质。
*)

(** ** Balls are open / ** 球开 *)

(* The metric ball around a point, as an open of the real line: at any interior point the slack radius witnesses openness (radius as data, no choice). / 点周围的度量球，作为实数轴的开集：在任何内部点处，松弛半径证明了开性（半径作为数据，无需选择）。 *)
Lemma ball_around (c d : R) :
  (0 < d)%R → ball_open BS_R (fun r : R => (Rabs (c - r) < d)%R).
Proof.
  intros Hd r Hr.
  exists (d - Rabs (c - r))%R; split.
  - RlinH.
  - intros y Hy; simpl in *.
    RlinH.
Qed.

(* * ** The pointwise algebra of continuous real-valued maps / * ** 连续实值映射的逐点代数 *)

Section Pointwise.

Context {X : TopSpace}.

(*
 Addition, pointwise; continuity by the union-of-intersections
 exhibition (design note 1). 

 --------
 加法，按点进行；通过交并展示的连续性（设计说明1）。
*)
Program Definition cr_plus (f g : ContinuousMorphism X R_Top) :
  ContinuousMorphism X R_Top := {|
  continuous_map :=
    {| morphism := fun x => (continuous_map f x + continuous_map g x)%R |}
|}.
Next Obligation.
  intros f g x y Hxy; simpl.
  rewrite (proper_morphism (continuous_map f) x y Hxy).
  rewrite (proper_morphism (continuous_map g) x y Hxy).
  reflexivity.
Qed.
Next Obligation.
  intros f g U HU.
  pose (I := { x : X & U ((continuous_map f x + continuous_map g x)%R) }).
  pose (rad := fun i : I =>
    projT1 (HU ((continuous_map f (projT1 i)
                   + continuous_map g (projT1 i))%R) (projT2 i))).
  apply (open_respects X (fun y =>
    { i : I
    & ((Rabs (continuous_map f (projT1 i) - continuous_map f y)
          < rad i / 2)%R
       ∧ (Rabs (continuous_map g (projT1 i) - continuous_map g y)
            < rad i / 2)%R) })).
  - intro y; split.
    + intros [i [Hf Hg]].
      destruct (HU _ (projT2 i)) as [d [Hd Hball]] eqn:Heq.
      apply Hball; simpl.
      unfold rad in Hf, Hg; rewrite Heq in Hf, Hg; simpl in Hf, Hg.
      RlinH.
    + intro Hy.
      unshelve eexists.
      * exact (y; Hy).
      * simpl; unfold rad; simpl.
        pose proof
          (fst (projT2 (HU ((continuous_map f y + continuous_map g y)%R)
                          Hy))) as Hd.
        assert (Hz : (Rabs (continuous_map f y - continuous_map f y)
                        = 0)%R).
        { replace ((continuous_map f y - continuous_map f y)%R)
            with 0%R by ring.
          exact Rabs_R0. }
        assert (Hz' : (Rabs (continuous_map g y - continuous_map g y)
                         = 0)%R).
        { replace ((continuous_map g y - continuous_map g y)%R)
            with 0%R by ring.
          exact Rabs_R0. }
        split; [ rewrite Hz | rewrite Hz' ];
        exact (Rdiv_lt_0_compat _ _ Hd Rlt_0_2).
  - apply open_union; intro i.
    apply open_inter.
    + apply (continuity f
        (fun v : R =>
           (Rabs (continuous_map f (projT1 i) - v) < rad i / 2)%R)).
      apply ball_around.
      exact (Rdiv_lt_0_compat _ _
               (fst (projT2 (HU ((continuous_map f (projT1 i)
                                    + continuous_map g (projT1 i))%R)
                               (projT2 i)))) Rlt_0_2).
    + apply (continuity g
        (fun v : R =>
           (Rabs (continuous_map g (projT1 i) - v) < rad i / 2)%R)).
      apply ball_around.
      exact (Rdiv_lt_0_compat _ _
               (fst (projT2 (HU ((continuous_map f (projT1 i)
                                    + continuous_map g (projT1 i))%R)
                               (projT2 i)))) Rlt_0_2).
Qed.

(* Multiplication, pointwise; the radius shrinks by the local bound and is capped at 1 (design note 1). / 逐点相乘；半径按局部界限缩小，并限制在1（设计说明1）。 *)
Program Definition cr_mult (f g : ContinuousMorphism X R_Top) :
  ContinuousMorphism X R_Top := {|
  continuous_map :=
    {| morphism := fun x => (continuous_map f x * continuous_map g x)%R |}
|}.
Next Obligation.
  intros f g x y Hxy; simpl.
  rewrite (proper_morphism (continuous_map f) x y Hxy).
  rewrite (proper_morphism (continuous_map g) x y Hxy).
  reflexivity.
Qed.
Next Obligation.
  intros f g U HU.
  pose (I := { x : X & U ((continuous_map f x * continuous_map g x)%R) }).
  pose (M := fun i : I =>
    (Rabs (continuous_map f (projT1 i))
       + Rabs (continuous_map g (projT1 i)) + 1)%R).
  pose (rad := fun i : I =>
    projT1 (HU ((continuous_map f (projT1 i)
                   * continuous_map g (projT1 i))%R) (projT2 i))).
  pose (del := fun i : I => Rmin 1 (rad i / (2 * M i))%R).
  apply (open_respects X (fun y =>
    { i : I
    & ((Rabs (continuous_map f (projT1 i) - continuous_map f y)
          < del i)%R
       ∧ (Rabs (continuous_map g (projT1 i) - continuous_map g y)
            < del i)%R) })).
  - intro y; split.
    + intros [i [Hf Hg]].
      destruct (HU _ (projT2 i)) as [d [Hd Hball]] eqn:Heq.
      apply Hball; simpl.
      unfold del, rad in Hf, Hg; rewrite Heq in Hf, Hg; simpl in Hf, Hg.
      set (fx := (continuous_map f (projT1 i) : R)) in *.
      set (gx := (continuous_map g (projT1 i) : R)) in *.
      set (fy := (continuous_map f y : R)) in *.
      set (gy := (continuous_map g y : R)) in *.
      assert (HM : (0 < Rabs fx + Rabs gx + 1)%R)
        by (pose proof (Rabs_pos fx); pose proof (Rabs_pos gx); lra).
      assert (Hδ1 : (Rabs (fx - fy) < 1)%R)
        by (eapply Rlt_le_trans; [ exact Hf | apply Rmin_l ]).
      assert (Hδd : (Rabs (fx - fy)
                       < d / (2 * (Rabs fx + Rabs gx + 1)))%R)
        by (eapply Rlt_le_trans; [ exact Hf | apply Rmin_r ]).
      assert (Hδd' : (Rabs (gx - gy)
                        < d / (2 * (Rabs fx + Rabs gx + 1)))%R)
        by (eapply Rlt_le_trans; [ exact Hg | apply Rmin_r ]).
      assert (Hfy : (Rabs fy <= Rabs fx + 1)%R).
      { pose proof (Rabs_triang_inv fy fx).
        pose proof (Rabs_minus_sym fx fy).
        lra. }
      assert (Key : (Rabs (fx * gx - fy * gy)
                       <= Rabs fy * Rabs (gx - gy)
                            + Rabs gx * Rabs (fx - fy))%R).
      { replace ((fx * gx - fy * gy)%R)
          with ((fy * (gx - gy) + gx * (fx - fy))%R) by ring.
        pose proof (Rabs_triang (fy * (gx - gy))%R (gx * (fx - fy))%R).
        rewrite Rabs_mult in H.
        rewrite (Rabs_mult gx (fx - fy)%R) in H.
        exact H. }
      simpl.
      assert (Hgxpos := Rabs_pos gx).
      assert (Hfypos := Rabs_pos fy).
      assert (Habs1 := Rabs_pos (gx - gy)%R).
      assert (Habs2 := Rabs_pos (fx - fy)%R).
      clear Heq Hball Hf Hg.
      clearbody fx gx fy gy.
      clear dependent X.
      set (A := (d / (2 * (Rabs fx + Rabs gx + 1)))%R) in *.
      assert (HApos : (0 < A)%R)
        by (apply Rdiv_lt_0_compat; lra).
      assert (Hdiv : ((2 * (Rabs fx + Rabs gx + 1)) * A = d)%R)
        by (unfold A; field; lra).
      clearbody A.
      nra.
    + intro Hy.
      unshelve eexists.
      * exact (y; Hy).
      * simpl; unfold del, rad, M; simpl.
        pose proof
          (fst (projT2 (HU ((continuous_map f y * continuous_map g y)%R)
                          Hy))) as Hd.
        set (d := projT1 (HU ((continuous_map f y
                                 * continuous_map g y)%R) Hy)) in *.
        set (fx := (continuous_map f y : R)) in *.
        set (gx := (continuous_map g y : R)) in *.
        assert (Hz : (Rabs (fx - fx) = 0)%R).
        { replace ((fx - fx)%R) with 0%R by ring.
          exact Rabs_R0. }
        assert (Hz' : (Rabs (gx - gx) = 0)%R).
        { replace ((gx - gx)%R) with 0%R by ring.
          exact Rabs_R0. }
        assert (HM : (0 < Rabs fx + Rabs gx + 1)%R).
        { pose proof (Rabs_pos fx); pose proof (Rabs_pos gx).
          clearbody d fx gx; clear dependent X; lra. }
        assert (Hmin : (0 < Rmin 1 (d / (2 * (Rabs fx + Rabs gx + 1))))%R).
        { apply Rmin_glb_lt; [ exact Rlt_0_1 | ].
          apply Rdiv_lt_0_compat; [ exact Hd | ].
          clearbody d fx gx; clear dependent X; lra. }
        split; [ rewrite Hz | rewrite Hz' ]; exact Hmin.
  - apply open_union; intro i.
    apply open_inter.
    + apply (continuity f
        (fun v : R =>
           (Rabs (continuous_map f (projT1 i) - v) < del i)%R)).
      apply ball_around.
      unfold del, rad, M.
      pose proof
        (fst (projT2 (HU ((continuous_map f (projT1 i)
                             * continuous_map g (projT1 i))%R)
                        (projT2 i)))) as Hd.
      set (fx := (continuous_map f (projT1 i) : R)) in *.
      set (gx := (continuous_map g (projT1 i) : R)) in *.
      set (d := projT1 (HU ((fx * gx)%R) (projT2 i))) in *.
      assert (HM : (0 < Rabs fx + Rabs gx + 1)%R).
      { pose proof (Rabs_pos fx); pose proof (Rabs_pos gx).
        clearbody d fx gx; clear dependent X; lra. }
      apply Rmin_glb_lt; [ exact Rlt_0_1 | ].
      apply Rdiv_lt_0_compat; [ exact Hd | ].
      clearbody d fx gx; clear dependent X; lra.
    + apply (continuity g
        (fun v : R =>
           (Rabs (continuous_map g (projT1 i) - v) < del i)%R)).
      apply ball_around.
      unfold del, rad, M.
      pose proof
        (fst (projT2 (HU ((continuous_map f (projT1 i)
                             * continuous_map g (projT1 i))%R)
                        (projT2 i)))) as Hd.
      set (fx := (continuous_map f (projT1 i) : R)) in *.
      set (gx := (continuous_map g (projT1 i) : R)) in *.
      set (d := projT1 (HU ((fx * gx)%R) (projT2 i))) in *.
      assert (HM : (0 < Rabs fx + Rabs gx + 1)%R).
      { pose proof (Rabs_pos fx); pose proof (Rabs_pos gx).
        clearbody d fx gx; clear dependent X; lra. }
      apply Rmin_glb_lt; [ exact Rlt_0_1 | ].
      apply Rdiv_lt_0_compat; [ exact Hd | ].
      clearbody d fx gx; clear dependent X; lra.
Qed.

(* Negation, pointwise: an isometry, so the same radius works. / 否定，逐点：是一种等距映射，所以同样的半径适用。 *)
Program Definition cr_neg (f : ContinuousMorphism X R_Top) :
  ContinuousMorphism X R_Top := {|
  continuous_map :=
    {| morphism := fun x => (- continuous_map f x)%R |}
|}.
Next Obligation.
  intros f x y Hxy; simpl.
  rewrite (proper_morphism (continuous_map f) x y Hxy).
  reflexivity.
Qed.
Next Obligation.
  intros f U HU.
  pose (I := { x : X & U ((- continuous_map f x)%R) }).
  pose (rad := fun i : I =>
    projT1 (HU ((- continuous_map f (projT1 i))%R) (projT2 i))).
  apply (open_respects X (fun y =>
    { i : I
    & (Rabs (continuous_map f (projT1 i) - continuous_map f y)
         < rad i)%R })).
  - intro y; split.
    + intros [i Hf].
      destruct (HU _ (projT2 i)) as [d [Hd Hball]] eqn:Heq.
      apply Hball; simpl.
      unfold rad in Hf; rewrite Heq in Hf; simpl in Hf.
      RlinH.
    + intro Hy.
      unshelve eexists.
      * exact (y; Hy).
      * simpl; unfold rad; simpl.
        pose proof
          (fst (projT2 (HU ((- continuous_map f y)%R) Hy))) as Hd.
        assert (Hz : (Rabs (continuous_map f y - continuous_map f y)
                        = 0)%R).
        { replace ((continuous_map f y - continuous_map f y)%R)
            with 0%R by ring.
          exact Rabs_R0. }
        rewrite Hz; exact Hd.
  - apply open_union; intro i.
    apply (continuity f
      (fun v : R =>
         (Rabs (continuous_map f (projT1 i) - v) < rad i)%R)).
    apply ball_around.
    exact (fst (projT2 (HU ((- continuous_map f (projT1 i))%R)
                          (projT2 i)))).
Qed.

(* Constants are continuous: the preimage of any open is uniform. / 常数是连续的：任意开集的原像是均匀的。 *)
Program Definition cr_const (c : R) : ContinuousMorphism X R_Top := {|
  continuous_map := {| morphism := fun _ => c |}
|}.
Next Obligation.
  intros c x y Hxy; reflexivity.
Qed.
Next Obligation.
  intros c U HU.
  exact (open_const X (U c)).
Qed.

End Pointwise.

(** ** C(X), as a ring / ** C(X)，作为一个环 *)

(*
 Since the PR “algebraic carriers are sets” (2026-09-17) a [RigObject] owes
 a [Prop]-valued mirror of its equality.  Two continuous maps into ℝ are
 identified POINTWISE (Instance/Top.v's [ContinuousMorphism_equiv]), and
 the real line's own `≈` is Instance/Top/Presheaf.v's [R_equiv], which is
 Coq's [eq] under a [Type] ascription and hence already a [Prop].  So the
 mirror is the same pointwise comparison read in [Prop] and both
 implications are the identity; no reals axiom is spent and nothing is
 truncated. 

 --------
 自从 PR “代数承载体是集合” (2026-09-17) 以来，一个 [RigObject] 承担一个 [Prop] 值的等式镜像。两个到 ℝ 的连续映射在点上被识别（Instance/Top.v 的 [ContinuousMorphism_equiv]），而实数线自身的 `≈` 是 Instance/Top/Presheaf.v 的 [R_equiv]，它是在 [Type] 指定下的 Coq 的 [eq]，因此已经是一个 [Prop]。因此，镜像就是以 [Prop] 阅读的相同点对点比较，并且两种蕴涵都是恒等；没有消耗实数公理，也没有任何被截断。
*)
Program Definition CRingOb (X : TopSpace) : RingObject := {|
  ring_rig := {|
    rig_setoid := Maps_to_R X;
    rig_zero := cr_const 0%R;
    rig_add := cr_plus;
    rig_one := cr_const 1%R;
    rig_mul := cr_mult;
    rig_prop := @PropEquiv_of_relation _ (is_setoid (Maps_to_R X))
                  (fun f g => forall x : X,
                     @eq R (continuous_map f x) (continuous_map g x))
                  (fun _ _ h => h) (fun _ _ h => h)
  |};
  ring_neg := cr_neg
|}.
Next Obligation.
  intros X f f' Hf g g' Hg x; simpl.
  rewrite (Hf x), (Hg x); reflexivity.
Qed.
Next Obligation.
  intros X f f' Hf g g' Hg x; simpl.
  rewrite (Hf x), (Hg x); reflexivity.
Qed.
Next Obligation.
  intros X f g h x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f g x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f g h x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f g h x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f g h x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f x; simpl; unfold R_equiv; ring.
Qed.
Next Obligation.
  intros X f f' Hf x; simpl.
  rewrite (Hf x); reflexivity.
Qed.
Next Obligation.
  intros X f x; simpl; unfold R_equiv; ring.
Qed.

(* * ** Precomposition, and the functor / * ** 预组合，以及函子 *)

(*
 Precomposition along a continuous map is a ring homomorphism: every
 preservation law is pointwise reflexivity, the operations being
 pointwise. 

 --------
 沿连续映射的预组合是一个环同态：每个保持律都是逐点自反性的，其运算也是逐点的。
*)
Program Definition CRing_precomp {Y X : TopSpace}
  (h : ContinuousMorphism Y X) :
  RigHom (CRingOb X) (CRingOb Y) := {|
  rig_map := {| morphism := fun f => top_compose f h |}
|}.
Next Obligation.
  intros Y X h f f' Hf y; simpl.
  exact (Hf (continuous_map h y)).
Qed.
Next Obligation.
  intros Y X h y; simpl; reflexivity.
Qed.
Next Obligation.
  intros Y X h f g y; simpl; reflexivity.
Qed.
Next Obligation.
  intros Y X h y; simpl; reflexivity.
Qed.
Next Obligation.
  intros Y X h f g y; simpl; reflexivity.
Qed.

(*
 Mac Lane §II.3 Exercise 5: C, contravariantly, from spaces to rings.
 The arrow action is [contramap] of the hom into the ring object ℝ
 (design note 2). 

 --------
 Mac Lane §II.3 练习 5：C，从空间到环，逆变。
 箭头作用是将同构映射到环对象 ℝ 的 [contramap]（设计注释 2）。
*)
Program Definition ContinuousRingFunctor : Top^op ⟶ Rng := {|
  fobj := fun X => CRingOb X;
  fmap := fun X Y h => CRing_precomp (unop h)
|}.
Next Obligation.
  intros X Y h h' Hh f y; simpl.
  exact (proper_morphism (continuous_map f) _ _ (Hh y)).
Qed.
Next Obligation.
  intros X f y; simpl; reflexivity.
Qed.
Next Obligation.
  intros X Y Z h h' f y; simpl; reflexivity.
Qed.
