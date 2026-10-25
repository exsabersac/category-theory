Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Semicartesian.Proofs.
Require Import Category.Structure.Monoidal.CompactClosed.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.

Generalizable All Variables.

(*
   * * Collapse theorems for over-structured tensors

   Two classical "no-go" results delimiting how much algebraic structure a
   monoidal category can carry before it degenerates.  Both are theorems
   about *seam discipline*: they are the mathematical reason copying
   (comonoid/Frobenius) structure must be withheld from a tensor that is
   already cartesian, and uniform copying must be withheld from a tensor
   that is compact closed.

   1. Frobenius collapse: a Frobenius object in a semicartesian (in
   particular, cartesian) monoidal category is isomorphic to the unit.

   2. Abramsky's no-cloning theorem (arXiv:0910.2401): in a compact closed
   category, uniform copying — a natural, monoidal, coassociative,
   cocommutative diagonal, i.e. exactly a [RelevanceMonoidal] structure —
   forces the braiding at every diagonal square to be the identity.

   nLab: https://ncatlab.org/nlab/show/Frobenius+algebra
   nLab: https://ncatlab.org/nlab/show/no-cloning+theorem 

   --------
   * * 针对过度结构化张量的塌缩定理

   两个经典的“不可达”结果限制了单体范畴在退化之前可以承载的代数结构量。两者都是关于*接缝规律*的定理：它们是数学上解释为什么复制（余单体/Frobenius）结构必须从已经是笛卡尔的张量中排除，并且为什么均匀复制必须从紧闭的张量中排除的原因。

   1. Frobenius塌缩：半笛卡尔（特别是笛卡尔）单体范畴中的Frobenius对象同构于单位对象。2. Abramsky 的不可克隆定理 (arXiv:0910.2401)：在一个紧闭范畴中，统一复制——一种自然的、幺半群的、满足余结合律和余交换律的对角结构，即完全的 [RelevanceMonoidal] 结构——会迫使每个对角方块处的编织是恒等映射。

   nLab: https://ncatlab.org/nlab/show/Frobenius+algebra
   nLab: https://ncatlab.org/nlab/show/no-cloning+theorem
*)

(*
   * ** Frobenius objects collapse in (semi)cartesian monoidal categories

   Let (X, μ, η, δ, ε) be a Frobenius algebra in a monoidal category whose
   unit I is terminal ([SemicartesianMonoidal]).  Terminality identifies ε
   with the discard map, so the comonoid counit laws say precisely that the
   projections retract δ.  Projecting the Frobenius law

   (μ ⨂ id) ∘ α⁻¹ ∘ (id ⨂ δ) ≈ δ ∘ μ

   with proj_right then collapses the multiplication: μ ≈ proj_right (in
   generalized-element notation, μ(x, y) = y).  Evaluating the monoid's
   right unit law at that equation yields η ∘ ε ≈ id, and ε ∘ η ≈ id[I]
   holds by terminality, so ε : X ≅ I : η.

   The cartesian case (Fox's setting, where the tensor is the product) is
   the instance used by the seam-discipline arguments: a cartesian colour
   cannot host a Frobenius algebra on any object except (up to iso) the
   unit.  Note the proof below never uses the diagonal: semicartesian
   suffices. 

   --------
   * ** Frobenius 对象在（半）笛卡尔单态范畴中塌缩  

   设 (X, μ, η, δ, ε) 是单态范畴中的一个 Frobenius 代数，其单位 I 是终对象 ([SemicartesianMonoidal])。终性将 ε 识别为丢弃映射，因此余单子余单位律恰好说明投影是 δ 的回退。将 Frobenius 律

   (μ ⨂ id) ∘ α⁻¹ ∘ (id ⨂ δ) ≈ δ ∘ μ  

   用 proj_right 投影后就塌缩了乘法：μ ≈ proj_right（在广义元素记法中，μ(x, y) = y）。在该方程上评估单子右单位律得到 η ∘ ε ≈ id，并且 ε ∘ η ≈ id [I] 由终性成立，所以 ε : X ≅ I : η。笛卡尔情况（Fox 的设定，其中张量是积）是缝合学科论证中使用的实例：笛卡尔对象不能在除单位（最多同构）之外的任何对象上承载 Frobenius 代数。注意下面的证明从未使用对角线：半笛卡尔就足够了。
*)

Section FrobeniusCollapse.

Context {C : Category}.
Context `{M : @Monoidal C}.
Context `{SM : @SemicartesianMonoidal C M}.

(* The counit of any comonoid is the discard map (both live in the terminal hom-set X ~> I), so the left counit law makes proj_right retract delta. / 任何余单子的余单位都是丢弃映射（都位于终端同态集 X ~> I 中），因此左余单位律使 proj_right 收缩 δ。 *)
Lemma proj_right_delta {X : C} (Co : Comonoid X) :
  proj_right ∘ delta[Co] ≈ id[X].
Proof.
  unfold proj_right.
  rewrite <- comp_assoc.
  rewrite (unit_terminal (@eliminate C M SM X) epsilon[Co]).
  rewrite (delta_counit_left (Comonoid := Co)).
  apply iso_to_from.
Qed.

(* Mirror image: proj_left retracts delta via the right counit law. / 镜像：proj_left 通过右余单位律回缩 delta。 *)
Lemma proj_left_delta {X : C} (Co : Comonoid X) :
  proj_left ∘ delta[Co] ≈ id[X].
Proof.
  unfold proj_left.
  rewrite <- comp_assoc.
  rewrite (unit_terminal (@eliminate C M SM X) epsilon[Co]).
  rewrite (delta_counit_right (Comonoid := Co)).
  apply iso_to_from.
Qed.

Section FrobeniusObject.

Context {X : C}.
Context (F : @Frobenius C M X).

(*
 Projecting the left Frobenius law with proj_right collapses the
 multiplication to the right projection: μ(x, y) = y on generalized
 elements.  (Dually, the right Frobenius law would give μ ≈ proj_left.) 

 --------
 使用 proj_right 投影左 Frobenius 定律会将乘法坍缩到右投影：μ(x, y) = y 在广义元素上。(对偶地，右 Frobenius 定律会得到 μ ≈ proj_left。)
*)
Lemma frobenius_mu_collapse : mu[F] ≈ @proj_right C M SM X X.
Proof.
  rewrite <- (id_left (mu[F])).
  rewrite <- (proj_right_delta F).
  rewrite <- comp_assoc.
  rewrite <- (frob_law_left (Frobenius := F)).
  rewrite !comp_assoc.
  rewrite proj_right_natural.
  rewrite id_left.
  rewrite <- proj_right_right.
  rewrite <- comp_assoc.
  rewrite proj_right_natural.
  rewrite comp_assoc.
  rewrite (proj_right_delta F).
  apply id_left.
Qed.

(*
 The monoid's right unit law μ ∘ (id ⨂ η) ≈ ρ evaluated at
 μ ≈ proj_right forces η to be a two-sided inverse of ε on X. 

 --------
 单元的右单元律 μ ∘ (id ⨂ η) ≈ ρ 在 μ ≈ proj_right 上的求值强制 η 成为 X 上 ε 的双边逆。
*)
Lemma frobenius_eta_epsilon : eta[F] ∘ epsilon[F] ≈ id[X].
Proof using C F M SM X.
  pose proof (mu_unit_right (Monoid := F)) as MU.
  rewrite frobenius_mu_collapse in MU.
  rewrite proj_right_natural in MU.
  rewrite (unit_terminal epsilon[F] (proj_right ∘ unit_right⁻¹)).
  rewrite comp_assoc.
  rewrite MU.
  apply iso_to_from.
Qed.

(*
 A Frobenius object in a semicartesian monoidal category is isomorphic to
 the monoidal unit, with the counit and unit of the Frobenius structure as
 the two directions. 

 --------
 半笛卡尔单体范畴中的 Frobenius 对象同构于单体对象，其 Frobenius 结构的余单位和单位分别作为两个方向。
*)
Theorem frobenius_collapse_semicartesian : X ≅ I.
Proof using C F M SM X.
  isomorphism.
  - exact (epsilon[F]).
  - exact (eta[F]).
  - apply unit_terminal.
  - apply frobenius_eta_epsilon.
Qed.

End FrobeniusObject.

End FrobeniusCollapse.

(*
 The cartesian instance: in a cartesian monoidal category — where the
 tensor is the categorical product — every Frobenius object collapses to
 the terminal unit (cf. Heunen & Vicary, "Categories for Quantum Theory",
 Oxford UP, 2019, Ch. 5 on Frobenius structures).  This is the
 load-bearing form for seam discipline: no special commutative Frobenius
 structure can live on a colour whose ambient tensor is cartesian. 

 --------
 笛卡尔实例：在一个笛卡尔单体范畴中——其张量是范畴积——每个弗罗贝尼乌斯对象都坍缩为终单位（参见 Heunen & Vicary，《量子理论的范畴》，牛津大学出版社，2019，第5章关于弗罗贝尼乌斯结构）。 这是接缝规范的承重形式：没有特殊的交换弗罗贝尼乌斯结构可以存在于其环境张量为笛卡尔的颜色上。
*)
Theorem frobenius_collapse {C : Category} `{H : @CartesianMonoidal C} {X : C}
        (F : @Frobenius C _ X) : X ≅ I.
Proof.
  exact (frobenius_collapse_semicartesian F).
Qed.

(*
   * ** Abramsky's no-cloning theorem

   Abramsky, "No-Cloning in categorical quantum mechanics" (arXiv:0910.2401),
   §4.  Uniform copying in a symmetric monoidal category is a monoidal
   natural diagonal that is coassociative and cocommutative — precisely the
   [RelevanceMonoidal] structure.  The proofs below consume only
   [diagonal_natural] (naturality), [diagonal_unit] (∆I = λ⁻¹),
   [diagonal_braid2] (monoidality) and [braid_diagonal] (cocommutativity);
   coassociativity ([diagonal_tensor_assoc]) is carried by the class but
   never used, so the no-go applies just as well to a non-coassociative
   copying operation.

   The theorem: if such a category is moreover compact closed, the braiding
   σ_{x,x} on every diagonal square is the identity ("the twist map is the
   identity", the boxed Second Step of op. cit.), from which Abramsky's
   Theorem 11 (every endomorphism is a scalar multiple of the identity)
   follows.  The proof formalized here reorganizes the paper's Lemma 13:

   1. Copying the cup η : I ~> x* ⨂ x and regrouping by colour shows the
   two-cup state braid2 ∘ (η ⨂ η) ∘ λ⁻¹ *is* the copied state
   (∆x* ⨂ ∆x) ∘ η          ([cups_mid_diagonal]);

   2. cocommutativity of ∆x therefore lets the two x-wires of the two-cup
   state be swapped silently  ([cups_mid_braid]) — the "confusion of
   entanglements";

   3. capping each input x-wire against one of the two duals turns that
   silent swap into σ ∘ - on the outputs ([close_braid]), while a double
   yanking evaluates the closure of the two-cup state to the braiding
   itself ([close_cups_mid]); combining gives σ ≈ σ ∘ σ ≈ id. 

   --------
   * ** Abramsky 的不可克隆定理

   Abramsky, 《范畴量子力学中的不可克隆》(arXiv:0910.2401),
   §4. 对称幺半范畴中的统一复制是一种具有余结合性和余交换性的幺半自然对角线 —— 正是 [RelevanceMonoidal] 结构。以下证明仅使用了 [diagonal_natural]（自然性）、[diagonal_unit]（∆I = λ⁻¹）、[diagonal_braid2]（幺半性）和 [braid_diagonal]（余交换性）；余结合性（[diagonal_tensor_assoc]）由类提供，但从未使用，因此该不可行结论同样适用于非余结合的复制操作。定理：如果这样的范畴另外是紧闭范畴，那么每个对角方格上的编织σ_{x,x}是恒等映射（“扭转映射是恒等映射”，即引文中的第二步方框），由此可以得出Abramsky的定理11（每个自同态都是恒等映射的标量倍）。这里形式化的证明重新组织了论文的引理13：

   1. 复制cup η : I ~> x* ⨂ x 并按颜色重新组合，显示两杯态 braid2 ∘ (η ⨂ η) ∘ λ⁻¹ *就是*复制后的态 (∆x* ⨂ ∆x) ∘ η          ([cups_mid_diagonal])；

   2. 因为∆x是协交换的，所以可以悄无声息地交换两杯态的两个x线 ([cups_mid_braid])——即“纠缠的混乱”；3. 将每个输入 x-线封顶到两个对偶之一，会将该静默交换转变为输出上的 σ ∘ - ([close_braid])，而双拉动则会将双杯态的闭合计算为编织本身 ([close_cups_mid])；组合后得到 σ ≈ σ ∘ σ ≈ id。
*)

Section NoCloning.

Context {C : Category}.
Context `{R : @RelevanceMonoidal C}.
Context `{CC : @CompactClosed C (@relevance_is_symmetric C R)}.

(*
 Naturality of the diagonal, in rewriting form: ∆ is a natural
 transformation from the identity functor to the squaring functor. 

 --------
 对角线的自然性，以重写形式表示：∆ 是从恒等函子到平方函子的自然变换。
*)
Lemma diagonal_natural' {a b : C} (f : a ~> b) :
  f ⨂ f ∘ ∆a ≈ ∆b ∘ f.
Proof.
  spose (@diagonal_natural C R) as X0.
  apply X0.
Qed.

(*
 The middle-four interchange is involutive: swapping the middle two
 factors twice is the identity.  (The two instances have their middle
 arguments transposed.) 

 --------
 中间四项交换是自反的：将中间两个因子交换两次就是恒等操作。（这两个实例的中间参数被互换。）
*)
Lemma braid2_invol {a b c e : C} :
  @braid2 C R a c b e ∘ @braid2 C R a b c e ≈ id[((a ⨂ b) ⨂ (c ⨂ e))%object].
Proof.
  unfold braid2.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to tensor_assoc) (tensor_assoc⁻¹)).
  rewrite iso_to_from, id_left.
  normal.
  rewrite <- (comp_assoc _ (tensor_assoc⁻¹) (to tensor_assoc)).
  rewrite iso_from_to, id_right.
  rewrite <- (comp_assoc _ (braid ⨂ id) (braid ⨂ id)).
  rewrite <- bimap_comp.
  rewrite braid_invol, id_left.
  rewrite bimap_id_id, id_right.
  rewrite iso_to_from, bimap_id_id, id_right.
  apply iso_from_to.
Qed.

(*
 [braid2] is a definitional field of [RelevanceMonoidal]; statements of
 other fields (e.g. [diagonal_braid2]) carry its body inlined.  This fold
 lemma lets those occurrences be rewritten back to the named form. 

 --------
 [braid2] 是 [RelevanceMonoidal] 的定义字段；其他字段的语句（例如 [diagonal_braid2]）将其主体内联。这个折叠引理允许那些出现被重写回命名形式。
*)
Lemma braid2_unfold {a b c e : C} :
  @braid2 C R a b c e ≈
  tensor_assoc⁻¹ ∘ id ⨂ (tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc⁻¹)
    ∘ tensor_assoc.
Proof. reflexivity. Qed.

(*
 The generic monoidal coherences the argument below leans on —
 [unit_identity_from] (λ_I⁻¹ ≈ ρ_I⁻¹), the solved triangle forms
 [tensor_assoc_unit_right] and [tensor_assoc_from_unit_left], and the
 solved pentagon [pentagon_step] — are imported from the shared toolkit
 in Structure/Monoidal/Braided/Proofs.v, where they are stated for any
 [Monoidal] category. 

 --------
 下面论证依赖的一般单伴性相干性——[unit_identity_from]（λ_I⁻¹ ≈ ρ_I⁻¹）、已解决的三角形形成 [tensor_assoc_unit_right] 和 [tensor_assoc_from_unit_left]，以及已解决的五边形 [pentagon_step]——是从 Structure/Monoidal/Braided/Proofs.v 的共享工具包中导入的，其中它们对任何 [Monoidal] 类别都作了陈述。
*)

Section Cloning.

Context {x : C}.

Notation d := (dual x).

(* The two parallel cups η ⨂ η, as a single state of (x* ⨂ x) ⨂ (x* ⨂ x). / 两个平行的杯 η ⨂ η，作为 (x* ⨂ x) ⨂ (x* ⨂ x) 的单一状态。 *)
Definition cups : I ~> ((d ⨂ x) ⨂ (d ⨂ x))%object :=
  cc_unit x ⨂ cc_unit x ∘ unit_left⁻¹.

(* The same state regrouped by colour, as a state of (x* ⨂ x* ) ⨂ (x ⨂ x). / 同一态按颜色重新组合，作为态 (x* ⨂ x* ) ⨂ (x ⨂ x)。 *)
Definition cups_mid : I ~> ((d ⨂ d) ⨂ (x ⨂ x))%object :=
  braid2 ∘ cups.

(* Naturality of ∆ at the cup, with ∆I = λ⁻¹: copying the cup is the diagonal of the cup. This is the upper square of Abramsky's Lemma 13. / 在杯子的∆的自然性，且∆I = λ⁻¹：复制杯子是杯子的对角线。这是Abramsky引理13的上方正方形。 *)
Lemma cups_diagonal : cups ≈ ∆(d ⨂ x) ∘ cc_unit x.
Proof.
  unfold cups.
  rewrite <- diagonal_unit.
  apply diagonal_natural'.
Qed.

(* Regrouped by colour, the two-cup state is the tensor of the two componentwise diagonals: monoidality of ∆ ([diagonal_braid2]) cancels against the regrouping via [braid2_invol]. / 按颜色重新分组，双杯状态是两个分量对角线的张量：∆（[diagonal_braid2]）的幺半群性与通过[braid2_invol]进行的重新分组相抵消。 *)
Lemma cups_mid_diagonal : cups_mid ≈ ∆d ⨂ ∆x ∘ cc_unit x.
Proof.
  unfold cups_mid.
  rewrite cups_diagonal.
  rewrite diagonal_braid2.
  rewrite <- braid2_unfold.
  rewrite !comp_assoc.
  rewrite braid2_invol.
  now rewrite id_left.
Qed.

(* Cocommutativity of ∆x, tensored on the right: the two x-wires of the regrouped two-cup state can be swapped silently. This is the state-level "confusion of entanglements". / ∆x 的余交换性，右侧张量：可以悄无声息地交换重新分组的双杯状态的两个 x 线。这是状态层面的“纠缠混淆”。 *)
Lemma cups_mid_braid :
  id[(d ⨂ d)%object] ⨂ braid ∘ cups_mid ≈ cups_mid.
Proof.
  rewrite !cups_mid_diagonal.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite braid_diagonal, id_left.
  reflexivity.
Qed.

(* The two-cup state built sequentially: the second cup is tensored to the right of the first. / 两个杯子状态按顺序构建：第二个杯子在第一个的右侧张量化。 *)
Lemma cups_split :
  cups ≈ id[(d ⨂ x)%object] ⨂ cc_unit x ∘ unit_right⁻¹ ∘ cc_unit x.
Proof.
  unfold cups.
  rewrite unit_identity_from.
  rewrite <- bimap_id_left_right.
  rewrite <- comp_assoc.
  rewrite from_unit_right_natural.
  rewrite comp_assoc.
  reflexivity.
Qed.

(*
 A single yanking stage: cap the leading x against the leading dual and
 pass the remainder through.  [bend] at Z := x, precomposed with a cup, is
 the left snake identity. 

 --------
 单一拉动阶段：将前导 x 与前导双进行对齐，然后将其余部分通过。[bend] 在 Z := x 时，预组合一个 cup，是左蛇形恒等式。
*)
Definition bend {Z : C} : (x ⨂ (d ⨂ Z))%object ~> Z :=
  unit_left ∘ cc_counit x ⨂ id[Z] ∘ tensor_assoc⁻¹.

(* bend is natural in the pass-through component. / 弯曲在直通组件中是自然的。 *)
Lemma bend_natural {Z Z' : C} (q : Z ~> Z') :
  bend ∘ id[x] ⨂ (id[d] ⨂ q) ≈ q ∘ bend.
Proof.
  unfold bend.
  rewrite <- comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  rewrite bimap_id_id.
  rewrite (comp_assoc (unit_left ∘ cc_counit x ⨂ id[Z'])
             (id[(x ⨂ d)%object] ⨂ q) (tensor_assoc⁻¹)).
  rewrite <- (comp_assoc unit_left (cc_counit x ⨂ id[Z'])
                (id[(x ⨂ d)%object] ⨂ q)).
  rewrite bimap_id_right_left.
  rewrite <- bimap_id_left_right.
  rewrite comp_assoc.
  rewrite <- to_unit_left_natural.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(* The left snake identity, phrased with [bend]. / 左蛇身份，用 [bend] 表示。 *)
Lemma bend_snake : bend ∘ id[x] ⨂ cc_unit x ∘ unit_right⁻¹ ≈ id[x].
Proof.
  unfold bend.
  apply snake_left.
Qed.

(*
 A corollary of the second hexagon: braiding a whole pair past x and then
 swapping inside the left factor is braiding the two inner x-wires. 

 --------
 第二个六边形的一个推论：将一整对编织过x，然后在左因子内交换，就是编织两个内部的x线。
*)
Lemma braid_pass {y : C} :
  braid ⨂ id[x] ∘ tensor_assoc⁻¹ ∘ @braid C _ (y ⨂ x)%object x
    ≈ tensor_assoc⁻¹ ∘ id[y] ⨂ braid ∘ tensor_assoc.
Proof.
  pose proof (@hexagon_identity_sym C _ y x x) as HX.
  assert (HX' : (@tensor_assoc C _ x y x)⁻¹ ∘ @braid C _ (y ⨂ x)%object x
                  ≈ braid ⨂ id[x] ∘ tensor_assoc⁻¹ ∘ id[y] ⨂ braid
                      ∘ tensor_assoc).
  { rewrite <- HX.
    rewrite <- !comp_assoc.
    rewrite iso_from_to, id_right.
    reflexivity. }
  rewrite <- comp_assoc.
  rewrite HX'.
  rewrite !comp_assoc.
  rewrite <- bimap_comp.
  rewrite braid_invol, id_left.
  rewrite bimap_id_id, id_left.
  reflexivity.
Qed.

(*
 Passing a wire over a freshly inserted cup from the right equals passing
 it under from the left: the hexagon absorbs the crossing.  (In Abramsky's
 diagrams this is how the crossing of the "confused" cups is normalized.) 

 --------
 将一根线从右侧穿过新插入的杯子，相当于从左侧从下方穿过：六角形吸收了交叉。（在Abramsky的图中，这就是“混乱”杯子的交叉如何被规范化的方式。）
*)
Lemma cup_pass :
  tensor_assoc ∘ braid ⨂ id[x] ∘ tensor_assoc⁻¹ ∘ id[x] ⨂ cc_unit x
      ∘ unit_right⁻¹
    ≈ id[d] ⨂ braid ∘ tensor_assoc ∘ cc_unit x ⨂ id[x] ∘ unit_left⁻¹.
Proof.
  rewrite <- braid_unit_right_from.
  rewrite comp_assoc.
  rewrite <- (comp_assoc _ (id[x] ⨂ cc_unit x) (@braid C _ I x)).
  rewrite bimap_braid.
  rewrite <- (comp_assoc (to tensor_assoc) (braid ⨂ id[x]) (tensor_assoc⁻¹)).
  rewrite (comp_assoc _ (@braid C _ (d ⨂ x)%object x) (cc_unit x ⨂ id[x])).
  rewrite <- (comp_assoc (to tensor_assoc) (braid ⨂ id[x] ∘ tensor_assoc⁻¹)
                (@braid C _ (d ⨂ x)%object x)).
  rewrite braid_pass.
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(*
 The α-normalized two-cup state, sequentially: first cup at the head, the
 second inserted inside it, with the crossing pushed onto the x-wires by
 [cup_pass].  This is the state that the two-stage closure below consumes
 snake by snake. 

 --------
 α-归一化的双杯状态，顺序如下：第一个杯在顶部，第二个杯插入其中，交叉通过 [cup_pass] 推到 x 线。这就是下面两阶段闭合逐条消耗蛇的状态。
*)
Lemma cups_mid_nested :
  to tensor_assoc ∘ cups_mid
    ≈ id[d] ⨂ (id[d] ⨂ braid ∘ tensor_assoc ∘ cc_unit x ⨂ id[x]
                 ∘ unit_left⁻¹)
        ∘ cc_unit x.
Proof.
  unfold cups_mid.
  rewrite cups_split.
  rewrite braid2_unfold.
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  rewrite <- (@bimap_id_id C C C (@tensor C _) d x).
  rewrite <- (comp_assoc _ (to tensor_assoc) ((id[d] ⨂ id[x]) ⨂ cc_unit x)).
  rewrite <- to_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to tensor_assoc) (unit_right⁻¹) (cc_unit x)).
  rewrite tensor_assoc_unit_right.
  normal.
  rewrite cup_pass.
  reflexivity.
Qed.

(* The left snake identity, solved for the inverse unitor. / 左蛇身份，解出逆单位元。 *)
Lemma snake_left_from :
  cc_counit x ⨂ id[x] ∘ tensor_assoc⁻¹ ∘ id[x] ⨂ cc_unit x ∘ unit_right⁻¹
    ≈ unit_left⁻¹.
Proof.
  apply (iso_to_monic unit_left).
  rewrite iso_to_from.
  rewrite !comp_assoc.
  apply snake_left.
Qed.

(*
 Yanking with a spectator: inserting a cup beside a wire and capping it
 against the leading input is the identity on both wires. 

 --------
 与观察者拉扯：在一根电线上放置一个杯子并盖上它，对主输入两根电线都是恒等操作。
*)
Lemma spectator_snake :
  bend ∘ id[x] ⨂ (tensor_assoc ∘ cc_unit x ⨂ id[x] ∘ unit_left⁻¹)
    ≈ id[(x ⨂ x)%object].
Proof.
  unfold bend.
  rewrite !bimap_comp_id_left.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (tensor_assoc⁻¹) (id[x] ⨂ to tensor_assoc)).
  rewrite pentagon_step.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (tensor_assoc⁻¹) (id[x] ⨂ (cc_unit x ⨂ id[x]))).
  rewrite <- from_tensor_assoc_natural.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (tensor_assoc⁻¹) (id[x] ⨂ unit_left⁻¹)).
  rewrite tensor_assoc_from_unit_left.
  rewrite <- (@bimap_id_id C C C (@tensor C _) x x).
  rewrite <- (comp_assoc unit_left (cc_counit x ⨂ (id[x] ⨂ id[x]))
                (to tensor_assoc)).
  rewrite to_tensor_assoc_natural.
  rewrite !comp_assoc.
  normal.
  rewrite snake_left_from.
  rewrite <- triangle_identity_left.
  normal.
  rewrite iso_to_from.
  normal.
  reflexivity.
Qed.

(* The two-input closure: tensor a colour-grouped state next to the two inputs and cap each input in turn against the state's dual wires; the state's two x-wires are the outputs. / 双输入闭包：将一个按颜色分组的张量状态放在两个输入旁边，并依次将每个输入与状态的对偶线连接；状态的两条 x 线是输出。 *)
Definition close (v : I ~> ((d ⨂ d) ⨂ (x ⨂ x))%object) :
  (x ⨂ x)%object ~> (x ⨂ x)%object :=
  bend ∘ id[x] ⨂ (bend ∘ id[x] ⨂ (to tensor_assoc ∘ v) ∘ unit_right⁻¹).

#[local] Instance close_respects : Proper (equiv ==> equiv) close.
Proof.
  proper.
  unfold close.
  rewrites.
  reflexivity.
Qed.

(* A braid on the x-wires of the state emerges from the closure as a braid on its outputs. / 状态的 x 线上的一个编织从闭包中出现，作为其输出上的一个编织。 *)
Lemma close_braid (v : I ~> ((d ⨂ d) ⨂ (x ⨂ x))%object) :
  close (id[(d ⨂ d)%object] ⨂ braid ∘ v) ≈ braid ∘ close v.
Proof.
  unfold close.
  rewrite (comp_assoc (to tensor_assoc) (id[(d ⨂ d)%object] ⨂ braid) v).
  rewrite <- (@bimap_id_id C C C (@tensor C _) d d).
  rewrite <- to_tensor_assoc_natural.
  rewrite <- (comp_assoc (id[d] ⨂ (id[d] ⨂ braid)) (to tensor_assoc) v).
  rewrite (bimap_comp_id_left (id[d] ⨂ (id[d] ⨂ braid)) (to tensor_assoc ∘ v)).
  rewrite (comp_assoc bend (id[x] ⨂ (id[d] ⨂ (id[d] ⨂ braid)))).
  rewrite bend_natural.
  rewrite <- (comp_assoc (id[d] ⨂ braid) bend (id[x] ⨂ (to tensor_assoc ∘ v))).
  rewrite <- (comp_assoc (id[d] ⨂ braid)
                (bend ∘ id[x] ⨂ (to tensor_assoc ∘ v)) unit_right⁻¹).
  rewrite (bimap_comp_id_left (id[d] ⨂ braid)
             (bend ∘ id[x] ⨂ (to tensor_assoc ∘ v) ∘ unit_right⁻¹)).
  rewrite (comp_assoc bend (id[x] ⨂ (id[d] ⨂ braid))).
  rewrite bend_natural.
  rewrite <- comp_assoc.
  reflexivity.
Qed.

(* Double yanking: closing the colour-grouped two-cup state evaluates to the braiding — the first input caps the first cup and flows out on the second output, and conversely. / 双拉：关闭按颜色分组的双杯状态会得到编织——第一个输入封闭第一个杯子并从第二个输出流出，反之亦然。 *)
Lemma close_cups_mid : close cups_mid ≈ braid.
Proof.
  unfold close.
  rewrite cups_mid_nested.
  rewrite (bimap_comp_id_left
             (id[d] ⨂ (id[d] ⨂ braid ∘ tensor_assoc ∘ cc_unit x ⨂ id[x]
                         ∘ unit_left⁻¹))
             (cc_unit x)).
  rewrite (comp_assoc bend
             (id[x] ⨂ (id[d] ⨂ (id[d] ⨂ braid ∘ tensor_assoc
                                  ∘ cc_unit x ⨂ id[x] ∘ unit_left⁻¹)))).
  rewrite bend_natural.
  rewrite <- (comp_assoc _ bend (id[x] ⨂ cc_unit x)).
  rewrite <- (comp_assoc _ (bend ∘ id[x] ⨂ cc_unit x) unit_right⁻¹).
  rewrite bend_snake.
  rewrite id_right.
  rewrite <- !comp_assoc.
  rewrite (bimap_comp_id_left (id[d] ⨂ braid)
             (to tensor_assoc ∘ (cc_unit x ⨂ id[x] ∘ unit_left⁻¹))).
  rewrite comp_assoc.
  rewrite bend_natural.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to tensor_assoc) (cc_unit x ⨂ id[x]) (unit_left⁻¹)).
  rewrite spectator_snake.
  rewrite id_right.
  reflexivity.
Qed.

(*
 Abramsky's no-cloning theorem (arXiv:0910.2401, Theorem 11, second
 step): in a compact closed category with uniform copying, the braiding
 on every diagonal square is the identity.  The copied two-cup state is
 silently swap-invariant ([cups_mid_braid]); pushing the swap through
 the closure ([close_braid]) and evaluating ([close_cups_mid]) forces
 σ ≈ σ ∘ σ ≈ id. 

 --------
 Abramsky 的不可克隆定理（arXiv:0910.2401，第 11 定理，第二步）：在具有统一复制的紧闭范畴中，每个对角方格上的编织都是恒等映射。被复制的双杯态在静默下是交换不变的（[cups_mid_braid]）；将交换操作通过闭包（[close_braid]）并进行求值（[close_cups_mid]）会强制 σ ≈ σ ∘ σ ≈ id。
*)
Theorem no_cloning : @braid C _ x x ≈ id[(x ⨂ x)%object].
Proof using C CC R x.
  pose proof close_cups_mid as E1.
  assert (E2 : close cups_mid ≈ braid ∘ close cups_mid).
  { transitivity (close (id[(d ⨂ d)%object] ⨂ braid ∘ cups_mid)).
    - symmetry.
      now rewrite cups_mid_braid.
    - apply close_braid. }
  rewrite E1 in E2.
  rewrite braid_invol in E2.
  exact E2.
Qed.

End Cloning.

End NoCloning.
