Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(* * * Preservation of limits and colimits; reflection of isomorphisms / * * 保持极限和余极限；同构的反射 *)

(*
 nLab:      https://ncatlab.org/nlab/show/preserved+limit
 nLab:      https://ncatlab.org/nlab/show/continuous+functor
 nLab:      https://ncatlab.org/nlab/show/conservative+functor
 Mac Lane:  Categories for the Working Mathematician, 2nd ed. (GTM 5),
 §V.4 "Preservation of limits" (book p. 117), with Exercise 1
 Awodey:    Category Theory, 2nd ed., §5.5 (the canonical comparison map)
 and §5.6 Definition 5.31 (p. 119)
 Riehl:     Category Theory in Context, 2nd ed., §3.3 and §3.4
 Wikipedia:
 https://en.wikipedia.org/wiki/Limit_(category_theory)#Preservation_of_limits

 WHICH OF THE TWO READINGS IS THE DEFINITION.  Mac Lane's §V.4 says that a
 functor F preserves the limit of a diagram K when it carries a LIMITING
 CONE over K to a LIMITING CONE over F ◯ K: the image cone — apex F L,
 legs fmap[F] of the legs of L — must itself be universal.  That is
 [PreservesLimitCone] below, and it is what this file leads with.

 The class [PreservesLimit] records something visibly weaker: that the
 image APEX F L carries SOME limit structure of F ◯ K, whose legs are
 unconstrained and need not be the image legs.  The two notions are
 genuinely different.  [PreservesLimitCone_PreservesLimit] goes one way,
 and the converse is refuted by an explicit countermodel in
 Structure/Limit/Preservation/Separation.v: over the walking span
 (Instance/Roof.v), the functor sending both legs to the first projection
 of bool × bool satisfies [PreservesLimit] and provably not
 [PreservesLimitCone] — the image cone and the genuine product cone share
 an apex and differ by precomposition with the non-invertible
 [fun p => (fst p, fst p)].  The prose of Construction/Comma/Limit.v and
 its consumers asserted exactly this about apex-only preservation; it is
 now a theorem.

 CONTINUITY.  A functor is continuous when it preserves the limits of all
 diagrams of all shapes IN THE CONE SENSE: [ContinuousFunctor] below is
 [PreservesLimitCone] quantified over every shape and diagram, and that is
 what the word means in Mac Lane §V.4, Awodey §5.6 and Riehl §3.3.  The
 apex-only quantification [PreservesAllLimits] is kept, because
 Adjunction/Continuity.v and Theory/Equivalence/Limit.v export it, but it
 is a CONSEQUENCE — [Continuous_PreservesAllLimits] — and not the
 definition.  An earlier version of this header called it "continuous";
 that presentation was wrong and this paragraph is the correction.  The
 name [ContinuousFunctor] rather than [Continuous] avoids the clash with
 Instance/Top.v, exactly as [obj_eq_iso] avoids [iso_of_eq]
 (Structure/Limit/Creation.v).  [ContinuousFunctor] is also,
 definitionally, the hypothesis [PreservesImageLimit] that
 Construction/Comma/Limit.v introduced and that Adjunction/GAFT.v and
 Adjunction/SAFT.v consume; the two bridges are identity functions at
 Construction/Comma/Creation.v.

 THE CANONICAL COMPARISON MAP (Awodey §5.5).  Given a cone N over K and a
 limiting cone M over F ◯ K, the universal property of M sends the image
 cone to a unique [cone_comparison F N : F (lim K) ~> lim (F ◯ K)].
 Cone-level preservation is exactly invertibility of that map
 ([LimitCone_comparison_iso] and its converse [comparison_iso_LimitCone]),
 which pins down the sense in which apex-only preservation is weak: it
 yields SOME isomorphism F L ≅ lim (F ◯ K) ([apex_iso_of_PreservesLimit])
 and says nothing about the canonical one.

 Issue #427 asked for these under the names [PreservesConeLimit] and
 [PreservesConeColimit]; the tree's [PreservesLimitCone] and
 [PreservesColimitCocone] are those constants, with the words in the
 library's order.

 Quantification over a fixed shape and over an arbitrary class of shapes
 is here; finite shapes and the discrete (product) case are in
 Structure/Limit/Preservation/Shapes.v, which may import the named shape
 categories that this file must not.

 None of the classes below is registered for instance resolution:
 preservation witnesses are always passed explicitly. 

 --------
 nLab：       https://ncatlab.org/nlab/show/preserved+limit
 nLab：       https://ncatlab.org/nlab/show/continuous+functor
 nLab：       https://ncatlab.org/nlab/show/conservative+functor
 Mac Lane：  《为工作数学家而写的范畴论》，第2版（GTM 5），
 §V.4 “极限的保持”（书本第117页），附练习题1
 Awodey：    《范畴论》，第2版，§5.5（典型比较映射）
 和 §5.6 定义5.31（第119页）
 Riehl：     《语境中的范畴论》，第2版，§3.3 和 §3.4
 维基百科：
 https://en.wikipedia.org/wiki/Limit_(category_theory)#Preservation_of_limits

 哪一种读法是定义。Mac Lane §V.4 表明，当函子 F 将图 K 的极限锥映射为 F ◯ K 的极限锥时，它就保持图 K 的极限：像锥——顶点 F L，腿 fmap [F] L 的各条腿——本身必须是普遍的。也就是 [PreservesLimitCone] 以下内容，这也是此文件开头所讲的内容。类 [PreservesLimit] 记录了一些明显较弱的内容：即图像 APEX F L 具有 F ◯ K 的某些极限结构，其腿不受约束，也不必是图像腿。这两种概念实际上是不同的。[PreservesLimitCone_PreservesLimit] 适用于一种情况，而其逆命题已被 Structure/Limit/Preservation/Separation.v 中的一个明确反例所否定：在 walking span (Instance/Roof.v) 上，将两条腿都映射到 bool × bool 的第一投影的函子满足 [PreservesLimit] 并且可证明不满足 [PreservesLimitCone]——图像锥和真正的积锥共享一个顶点，并通过与不可逆的 [fun p => (fst p, fst p)] 前合成而不同。Construction/Comma/Limit.v 及其使用者的叙述正是断言了关于仅顶点保持的这一点；现在它已成为一个定理。连续性。当函子在锥体意义下保持所有形状的所有图的极限时，它是连续的：下面的 [ContinuousFunctor] 是对每种形状和图都进行量化的 [PreservesLimitCone]，这正是 Mac Lane §V.4、Awodey §5.6 和 Riehl §3.3 中所说的意思。仅顶点的量化 [PreservesAllLimits] 被保留，因为 Adjunction/Continuity.v 和 Theory/Equivalence/Limit.v 导出了它，但它是一个结果 — [Continuous_PreservesAllLimits] — 而不是定义。该标题的早期版本称其为“连续的”；那种表述是错误的，这段文字是修正。名称 [ContinuousFunctor] 而非 [Continuous] 避免了与 Instance/Top.v 的冲突，正如 [obj_eq_iso] 避免了 [iso_of_eq]（Structure/Limit/Creation.v）一样。[ContinuousFunctor] 在定义上也是 [PreservesImageLimit] 假设，即 Construction/Comma/Limit.v 引入的，并且 Adjunction/GAFT.v 和 Adjunction/SAFT.v 使用的；在 Construction/Comma/Creation.v，这两座桥都是恒等函数。

 典型的比较映射（Awodey §5.5）。给定一个关于 K 的锥 N 和一个关于 F ◯ K 的极限锥 M，M 的泛性质将影像锥映射到唯一的 [cone_comparison F N : F (lim K) ~> lim (F ◯ K)]。
 锥层面的保持正是该映射（[LimitCone_comparison_iso] 及其逆映射 [comparison_iso_LimitCone]）的可逆性，这确定了顶点仅保持在某种意义上的弱性：它产生某个同构 F L ≅ lim (F ◯ K) ([apex_iso_of_PreservesLimit])，但对典型同构没有任何说明。第427号问题要求这些以 [PreservesConeLimit] 和 [PreservesConeColimit] 命名；树的 [PreservesLimitCone] 和 [PreservesColimitCocone] 是那些常量，按库中的顺序排列单词。

 这里包含对固定形状和任意形状类的量化；有限形状和离散（乘积）情况在 Structure/Limit/Preservation/Shapes.v 中，该文件可能导入此文件绝不能导入的命名形状类别。

 下面的类没有一个是为实例解析注册的：保留证人总是显式传递。
*)

(** ** Preservation of limits / ** 限制的保留 *)

(*
 The APEX-ONLY class, kept for its downstream consumers: F preserves the
 limit of G when the image of any limit apex of G underlies SOME limit of
 F ◯ G, with the legs of that limit unrelated to the image legs.  The
 cone-level [PreservesLimitCone] is the definition proper, and
 Structure/Limit/Preservation/Separation.v shows this one does not imply
 it. The apex is written [F L]: since
 [limit_cone] is a class projection whose [Limit] argument is resolved by
 typeclass inference, it cannot be applied to the term [L] directly;
 instead [F L] elaborates through the coercion chain
 [Limit >-> Cone >-> vertex_obj], so the explicit spelling of the image
 apex is [F (@vertex_obj _ _ _ (@limit_cone _ _ _ L))]. 

 --------
 APEX-ONLY 类，保留给其下游使用者：F 保持 G 的极限，当 G 的任意极限顶点的像属于 F ◯ G 的某个极限时，该极限的支腿与像的支腿无关。锥层 [PreservesLimitCone] 是正式的定义，Structure/Limit/Preservation/Separation.v 表明这个定义并不意味着它。顶点记作 [F L]：由于 [limit_cone] 是一个类投影，其 [Limit] 参数通过类型类推断解决，因此不能直接应用于项 [L]；相反，[F L] 通过强制转换链 [Limit >-> Cone >-> vertex_obj] 进行展开，因此像顶点的显式拼写是 [F (@vertex_obj _ _ _ (@limit_cone _ _ _ L))]。
*)

Class PreservesLimit `(G : J ⟶ C) `(F : C ⟶ D) := {
  preserves_limit (L : Limit G) : IsALimit (F ◯ G) (F L)
}.

(* * ** Covariant accessors for apex-pinned limits / * ** 针对 apex 固定限制的协变访问器 *)

(*
 The leg of a cone N at x, as a first-class function (the notation
 [vertex_map[N]] leaves the diagram object as a hole, so it resists
 explicit application). 

 --------
 圆锥 N 在 x 处的边，作为一等函数（符号 [vertex_map[N] ] 将图形对象保留为空洞，因此它抗拒显式应用）。
*)

Definition cone_leg `{F : J ⟶ C} (N : Cone F) (x : J) :
  vertex_obj[N] ~{C}~> F x :=
  @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x.

(* The legs of a limit witness at a fixed apex c. / 位于固定顶点 c 的极限点的腿。 *)

Definition limit_leg `(H : @IsALimit J C F c) (x : J) : c ~{C}~> F x :=
  @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) x.

Lemma limit_leg_coherence `(H : @IsALimit J C F c) {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ limit_leg H x ≈ limit_leg H y.
Proof. exact (@cone_coherence _ _ _ _ (@limit_acone _ _ _ _ H) x y f). Qed.

(*
 The mediating morphism from a competing cone into the limit apex, and
 its defining properties. 

 --------
 从竞争锥到极限顶点的中介态射及其定义性质。
*)

Definition limit_med `(H : @IsALimit J C F c) (N : Cone F) :
  vertex_obj[N] ~{C}~> c :=
  unique_obj (@ump_limit _ _ _ _ H N).

Lemma limit_med_commutes `(H : @IsALimit J C F c) (N : Cone F) (x : J) :
  limit_leg H x ∘ limit_med H N ≈ cone_leg N x.
Proof. exact (unique_property (@ump_limit _ _ _ _ H N) x). Qed.

Lemma limit_med_unique `(H : @IsALimit J C F c) (N : Cone F)
  (v : vertex_obj[N] ~{C}~> c) :
  (∀ x : J, limit_leg H x ∘ v ≈ cone_leg N x) →
  limit_med H N ≈ v.
Proof. intro Hv. exact (uniqueness (@ump_limit _ _ _ _ H N) v Hv). Qed.

(*
 Two morphisms into the limit apex that agree on every leg are equal;
 useful for identifying mediators without naming [limit_med]. 

 --------
 两个指向极限顶点的态射，如果在每一条腿上都相同，则它们相等；有助于在不命名 [limit_med] 的情况下识别中介物。
*)

Lemma limit_med_eq `(H : @IsALimit J C F c) (N : Cone F)
  (u v : vertex_obj[N] ~{C}~> c) :
  (∀ x : J, limit_leg H x ∘ u ≈ cone_leg N x) →
  (∀ x : J, limit_leg H x ∘ v ≈ cone_leg N x) →
  u ≈ v.
Proof.
  intros Hu Hv.
  transitivity (limit_med H N).
  - symmetry. exact (limit_med_unique H N u Hu).
  - exact (limit_med_unique H N v Hv).
Qed.

(* A bundled limit, viewed as a limit witness pinned at its own apex. / 一个捆绑极限，被视为钉在自身顶点的极限见证。 *)

Definition limit_is_alimit `(L : @Limit J C G) : IsALimit G L :=
  @Build_IsALimit _ _ G _
    (@coneFrom _ _ _ (@limit_cone _ _ _ L))
    (@ump_limits _ _ _ L).

(* * ** The cone-level limit predicate / * ** 圆锥级别极限谓词 *)

(*
 [N] is a limiting cone: every cone over the same diagram factors through
 it uniquely, and the factorization is compatible with the legs OF N —
 which is what distinguishes this from the apex-pinned [IsALimit]. 

 --------
 [N] 是一个极限锥：每个在相同图上的锥都唯一地通过它进行分解，并且分解与 N 的支腿兼容——这正是将其与顶点固定的 [IsALimit] 区分开的地方。
*)

Definition IsLimitCone {J C : Category} {K : J ⟶ C} (N : Cone K) : Type :=
  ∀ M : Cone K, ∃! u : vertex_obj[M] ~{C}~> vertex_obj[N],
    ∀ x : J, cone_leg N x ∘ u ≈ cone_leg M x.

(*
 The four conversions against the existing classes are pure repackaging:
 every one is a term, with no proof obligation. 

 --------
 针对现有类的四种转换纯粹是重新包装：每一种都是一个术语，没有证明义务。
*)

Definition limitcone_isalimit {J C : Category} {K : J ⟶ C} {N : Cone K}
  (H : IsLimitCone N) : IsALimit K vertex_obj[N] :=
  @Build_IsALimit J C K vertex_obj[N] (@coneFrom _ _ _ N) H.

Definition isalimit_limitcone {J C : Category} {K : J ⟶ C} {c : C}
  (H : IsALimit K c) :
  @IsLimitCone J C K (@Build_Cone J C K c (@limit_acone _ _ _ _ H)) :=
  @ump_limit _ _ _ _ H.

Definition limit_limitcone {J C : Category} {K : J ⟶ C} (L : Limit K) :
  IsLimitCone (@limit_cone _ _ _ L) := @ump_limits _ _ _ L.

Definition limitcone_limit {J C : Category} {K : J ⟶ C} (N : Cone K)
  (H : IsLimitCone N) : Limit K := @Build_Limit J C K N H.

(** ** Isomorphism of cones / ** 圆锥的同构 *)

(*
 A cone isomorphism is an isomorphism of apexes commuting with the legs.
 It is [sigT], hence data: the comparison morphism can be projected and
 computed with. 

 --------
 锥体同构是顶点之间与腿部可交换的同构。它是 [sigT]，因此数据：比较态射可以被投影并计算。
*)

Definition ConeIso {J C : Category} {K : J ⟶ C} (N M : Cone K) : Type :=
  { i : vertex_obj[N] ≅ vertex_obj[M]
  & ∀ x : J, cone_leg M x ∘ to i ≈ cone_leg N x }.

Section ConeIsoLemmas.

Context {J C : Category}.
Context {K : J ⟶ C}.

Lemma coneiso_from {N M : Cone K} (i : ConeIso N M) (x : J) :
  cone_leg N x ∘ from `1 i ≈ cone_leg M x.
Proof.
  destruct i as [i Hi]; simpl.
  rewrite <- (Hi x).
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  now rewrite id_right.
Qed.

Definition ConeIso_sym {N M : Cone K} (i : ConeIso N M) : ConeIso M N :=
  (iso_sym `1 i; coneiso_from i).

Definition ConeIso_id (N : Cone K) : ConeIso N N.
Proof.
  exists iso_id.
  intro x; simpl; now rewrite id_right.
Defined.

Definition ConeIso_comp {N M P : Cone K}
  (j : ConeIso M P) (i : ConeIso N M) : ConeIso N P.
Proof.
  exists (iso_compose `1 j `1 i).
  intro x; simpl.
  rewrite comp_assoc.
  rewrite (`2 j x).
  exact (`2 i x).
Defined.

(* Limit-ness is invariant under isomorphism of cones. / 极限在锥体的同构下是不变的。 *)

Lemma limitcone_transport {N M : Cone K} (i : ConeIso N M)
  (HN : IsLimitCone N) : IsLimitCone M.
Proof.
  intro P.
  unshelve refine {| unique_obj := to `1 i ∘ unique_obj (HN P) |}.
  - intro x.
    rewrite comp_assoc.
    rewrite (`2 i x).
    exact (unique_property (HN P) x).
  - intros v Hv.
    assert (Hfv : ∀ x : J, cone_leg N x ∘ (from `1 i ∘ v) ≈ cone_leg P x).
    { intro x.
      rewrite comp_assoc.
      rewrite (coneiso_from i x).
      exact (Hv x). }
    rewrite (uniqueness (HN P) _ Hfv).
    rewrite comp_assoc.
    rewrite iso_to_from.
    now rewrite id_left.
Defined.

(*
 Uniqueness of limits, in the cone-level form: any two limiting cones over
 the same diagram are isomorphic by a leg-compatible isomorphism.  This is
 what makes the created lift unique up to canonical isomorphism below. 

 --------
 极限的唯一性，在锥层形式下：对于同一个图的任意两个极限锥，通过兼容锥脚的同构是同构的。这就是使下方构造的提升在典型同构下唯一的原因。
*)

Definition limitcone_iso {N M : Cone K}
  (HN : IsLimitCone N) (HM : IsLimitCone M) : ConeIso N M.
Proof.
  unshelve refine ((_; _)).
  - unshelve refine {| to := unique_obj (HM N); from := unique_obj (HN M) |}.
    + transitivity (unique_obj (HM M)).
      * symmetry.
        apply (uniqueness (HM M)).
        intro x.
        rewrite comp_assoc.
        rewrite (unique_property (HM N) x).
        exact (unique_property (HN M) x).
      * apply (uniqueness (HM M)).
        intro x; now rewrite id_right.
    + transitivity (unique_obj (HN N)).
      * symmetry.
        apply (uniqueness (HN N)).
        intro x.
        rewrite comp_assoc.
        rewrite (unique_property (HN M) x).
        exact (unique_property (HM N) x).
      * apply (uniqueness (HN N)).
        intro x; now rewrite id_right.
  - exact (unique_property (HM N)).
Defined.

End ConeIsoLemmas.

(* * ** The image of a cone under a functor / * ** 在函子下的锥的像 *)

Section ImageCone.

Context {J C D : Category}.
Context (F : C ⟶ D).
Context {K : J ⟶ C}.

(*
 The coherence of a cone, read through [cone_leg].  This duplicates
 [cone_leg_coherence] (Theory/Equivalence/Limit.v), which sits above
 this layer: importing it here would compile, but it would invert the
 layering. 

 --------
 锥体的一致性，通过 [cone_leg] 阅读。这会重复 [cone_leg_coherence]（Theory/Equivalence/Limit.v），它位于这一层之上：在此导入它可以编译，但会颠倒层次结构。
*)

Lemma cone_leg_coh (N : Cone K) {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ cone_leg N x ≈ cone_leg N y.
Proof. exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f). Qed.

Definition fcone_leg (N : Cone K) (x : J) :
  F (vertex_obj[N]) ~{D}~> (F ◯ K) x := fmap[F] (cone_leg N x).

Lemma fcone_coherence (N : Cone K) {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ K] f ∘ fcone_leg N x ≈ fcone_leg N y.
Proof.
  unfold fcone_leg; simpl.
  rewrite <- fmap_comp.
  now rewrite (cone_leg_coh N f).
Qed.

Definition FCone (N : Cone K) : Cone (F ◯ K) :=
  @Build_Cone J D (F ◯ K) (F (vertex_obj[N]))
    (@Build_ACone J D (F (vertex_obj[N])) (F ◯ K) (fcone_leg N)
       (fun x y f => fcone_coherence N f)).

(*
 The legs of [FCone N] ARE the image legs, definitionally; this is what
 discharges the leg side conditions of the reflection lemmas downstream. 

 --------
 [FCone N] 的腿从定义上来说就是图像的腿；这就是释放反射引理下游的腿侧条件的原因。
*)

Lemma FCone_leg (N : Cone K) (x : J) :
  cone_leg (FCone N) x ≈ fmap[F] (cone_leg N x).
Proof. reflexivity. Qed.

Definition FCone_iso {N M : Cone K} (i : ConeIso N M) :
  ConeIso (FCone N) (FCone M).
Proof.
  exists (fobj_iso F _ _ `1 i).
  intro x; simpl.
  change (fmap[F] (cone_leg M x) ∘ fmap[F] (to `1 i) ≈ fmap[F] (cone_leg N x)).
  rewrite <- fmap_comp.
  now rewrite (`2 i x).
Defined.

End ImageCone.

(* * ** Cone-level preservation and reflection / * **锥体水平的保存与反射 *)

Definition PreservesLimitCone {J C D : Category} (K : J ⟶ C) (F : C ⟶ D)
  : Type := ∀ N : Cone K, IsLimitCone N → IsLimitCone (FCone F N).

Definition ReflectsLimitCone {J C D : Category} (K : J ⟶ C) (F : C ⟶ D)
  : Type := ∀ N : Cone K, IsLimitCone (FCone F N) → IsLimitCone N.

(*
 The cone-level notion is stronger than the apex-only class of
 Structure/Limit/Preservation.v; this is the bridge, and only this
 direction holds (the argument at Construction/Comma/Limit.v is
 precisely that the converse does not go through). 

 --------
 锥体级概念比仅顶点类的 Structure/Limit/Preservation.v 更强；这是桥接，而且仅此方向成立（Construction/Comma/Limit.v 中的论证正是说明其逆向不可行）。
*)

Definition PreservesLimitCone_PreservesLimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (P : PreservesLimitCone K F) : PreservesLimit K F.
Proof.
  constructor.
  intro L.
  exact (limitcone_isalimit (P (@limit_cone _ _ _ L) (limit_limitcone L))).
Defined.

(* * ** The canonical comparison map [F (lim K) ~> lim (F ◯ K)] (Awodey §5.5) / * ** 规范比较映射 [F (lim K) ~> lim (F ◯ K)]（Awodey §5.5） *)

Section Comparison.

Context {J C D : Category}.
Context {K : J ⟶ C}.
Context (F : C ⟶ D).

Definition cone_comparison (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) :
  F (vertex_obj[N]) ~{D}~> vertex_obj[M] :=
  unique_obj (HM (FCone F N)).

Lemma cone_comparison_commutes (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) (x : J) :
  cone_leg M x ∘ cone_comparison N HM ≈ fmap[F] (cone_leg N x).
Proof. exact (unique_property (HM (FCone F N)) x). Qed.

Lemma cone_comparison_unique (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) (v : F (vertex_obj[N]) ~{D}~> vertex_obj[M]) :
  (∀ x : J, cone_leg M x ∘ v ≈ fmap[F] (cone_leg N x)) →
  cone_comparison N HM ≈ v.
Proof. intro Hv. exact (uniqueness (HM (FCone F N)) v Hv). Qed.

(* Cone-level preservation IS invertibility of the comparison, both ways. / 圆锥级保留是比较的可逆性，双向的。 *)

Definition LimitCone_comparison_iso (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) (HN : IsLimitCone (FCone F N)) :
  IsIsomorphism (cone_comparison N HM) :=
  {| two_sided_inverse := from `1 (limitcone_iso HN HM);
     is_right_inverse  := iso_to_from `1 (limitcone_iso HN HM);
     is_left_inverse   := iso_from_to `1 (limitcone_iso HN HM) |}.

Definition comparison_iso_LimitCone (N : Cone K) {M : Cone (F ◯ K)}
  (HM : IsLimitCone M) (Hi : IsIsomorphism (cone_comparison N HM)) :
  IsLimitCone (FCone F N).
Proof.
  assert (ci : ConeIso (FCone F N) M).
  { exists (IsIsoToIso _ Hi).
    intro x; exact (cone_comparison_commutes N HM x). }
  exact (limitcone_transport (ConeIso_sym ci) HM).
Defined.

Definition PreservesLimitCone_of_comparison {M : Cone (F ◯ K)}
  (HM : IsLimitCone M)
  (H : ∀ N : Cone K, IsLimitCone N → IsIsomorphism (cone_comparison N HM)) :
  PreservesLimitCone K F :=
  fun N HN => comparison_iso_LimitCone N HM (H N HN).

Definition comparison_iso_of_PreservesLimitCone
  (P : PreservesLimitCone K F) {M : Cone (F ◯ K)} (HM : IsLimitCone M)
  (N : Cone K) (HN : IsLimitCone N) :
  IsIsomorphism (cone_comparison N HM) :=
  LimitCone_comparison_iso N HM (P N HN).

(*
 The apex-only class produces SOME isomorphism between the image apex and
 the limit apex, with no claim that it is the canonical comparison; the
 Separation development exhibits the isomorphism existing while the
 comparison is provably not invertible. 

 --------
 仅顶点类在图像顶点和极限顶点之间产生某种同构，但并不声称这是规范比较；分离发展展示了同构的存在，而该比较可证明不可逆。
*)

Definition apex_iso_of_PreservesLimit (P : PreservesLimit K F) (L : Limit K)
  {M : Cone (F ◯ K)} (HM : IsLimitCone M) :
  F (vertex_obj[L]) ≅ vertex_obj[M] :=
  `1 (limitcone_iso (isalimit_limitcone (preserves_limit L)) HM).

(* The bundled reading, for chosen limits (Awodey's F (lim D) → lim (F D)). / 捆绑的读法，对于选定的极限（Awodey 的 F (lim D) → lim (F D)）。 *)

Definition limit_comparison (L : Limit K) (M : Limit (F ◯ K)) :
  F (vertex_obj[L]) ~{D}~> vertex_obj[M] :=
  cone_comparison (@limit_cone _ _ _ L) (limit_limitcone M).

End Comparison.



(* * ** Repackagings across functor-composition associativity and op / * ** 跨函子组合结合性和对偶的重新打包 *)

Section ConeAssoc.

Context {J C D E : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.
Context {G : D ⟶ E}.

(* [(G ◯ F) ◯ K] and [G ◯ (F ◯ K)] have the same cones, but the two record types are not convertible, so the repackaging is field by field. / [(G ◯ F) ◯ K] 和 [G ◯ (F ◯ K)] 拥有相同的锥体，但这两种记录类型不可互换，所以重新打包是逐字段进行的。 *)

Definition cone_assoc (N : Cone ((G ◯ F) ◯ K)) : Cone (G ◯ (F ◯ K)) :=
  @Build_Cone J E (G ◯ (F ◯ K)) (@vertex_obj _ _ _ N)
    (@Build_ACone J E (@vertex_obj _ _ _ N) (G ◯ (F ◯ K))
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition cone_assoc_inv (N : Cone (G ◯ (F ◯ K))) : Cone ((G ◯ F) ◯ K) :=
  @Build_Cone J E ((G ◯ F) ◯ K) (@vertex_obj _ _ _ N)
    (@Build_ACone J E (@vertex_obj _ _ _ N) ((G ◯ F) ◯ K)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition islimitcone_assoc {N : Cone ((G ◯ F) ◯ K)} (H : IsLimitCone N) :
  IsLimitCone (cone_assoc N) := fun M => H (cone_assoc_inv M).

Definition islimitcone_assoc_inv {N : Cone (G ◯ (F ◯ K))}
  (H : IsLimitCone N) : IsLimitCone (cone_assoc_inv N) :=
  fun M => H (cone_assoc M).

End ConeAssoc.

(*
 A cone over [K] read as a cone over [Id ◯ K]: the same apex and legs,
 [Id ◯ K] not being [K] on the nose.  Added by #477 for
 Structure/Limit/Absolute.v's "an absolute limit is a limit", with that
 file's binders: one hom level for the shape and the ambient. 

 --------
 一个关于  [K] 的锥体 读作 一个关于  [Id ◯ K] 的锥体：相同的顶点和边，[Id ◯ K] 并不是 [K] 精确相同的部分。由 #477 添加用于 Structure/Limit/Absolute.v 的“一个绝对极限就是一个极限”，以及该文件的绑定器：形状的一个同伦层级和环境的同伦层级。
*)

Definition cone_id_comp@{jo co ch +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}} {K : J ⟶ C}
  (M : Cone K) : Cone (Id ◯ K) :=
  @Build_Cone J C (Id ◯ K) (@vertex_obj _ _ _ M)
    (@Build_ACone J C (@vertex_obj _ _ _ M) (Id ◯ K)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ M) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f)).

(*
 Mac Lane §V.4 Exercise 1, per diagram: the image under G of an
 already-limiting image cone is limiting, so preservation composes. 

 --------
 Mac Lane §V.4 练习 1，根据图示：一个已经是极限的像锥在 G 下的像仍然是极限，所以保持性可组合。
*)
Definition PreservesLimitCone_compose {J C D E : Category}
  {K : J ⟶ C} {F : C ⟶ D} {G : D ⟶ E}
  (PF : PreservesLimitCone K F) (PG : PreservesLimitCone (F ◯ K) G) :
  PreservesLimitCone K (G ◯ F).
Proof.
  intros N HN M.
  exact (PG (FCone F N) (PF N HN) (cone_assoc M)).
Defined.

Section OpComp.

Context {J C D : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.

Definition cone_op_comp (N : Cone ((F ◯ K)^op)) : Cone (F^op ◯ K^op) :=
  @Build_Cone (J^op) (D^op) (F^op ◯ K^op) (@vertex_obj _ _ _ N)
    (@Build_ACone (J^op) (D^op) (@vertex_obj _ _ _ N) (F^op ◯ K^op)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition cone_op_comp_inv (N : Cone (F^op ◯ K^op)) : Cone ((F ◯ K)^op) :=
  @Build_Cone (J^op) (D^op) ((F ◯ K)^op) (@vertex_obj _ _ _ N)
    (@Build_ACone (J^op) (D^op) (@vertex_obj _ _ _ N) ((F ◯ K)^op)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition islimitcone_op_comp {N : Cone ((F ◯ K)^op)} (H : IsLimitCone N) :
  IsLimitCone (cone_op_comp N) := fun M => H (cone_op_comp_inv M).

End OpComp.

(*
 (F ◯ G)^op and F^op ◯ G^op share their object and morphism maps but
 differ in the proofs of functoriality, so an apex-pinned limit witness
 over the one repackages field by field as a witness over the other
 (the [preserves_colimit] precedent in Structure/Limit/Preservation.v).
 No destructuring: everything is spelled with projections, so the
 result stays convertible with the input on legs and mediators. 

 --------
 (F ◯ G)^op 和 F^op ◯ G^op 共享它们的对象映射和态射映射，但在函子性证明上有所不同，因此，一个顶点固定的极限见证可以通过逐字段打包成另一个的见证（参见 Structure/Limit/Preservation.v 中的 [preserves_colimit] 前例）。不要解构：一切都用投影拼写，因此结果在腿和中介上与输入保持可转换。
*)

Definition isalimit_op_comp {J C D : Category} {G : J ⟶ C} {F : C ⟶ D}
  {c : D} (H : IsALimit ((F ◯ G)^op) c) : IsALimit (F^op ◯ G^op) c :=
  @Build_IsALimit (J^op) (D^op) (F^op ◯ G^op) c
    (@Build_ACone (J^op) (D^op) c (F^op ◯ G^op)
       (fun x => @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) x)
       (fun x y f =>
          @cone_coherence _ _ _ _ (@limit_acone _ _ _ _ H) x y f))
    (fun N =>
       @ump_limit _ _ _ _ H
         (@Build_Cone (J^op) (D^op) ((F ◯ G)^op) (@vertex_obj _ _ _ N)
            (@Build_ACone (J^op) (D^op) (@vertex_obj _ _ _ N) ((F ◯ G)^op)
               (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
               (fun x y f =>
                  @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)))).


(* * ** Covariant accessors for cocones and apex-pinned colimits / * ** 协变取值器用于余锥和顶点固定的余极限 *)

(*
 A cocone over F is a cone over F^op (Structure/Cone.v); its legs run
 from the diagram into the apex. [cocone_inj] re-reads those legs
 covariantly, as injections F x ~> N in C. 

 --------
 F 的余锥是 F^op 上的锥（Structure/Cone.v）；它的边从图流向顶点。[cocone_inj] 以协变的方式重新读取这些边，作为 C 中的单射 F x ~> N。
*)

Definition cocone_inj `{F : J ⟶ C} (N : Cocone F) (x : J) :
  F x ~{C}~> vertex_obj[N] :=
  @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x.

Lemma cocone_inj_coherence `{F : J ⟶ C} (N : Cocone F)
  {x y : J} (f : x ~{J}~> y) :
  cocone_inj N y ∘ fmap[F] f ≈ cocone_inj N x.
Proof. exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) y x f). Qed.

(*
 [IsAColimit F c] pins the apex of a colimit of F at c, dually to
 [IsALimit]: it is [IsALimit] for the opposite diagram, at the same
 object. The accessors below restate its legs and universal property
 covariantly, entirely in terms of C. 

 --------
 [IsAColimit F c] 将 F 的余极限的顶点固定在 c 上，与 [IsALimit] 对偶：它是相反图的 [IsALimit]，在同一个对象上。下面的访问器以协变方式重新表述它的各条腿和普遍性性质，完全用 C 来表示。
*)

Definition IsAColimit `(F : J ⟶ C) (c : C) : Type := IsALimit (F^op) c.

(* The injections of the colimit: the legs of the underlying opposite cone, read in C. / 余极限的单射：底层对偶锥的腿，在 C 中读取。 *)

Definition colimit_inj `(H : @IsAColimit J C F c) (x : J) : F x ~{C}~> c :=
  @vertex_map _ _ _ _ (@limit_acone _ _ _ _ H) x.

Lemma colimit_inj_coherence `(H : @IsAColimit J C F c) {x y : J}
  (f : x ~{J}~> y) :
  colimit_inj H y ∘ fmap[F] f ≈ colimit_inj H x.
Proof. exact (@cone_coherence _ _ _ _ (@limit_acone _ _ _ _ H) y x f). Qed.

(*
 Universal property, covariantly: every cocone N over F factors through
 the colimit apex by a unique mediating morphism out of c. Transparent,
 so downstream constructions can extract the mediator. 

 --------
 泛性质，共变：每个 F 上的余锥 N 都通过余极点由唯一的中介态射 c 分解。透明，因此下游构造可以提取中介者。
*)

Definition ump_colimit `(H : @IsAColimit J C F c) (N : Cocone F) :
  ∃! u : c ~{C}~> vertex_obj[N],
    ∀ x : J, u ∘ colimit_inj H x ≈ cocone_inj N x.
Proof. exact (@ump_limit _ _ _ _ H N). Defined.

Definition colimit_med `(H : @IsAColimit J C F c) (N : Cocone F) :
  c ~{C}~> vertex_obj[N] :=
  unique_obj (ump_colimit H N).

Lemma colimit_med_commutes `(H : @IsAColimit J C F c) (N : Cocone F) (x : J) :
  colimit_med H N ∘ colimit_inj H x ≈ cocone_inj N x.
Proof. exact (unique_property (ump_colimit H N) x). Qed.

Lemma colimit_med_unique `(H : @IsAColimit J C F c) (N : Cocone F)
  (v : c ~{C}~> vertex_obj[N]) :
  (∀ x : J, v ∘ colimit_inj H x ≈ cocone_inj N x) →
  colimit_med H N ≈ v.
Proof. intro Hv. exact (uniqueness (ump_colimit H N) v Hv). Qed.

Lemma colimit_med_eq `(H : @IsAColimit J C F c) (N : Cocone F)
  (u v : c ~{C}~> vertex_obj[N]) :
  (∀ x : J, u ∘ colimit_inj H x ≈ cocone_inj N x) →
  (∀ x : J, v ∘ colimit_inj H x ≈ cocone_inj N x) →
  u ≈ v.
Proof.
  intros Hu Hv.
  transitivity (colimit_med H N).
  - symmetry. exact (colimit_med_unique H N u Hu).
  - exact (colimit_med_unique H N v Hv).
Qed.

(*
 The apex of a bundled colimit, read as an object of C, and the bundled
 colimit viewed as a colimit witness pinned at that apex. 

 --------
 捆绑余极限的顶点，被视为 C 的一个对象，以及作为固定在该顶点的余极限见证的捆绑余极限。
*)

Definition colimit_apex `(L : @Colimit J C G) : C :=
  @vertex_obj _ _ _ (@limit_cone _ _ _ L).

Definition colimit_is_acolimit `(L : @Colimit J C G) :
  IsAColimit G (colimit_apex L) :=
  @Build_IsALimit _ _ (G^op) _
    (@coneFrom _ _ _ (@limit_cone _ _ _ L))
    (@ump_limits _ _ _ L).

(** ** Preservation of colimits / ** 共极限的保持 *)

(*
 F preserves the colimit of G exactly when F^op preserves the limit of
 the opposite diagram G^op; this is the one-line dual definition, in the
 style of [Colimit] itself. 

 --------
 当且仅当 F^op 保留对偶图 G^op 的极限时，F 精确地保留 G 的余极限；这是一个一行的对偶定义，采用 [Colimit] 本身的风格。
*)

Definition PreservesColimit `(G : J ⟶ C) `(F : C ⟶ D) : Type :=
  @PreservesLimit (J^op) (C^op) (G^op) (D^op) (F^op).

(*
 Covariant accessor: a colimit-preservation witness sends the apex of
 any colimit of G to the apex of a colimit of F ◯ G. The functors
 (F ◯ G)^op and F^op ◯ G^op share their object and morphism maps up to
 conversion, differing only in the proofs of functoriality, so the
 witness produced by [preserves_limit] is repackaged field by field. 

 --------
 协变访问器：一个余极限保持证人将 G 的任意余极限的顶点发送到 F ◯ G 的余极限的顶点。函子 (F ◯ G)^op 和 F^op ◯ G^op 在对象和态射映射上达成一致，仅在函子性证明上有所不同，因此 [preserves_limit] 生成的证人按字段重新打包。
*)

Definition preserves_colimit {J C D : Category} {G : J ⟶ C} {F : C ⟶ D}
  (P : PreservesColimit G F) (L : Colimit G) :
  IsAColimit (F ◯ G) (F (colimit_apex L)).
Proof.
  destruct (@preserves_limit _ _ _ _ _ P L) as [ac um].
  unshelve refine (@Build_IsALimit _ _ ((F ◯ G)^op) _ _ _).
  - exact (@Build_ACone _ _ _ ((F ◯ G)^op)
      (fun x => @vertex_map _ _ _ _ ac x)
      (fun x y f => @cone_coherence _ _ _ _ ac x y f)).
  - intro N.
    exact (um (@Build_Cone _ _ (F^op ◯ G^op)
      (@vertex_obj _ _ _ N)
      (@Build_ACone _ _ _ (F^op ◯ G^op)
         (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
         (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)))).
Defined.

(** ** Continuity and cocontinuity / ** 连续性与共连续性 *)

(*
 A functor preserving the limits of all diagrams of all shapes
 (continuous), respectively all colimits (cocontinuous). These are plain
 Definitions: preservation of a class of limits is data to be supplied,
 never inferred. 

 --------
 一个保持所有形状的所有图的极限的函子（连续的），以及保持所有余极限的函子（余连续的）。这些是简单的定义：保持一类极限是需要提供的数据，从不进行推断。
*)

Definition PreservesAllLimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (G : J ⟶ C), PreservesLimit G F.

Definition PreservesAllColimits {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (G : J ⟶ C), PreservesColimit G F.

(* * ** Continuity, cocontinuity, and quantification over shapes / * ** 连续性、协连续性以及对形状的量化 *)

(*
 Continuity is preservation of every limit of every shape in the CONE
 sense (Mac Lane §V.4); [Continuous_PreservesAllLimits] descends to the
 apex-only quantification, and the countermodel of
 Structure/Limit/Preservation/Separation.v shows the descent has no
 inverse.  These are plain Definitions: preservation of a class of limits
 is data to be supplied, never inferred. 

 --------
 连续性是在圆锥意义下（Mac Lane §V.4）对每个形状的每个极限的保持；[Continuous_PreservesAllLimits] 能下降到仅顶点的量化，并且 Structure/Limit/Preservation/Separation.v 的反例显示该下降没有逆。 这些都是明确定义：对一类极限的保持是需要提供的数据，从不推断。
*)

Definition ContinuousFunctor {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), PreservesLimitCone K F.

Definition Continuous_PreservesAllLimits {C D : Category} {F : C ⟶ D}
  (H : ContinuousFunctor F) : PreservesAllLimits F :=
  fun J K => PreservesLimitCone_PreservesLimit (H J K).

(*
 Riehl §3.4: preservation over all diagrams of a given shape, and over an
 arbitrary class of shapes. 

 --------
 Riehl §3.4：对给定形状的所有图表的保持，以及对任意形状类的保持。
*)

Definition PreservesLimitConesOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, PreservesLimitCone K F.

Definition PreservesLimitConesOver {C D : Category} (S : Category → Type)
  (F : C ⟶ D) : Type :=
  ∀ J : Category, S J → ∀ K : J ⟶ C, PreservesLimitCone K F.

Definition Continuous_PreservesLimitConesOver {C D : Category}
  {S : Category → Type} {F : C ⟶ D} (H : ContinuousFunctor F) :
  PreservesLimitConesOver S F := fun J _ K => H J K.

Definition Continuous_OfShape {C D : Category} {F : C ⟶ D}
  (H : ContinuousFunctor F) (J : Category) :
  PreservesLimitConesOfShape J F := H J.

(* Mac Lane §V.4 Exercise 1 at full strength. / Mac Lane §V.4 练习1 完全用力做。 *)

Definition continuous_compose {C D E : Category} {F : C ⟶ D} {G : D ⟶ E}
  (PF : ContinuousFunctor F) (PG : ContinuousFunctor G) :
  ContinuousFunctor (G ◯ F) :=
  fun J K => PreservesLimitCone_compose (PF J K) (PG J (F ◯ K)).

(** ** Reflection of isomorphisms / **同构的反射 *)

(*
 A conservative functor: any morphism whose image under F is invertible
 is itself invertible. Stated with the two-sided-inverse predicate
 [IsIsomorphism] (Theory/Isomorphism.v). Fully faithful functors are the
 standard source of such witnesses (Phase consumers derive them there);
 none is registered here. 

 --------
 保守函子：任何在 F 下的像是可逆的态射本身也是可逆的。用双向逆谓词 [IsIsomorphism]（Theory/Isomorphism.v）表示。完全忠实的函子是这种证人（witnesses）的标准来源（阶段消费者在那里派生它们）；这里没有注册任何一个。
*)

Class ReflectsIsos {C D : Category} (F : C ⟶ D) := {
  reflects_iso {x y : C} (f : x ~> y) :
    IsIsomorphism (fmap[F] f) → IsIsomorphism f
}.

(* * ** The cocone-level colimit predicate, preservation, and cocontinuity / * ** 余圆锥水平余极限谓词、保持性和余连续性 *)

(*
 [IsColimitCocone] is [IsLimitCone] for the opposite diagram at the same
 cocone; unfolded in C it says every cocone over K receives a unique
 mediator out of N compatible with the injections. 

 --------
 [IsColimitCocone] 对于相同的余锥在相反图中就是 [IsLimitCone]；在 C 中展开，它表示每个 K 上的余锥都接收一个来自 N 的独特中介，该中介与注入兼容。
*)

Definition IsColimitCocone {J C : Category} {K : J ⟶ C} (N : Cocone K) : Type :=
  @IsLimitCone (J^op) (C^op) (K^op) N.

Definition colimitcocone_ump {J C : Category} {K : J ⟶ C} {N : Cocone K}
  (H : IsColimitCocone N) (M : Cocone K) :
  ∃! u : vertex_obj[N] ~{C}~> vertex_obj[M],
    ∀ x : J, u ∘ cocone_inj N x ≈ cocone_inj M x := H M.

Definition colimitcocone_isacolimit {J C : Category} {K : J ⟶ C}
  {N : Cocone K} (H : IsColimitCocone N) : IsAColimit K vertex_obj[N] :=
  limitcone_isalimit H.

Definition colimit_colimitcocone {J C : Category} {K : J ⟶ C}
  (L : Colimit K) : IsColimitCocone (@limit_cone _ _ _ L) :=
  @ump_limits _ _ _ L.

Section ImageCocone.

Context {J C D : Category}.
Context (F : C ⟶ D).
Context {K : J ⟶ C}.

Definition fcocone_inj (N : Cocone K) (x : J) :
  (F ◯ K) x ~{D}~> F (vertex_obj[N]) := fmap[F] (cocone_inj N x).

Lemma fcocone_coherence (N : Cocone K) {x y : J} (f : x ~{J}~> y) :
  fcocone_inj N y ∘ fmap[F ◯ K] f ≈ fcocone_inj N x.
Proof.
  unfold fcocone_inj; simpl.
  rewrite <- fmap_comp.
  now rewrite (cocone_inj_coherence N f).
Qed.

Definition FCocone (N : Cocone K) : Cocone (F ◯ K).
Proof.
  unshelve refine (@Build_Cone (J^op) (D^op) ((F ◯ K)^op)
                     (F (vertex_obj[N])) _).
  unshelve refine (@Build_ACone (J^op) (D^op) (F (vertex_obj[N]))
                     ((F ◯ K)^op) (fcocone_inj N) _).
  intros x y f; exact (fcocone_coherence N f).
Defined.

Lemma FCocone_inj (N : Cocone K) (x : J) :
  cocone_inj (FCocone N) x ≈ fmap[F] (cocone_inj N x).
Proof. reflexivity. Qed.

Definition cocone_comparison (N : Cocone K) {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) :
  vertex_obj[M] ~{D}~> F (vertex_obj[N]) :=
  unique_obj (HM (FCocone N)).

End ImageCocone.

(*
 The cocone twin of [FCone_iso]: the image of a cocone isomorphism is
 one.  Added by #477, the tree having had no cocone twin, with
 Structure/Limit/Absolute.v's binders. 

 --------
 [FCone_iso] 的余锥双胞胎：余锥同构的像是一个。由 #477 添加，该树之前没有余锥双胞胎，带有 Structure/Limit/Absolute.v 的绑定器。
*)

Definition FCocone_iso@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}}
  {D : Category@{do ch ch}} (F : C ⟶ D) {K : J ⟶ C} {N M : Cocone K}
  (i : ConeIso N M) : ConeIso (FCocone F N) (FCocone F M).
Proof.
  exists (fobj_iso (F^op) _ _ `1 i).
  intro x.
  change (fmap[F] (to `1 i) ∘ fmap[F] (cocone_inj M x)
            ≈ fmap[F] (cocone_inj N x)).
  rewrite <- fmap_comp.
  apply fmap_respects.
  exact (`2 i x).
Defined.

Definition PreservesColimitCocone {J C D : Category}
  (K : J ⟶ C) (F : C ⟶ D) : Type :=
  ∀ N : Cocone K, IsColimitCocone N → IsColimitCocone (FCocone F N).

Definition ReflectsColimitCocone {J C D : Category}
  (K : J ⟶ C) (F : C ⟶ D) : Type :=
  ∀ N : Cocone K, IsColimitCocone (FCocone F N) → IsColimitCocone N.

Definition PreservesColimitCocone_PreservesColimit {J C D : Category}
  {K : J ⟶ C} {F : C ⟶ D} (P : PreservesColimitCocone K F) :
  PreservesColimit K F.
Proof.
  constructor.
  intro L.
  exact (isalimit_op_comp
           (limitcone_isalimit
              (P (@limit_cone _ _ _ L) (limit_limitcone L)))).
Defined.

Section CoCompose.

Context {J C D E : Category}.
Context {K : J ⟶ C}.
Context {F : C ⟶ D}.
Context {G : D ⟶ E}.

Definition cocone_assoc (N : Cocone ((G ◯ F) ◯ K)) : Cocone (G ◯ (F ◯ K)) :=
  @Build_Cone (J^op) (E^op) ((G ◯ (F ◯ K))^op) (@vertex_obj _ _ _ N)
    (@Build_ACone (J^op) (E^op) (@vertex_obj _ _ _ N) ((G ◯ (F ◯ K))^op)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition PreservesColimitCocone_compose
  (PF : PreservesColimitCocone K F) (PG : PreservesColimitCocone (F ◯ K) G) :
  PreservesColimitCocone K (G ◯ F).
Proof.
  intros N HN M.
  exact (PG (FCocone F N) (PF N HN) (cocone_assoc M)).
Defined.

End CoCompose.

(* The cocone twin of [cone_assoc_inv], and the inverse repackaging of [cocone_assoc]. Added by #477, with Structure/Limit/Absolute.v's binders. / [cone_assoc_inv] 的 cocone 双胞，以及 [cocone_assoc] 的逆重打包。由 #477 添加，包含 Structure/Limit/Absolute.v 的绑定器。 *)

Definition cocone_assoc_inv@{jo co ch do eo +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}}
  {D : Category@{do ch ch}} {E : Category@{eo ch ch}}
  {K : J ⟶ C} {F : C ⟶ D} {G : D ⟶ E}
  (N : Cocone (G ◯ (F ◯ K))) : Cocone ((G ◯ F) ◯ K) :=
  @Build_Cone (J^op) (E^op) (((G ◯ F) ◯ K)^op) (@vertex_obj _ _ _ N)
    (@Build_ACone (J^op) (E^op) (@vertex_obj _ _ _ N) (((G ◯ F) ◯ K)^op)
       (fun x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) x)
       (fun x y f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)).

Definition CocontinuousFunctor {C D : Category} (F : C ⟶ D) : Type :=
  ∀ (J : Category) (K : J ⟶ C), PreservesColimitCocone K F.

Definition Cocontinuous_PreservesAllColimits {C D : Category} {F : C ⟶ D}
  (H : CocontinuousFunctor F) : PreservesAllColimits F :=
  fun J K => PreservesColimitCocone_PreservesColimit (H J K).

Definition PreservesColimitCoconesOfShape (J : Category) {C D : Category}
  (F : C ⟶ D) : Type := ∀ K : J ⟶ C, PreservesColimitCocone K F.

Definition cocontinuous_compose {C D E : Category} {F : C ⟶ D} {G : D ⟶ E}
  (PF : CocontinuousFunctor F) (PG : CocontinuousFunctor G) :
  CocontinuousFunctor (G ◯ F) :=
  fun J K => PreservesColimitCocone_compose (PF J K) (PG J (F ◯ K)).
