(*
   * * Partial orders are a full reflective subcategory of all preorders

   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Springer GTM 5, §IV.3, printed p. 92, Exercise 4.  Read from the
   page image: "4. Show the following subcategories to be
   reflective: (a) The full subcategory of all partial orders in
   the category Preord of all preorders, with arrows all monotone
   functions.  (b) The full subcategory of T_0-spaces in Top."
   Catalog id: maclane:IV.3:ex4.  This file is half (a); half (b)
   is Instance/Top/Kolmogorov.v, written in parallel.

   ** What is delivered

   [Poset_Reflective_in_Ord : Reflective Pos_Sub] -- the record of
   Construction/Reflective.v, whose three fields are exactly the three
   things Mac Lane's phrase names: FULLNESS of the subcategory
   ([Pos_Sub_Full], Instance/Ord.v), a REFLECTOR ([Poset_reflector]), and
   the ADJUNCTION ([Poset_adj]) making it left adjoint to the inclusion.
   Read the packaging precisely: the adjunction ALONE is strictly less
   than the record, and that mismatch is this development's typing
   rejection.

   Around it: the poset reflection [PosetReflection] with
   [PosetReflection_Antisymmetric], its packaging [PosetReflectionObj],
   the projection [reflection_proj], the mediator [poset_med], the
   universal property [poset_reflection_universal] and its arrow
   [poset_reflection_universal_arrow], the counit corollary
   [poset_reflect_iso] -- for a partial order P, the reflection of P is
   isomorphic to P -- instantiated at the naturals as
   [natle_reflect_iso], and three witnesses.

   ** The route

   Universal arrows, exactly the path Instance/Ab/TorsionFree.v takes for
   §IV.3 Exercise 2 and Instance/Grp/Abelianize.v for §III.1 Exercise 3:
   state the ∃! ([poset_reflection_universal]), package it with
   Theory/Universal/Arrow.v's [universal_arrow_from_UMP], then read
   the functor and the adjunction off [LeftAdjointFunctorFromUniversalArrows] and [AdjunctionFromUniversalArrows] with no further proof.  Nothing in
   that chain is re-derived here, and this file states no triangle
   identity and no naturality square of its own.

   ** Same carrier, coarser [≈], and no choice principle

   [PosetReflection P] has the SAME carrier TYPE as P and the SAME order
   relation -- both recorded by [eq_refl] as [poset_reflection_carrier]
   and [poset_reflection_order] -- and differs from P in ONE field, the
   setoid: [≈] is coarsened from P's own to [poset_refl_equiv P x y :=
   ord_le P x y /\ ord_le P y x].  So the quotient is a SETOID quotient,
   which is what the issue asks for: no new carrier is built, no
   equivalence class is ever formed, no quotient axiom or quotient type
   is used, and no witness is extracted from a [Prop]-valued existential,
   so no choice principle appears anywhere.  This is the design
   Instance/Ab/TorsionFree.v uses for A/T(A) and the one
   Instance/Grp/Abelianization.v uses for G/[G,G].

   Three things fall out of that choice rather than being proved:
   antisymmetry of the reflection is the DEFINITION of its [≈]
   ([PosetReflection_Antisymmetric] hands back the two order proofs it is
   given, as the pair the coarser equivalence asks for); the projection
   is the identity on points; and respectfulness of the coarser relation
   for the order ([PosetReflection]'s one obligation) is transitivity of
   P applied twice on each side.  The only genuinely new argument in the
   file is the mediator's respectfulness, [poset_med]'s first obligation:
   [x ≈ y] in the reflection gives [f x ≤ f y] and [f y ≤ f x] in the
   target by monotonicity, and the target's OWN antisymmetry then gives
   [f x ≈ f y].  That is the one place where being in the subcategory is
   spent, and it is spent exactly once.

   ** Strengths, measured strict-first

   Holding at [eq_refl] (six occurrences, all outside any rejection):
   the reflector's object part is the reflection
   ([poset_reflector_obj]); the universal arrow IS [reflection_proj] and
   its object IS [PosetReflectionObj] ([poset_arrow_is_proj],
   [poset_arrow_obj] -- the TorsionFree.v precedent, since
   [universal_arrow_from_UMP] stores the supplied morphism as the second
   projection of the comma object it builds); the carrier and the order
   are the base preorder's ([poset_reflection_carrier],
   [poset_reflection_order]); and -- the reviewer's check -- the
   adjunction's UNIT applied to any point IS the projection applied to it
   ([poset_unit_is_proj]).

   Falling back, with the cause diagnosed in each case:

   - The unit as a MORPHISM RECORD is only [≈] the projection
   ([poset_unit_is_proj_hom]).  Cause:
   [AdjunctionFromUniversalArrows] builds the transpose as
   [fun g => fmap[U] g ∘ arrow], so the class unit is a COMPOSITE
   record, [fmap[Incl] id ∘ reflection_proj P]; applied to a point that
   composite reduces, as a record it does not.  This is the same
   fallback, with the same cause, that TorsionFree.v records.
   - The reflection of a partial order is isomorphic to it but not equal
   to it: [natle_reflect_iso] is a pure instantiation of
   [reflective_counit_iso] with no tactic, while
   [PosetReflection NatLe = NatLe] is refused -- the two [OrdObject]s
   agree in carrier and order (both pinned as controls) and differ in
   the setoid field, which is the entire content of the reflection.
   - The COUNIT is not read back at all.  It is the other transpose,
   [unique_obj (ump_universal_arrows ...)], and [ump_universal_arrows]
   (Theory/Universal/Arrow.v) is closed with [Qed], so nothing on
   that side reduces and no [eq_refl] is claimed for it.

   The first two fallbacks are pinned as conversion rejections in
   Test/ProbeOrd372.v, together with the record-versus-adjunction
   mismatch (typing), the [sigT]-eta rejection of the [Pos] comparison
   (conversion), the objects-of-[Ord] versus objects-of-a-thin-category
   refutation (conversion) and one universe rejection (formability): six
   negatives of three kinds, plus one scope-free instrument check.  The
   COUNIT is NOT among them -- nothing is claimed about it in either
   direction.  This file itself carries no rejection at all, so it
   contributes nothing to [make todo].

   ** Non-vacuity: three preorders, and what each refutation uses

   - [Chaos2]: [bool] under the TOTAL relation.  Not antisymmetric
   ([Chaos2_not_antisymmetric]) and its reflection identifies the two
   points ([chaos2_merges]).  Its carrier setoid is Instance/Sets.v's
   discrete [bool_setoid_object], so the refutation of antisymmetry is
   settled by [Bool.diff_true_false] on a Leibniz equality -- by
   DISCRIMINATION at the discrete carrier, not by mapping out.
   - [NatLe]: the naturals under [le].  Antisymmetric
   ([NatLe_antisymmetric]), so it is an object [NatLePos] of [Posets],
   the counit isomorphism applies to it, and its reflection is INERT
   ([natle_reflection_inert]: the coarser [≈] is still Leibniz
   equality).  It is the witness that the reflection does not collapse
   everything.
   - [MixOrd]: three points, two of them mutually related and one
   strictly above both.  The reflection merges EXACTLY the pair
   ([mix_merges], and at the projection [mix_proj_merges]) and keeps
   the top apart ([mix_top_stays_apart]).  The merge is by direct
   construction of the two order proofs; the separation is by direct
   COMPUTATION of the relation -- destructing the pair and reading
   [mix_le mtop mleft = False] off the [match] -- not by mapping out
   and not by discrimination.  [MixOrd_not_antisymmetric] does use
   discrimination, at the discrete carrier.

   ** Universes

   Measured with [Set Printing Universes] on all 56 constants of this
   module, reading BOTH binder and block.  NO constraint block carries a
   universe EQUATION; every entry is [<] or [<=].  The identifications
   are in the binders and are the donors': [Poset_reflector] is a
   [Functor@{u u0 u0 u u0 u0}] and [Poset_Reflective_in_Ord] a
   [Reflective@{u1 u u1 u0 u1 u2 u2}] over [Pos_Sub@{u1 u2 u2 ...}], all
   inheriting [Subcategory]'s hom-with-proof identification, which the
   probe guards.  [Set] appears as a BOUND on most constants, from the
   [Prop]-valued order; Instance/Ord.v's header carries the
   discriminating experiment that attributes it.  All 122 constants of
   the two files are closed under the global context, with no [Axioms:]
   line anywhere.

   ** NOT delivered

   - No functoriality of [PosetReflection] beyond what [Poset_reflector]
   gives, and no naturality of [reflection_proj] stated separately.
   - No comparison with Instance/Proset/Skeletal.v's [Proset_Skeleton]
   -- the thin-category shadow of this reflection -- and no [Cat]-level
   statement of any kind.
   - No uniqueness statement for the reflector beyond what
   [poset_reflection_universal] and [reflective_counit_iso] give.
   - No idempotent monad of the reflection.
   Construction/Reflective/Idempotent.v would give it by instantiation
   from [Poset_Reflective_in_Ord]; that instantiation is not made.
   - No coreflection, no [Coreflective] statement, and nothing about
   preorders inside [Cat].
   - No specialization preorder of a topological space, which would be
   the natural bridge to half (b); neither file builds it.
   - No decision procedure for the reflection's [≈] and no normal form,
   and no relation between [PosetReflection] and any quotient
   construction elsewhere in tree. 

   --------
   * * 偏序是所有预序的一个完全反射子范畴

   书籍：Mac Lane，《为工作数学家准备的范畴论》，第二版，
   Springer GTM 5，第 IV.3 节，第 92 页，练习 4。从
   页面图像中阅读：“4. 证明以下子范畴是反射的：
   (a) 在预序范畴 Preord 中，所有偏序的完全子范畴，箭头
   是所有单调函数。 (b) 在 Top 中，T_0 空间的完全子范畴。”
   目录 id：maclane:IV.3:ex4。此文件包含一半 (a)；
   另一半 (b) 在 Instance/Top/Kolmogorov.v，并行编写。

   ** 交付内容是什么[Poset_Reflective_in_Ord : Reflective Pos_Sub] -- Construction/Reflective.v 的记录，其三个字段正是 Mac Lane 术语所命名的三件事物：子范畴（[Pos_Sub_Full]，Instance/Ord.v）的完备性、一个反射器（[Poset_reflector]），以及使其成为包含的左伴随的伴随（[Poset_adj]）。精确阅读这个封装：单独的伴随严格小于记录，而这种不匹配就是本开发中的类型拒绝原因。

   其周围：偏序集合的反射 [PosetReflection] 及 [PosetReflection_Antisymmetric]，其封装 [PosetReflectionObj]，投影 [reflection_proj]，中介 [poset_med]，泛性质 [poset_reflection_universal] 及其箭头 [poset_reflection_universal_arrow]，协单位推论 [poset_reflect_iso] -- 对于一个偏序集合 P，P 的反射同构于 P -- 在自然数上实例化为 [natle_reflect_iso]，以及三个证人。** 路径

   通用箭头，完全遵循 Instance/Ab/TorsionFree.v 在 §IV.3 练习 2 和 Instance/Grp/Abelianize.v 在 §III.1 练习 3 中的路径：声明 ∃! ( [poset_reflection_universal] )，用 Theory/Universal/Arrow.v 的 [universal_arrow_from_UMP] 打包，然后从 [LeftAdjointFunctorFromUniversalArrows] 和 [AdjunctionFromUniversalArrows] 中读取函子和伴随，而无需进一步证明。在该链中没有任何内容在这里重新导出，并且此文件未声明自己的三角恒等式和自然性正方形。

   ** 相同的承载体，更粗的 [≈]，并且没有选择原理[PosetReflection P] 与 P 拥有相同的载体类型，并且具有相同的顺序关系——都由 [eq_refl] 记录为 [poset_reflection_carrier] 和 [poset_reflection_order]——并且与 P 在一个字段上不同，即集合等价关系：[≈] 是从 P 自身粗化得到的 [poset_refl_equiv P x y := ord_le P x y /\ ord_le P y x]。因此，商集是一个集合等价商，这是问题所要求的：没有新载体被构建，没有等价类被形成，没有使用商公理或商类型，也没有从 [Prop] 值存在式中提取见证，因此在任何地方都没有出现选择原理。这是 Instance/Ab/TorsionFree.v 在 A/T(A) 上使用的设计，也是 Instance/Grp/Abelianization.v 在 G/[G,G] 上使用的设计。有三件事是从那个选择中自然得出的，而不是被证明的：
   反射的反对称性是其 [≈] 的定义（[PosetReflection_Antisymmetric] 会将它收到的两个序证明按较粗等价关系要求的对返回）；投影在点上是恒等的；而较粗关系对序的尊重（[PosetReflection] 的唯一义务）是 P 在每一边上两次应用的传递性。文件中唯一真正新的论证是中介者的尊重性，[poset_med] 的第一个义务：在反射中 [x ≈ y] 通过单调性得到目标中的 [f x ≤ f y] 和 [f y ≤ f x]，而目标自身的反对称性则得到 [f x ≈ f y]。那是唯一一次使用属于子范畴的条件，而且仅使用一次。** 优势，严格优先测量

   保持在 [eq_refl]（六次出现，全部在任何拒绝之外）：
   反射器的对象部分是反射
   （[poset_reflector_obj]）；通用箭头是 [reflection_proj]，
   它的对象是 [PosetReflectionObj]（[poset_arrow_is_proj]，
   [poset_arrow_obj] —— TorsionFree.v 先例，因为
   [universal_arrow_from_UMP] 将提供的态射存储为它构建的逗号对象的第二投影）；载体和顺序
   是基础偏序的（[poset_reflection_carrier]，
   [poset_reflection_order]）；并且 —— 审稿人的检查 —— 
   并联的 UNIT 应用于任何点是投影应用于它本身
   （[poset_unit_is_proj]）。

   回退，并在每种情况下诊断原因：- 以 MORPHISM RECORD 表示的单元仅为 [≈] 投影 ([poset_unit_is_proj_hom])。原因：[AdjunctionFromUniversalArrows] 构建转置为 [fun g => fmap[U] g ∘ arrow]，所以类单元是一个复合记录，[fmap[Incl] id ∘ reflection_proj P]；应用到一个点时复合会简化，但作为记录则不会。这与 TorsionFree.v 记录中相同的回退及其原因相同。- 一个偏序的反射与其同构但不相等：[natle_reflect_iso] 是 [reflective_counit_iso] 的一个纯实例化，没有使用任何策略，而 [PosetReflection NatLe = NatLe] 被拒绝——两个 [OrdObject] 在承载和顺序上（均固定为控件）一致，而在集合域上不同，这就是反射的全部内容。- COUNIT 根本没有被读取回来。它是另一个转置，
   [unique_obj (ump_universal_arrows ...)]，以及 [ump_universal_arrows] 
   （Theory/Universal/Arrow.v）被 [Qed] 关闭，所以那一边没有任何简化，也没有为其声明 [eq_refl]。

   前两个回退作为转换拒绝在 Test/ProbeOrd372.v 中被固定，还有记录与伴随的不匹配（类型检查）、ZWZ56WZZ -eta 对 [Pos] 比较的拒绝（转换）、ZWZ58WZZ 对薄范畴对象的反驳（转换）以及一个宇宙拒绝（可形成性）：三种类型的六个否定，加上一个不涉及范围的工具检查。COUNIT 不在其中——无论哪个方向都没有对它作出声明。这个文件本身没有任何拒绝，因此它对 [make todo] 没有贡献。** 非空性：三种前序，以及每种反驳所使用的内容-  [Chaos2]：在 TOTAL 关系下的 [bool]。不满足反对称性（[Chaos2_not_antisymmetric]），其反射将两个点（[chaos2_merges]）认同。它的载体集合是 Instance/Sets.v 的离散 [bool_setoid_object]，因此通过离散载体上的 [Bool.diff_true_false] 对莱布尼茨等式进行区分来驳斥反对称性，而不是通过映射外部。-  [NatLe]：在 [le] 下的自然数。满足反对称性（[NatLe_antisymmetric]），因此它是 [Posets] 的一个对象 [NatLePos]，协单位同构适用于它，其反射是惰性的（[natle_reflection_inert]：更粗的 [≈] 仍然是莱布尼茨等式）。它是反射不会将一切压缩的证据。-  [MixOrd]：三个点，其中两个相互相关，一个严格高于两者。反射精确地将这一对合并 ([mix_merges]，及在投影 [mix_proj_merges] 处) 并保持顶部分开 ([mix_top_stays_apart])。合并是通过直接构造两个顺序证明来实现的；分离是通过直接计算关系——析构该对并从 [match] 中读取 [mix_le mtop mleft = False]——而不是通过映射或区分来实现的。[MixOrd_not_antisymmetric] 的确在离散载体上使用了区分。

   ** 宇宙使用 [Set Printing Universes] 测量此模块的所有 56 个常量，读取绑定器和块。没有约束块包含宇宙方程；每个条目都是 [<] 或 [<=]。标识在绑定器中，并且属于捐赠者：[Poset_reflector] 是一个 [Functor@{u u0 u0 u u0 u0}]，[Poset_Reflective_in_Ord] 是一个 [Reflective@{u1 u u1 u0 u1 u2 u2}] 位于 [Pos_Sub@{u1 u2 u2 ...}] 上，所有都继承 [Subcategory] 的带证明同一性，探针进行保护。[Set] 在大多数常量上作为 BOUND 出现，来自 [Prop] 值的顺序；Instance/Ord.v 的头部包含区分它的实验。两个文件的所有 122 个常量在全局上下文下都是封闭的，没有任何 [Axioms:] 行。

   ** 未交付- [PosetReflection] 的函子性不超过 [Poset_reflector] 所提供的范围，并且 [reflection_proj] 的自然性没有单独说明。 - 与 Instance/Proset/Skeletal.v 中的 [Proset_Skeleton] 没有比较 —— 即该反射的薄范畴影子 —— 并且没有任何 [Cat] 级别的声明。 - 超出 [poset_reflection_universal] 和 [reflective_counit_iso] 所提供的范围，没有反射子唯一性的声明。 - 反射没有幂等单子。Construction/Reflective/Idempotent.v 可以通过从 [Poset_Reflective_in_Ord] 实例化来提供，但该实例化未进行。 - 没有共反射，没有 [Coreflective] 的声明，并且关于 [Cat] 中的预序没有任何内容。 - 拓扑空间的专化预序没有构建，这将是通向中间 (b) 的自然桥梁；两个文件都没有构建它。- 对于反射的 [≈] 没有决策程序，也没有标准形式，
   并且 [PosetReflection] 与树中其他任何商构造之间没有关系。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Ord.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(* * ** The reflection: same carrier, coarser [≈] / * ** 反射：相同载体，更粗的 [≈] *)

Definition poset_refl_equiv (P : OrdObject)
    (x y : carrier (ord_setoid P)) : Prop :=
  ord_le P x y ∧ ord_le P y x.

#[local] Obligation Tactic := idtac.

Program Definition poset_refl_setoid (P : OrdObject)
  : Setoid (carrier (ord_setoid P)) := {|
  equiv := poset_refl_equiv P
|}.
Next Obligation.
  intro P; constructor.
  - intro x; split; apply ord_refl.
  - intros x y [Hxy Hyx]; split; assumption.
  - intros x y z [Hxy Hyx] [Hyz Hzy]; split.
    + exact (ord_trans P x y z Hxy Hyz).
    + exact (ord_trans P z y x Hzy Hyx).
Qed.

Definition poset_refl_carrier (P : OrdObject) : SetoidObject := {|
  carrier   := carrier (ord_setoid P);
  is_setoid := poset_refl_setoid P
|}.

Program Definition PosetReflection (P : OrdObject) : OrdObject := {|
  ord_setoid := poset_refl_carrier P;
  ord_le     := ord_le P;
  ord_refl   := ord_refl P;
  ord_trans  := ord_trans P
|}.
Next Obligation.
  intros P x x' [Hxx' Hx'x] y y' [Hyy' Hy'y]; split; intro H.
  - exact (ord_trans P x' x y' Hx'x (ord_trans P x y y' H Hyy')).
  - exact (ord_trans P x x' y Hxx' (ord_trans P x' y' y H Hy'y)).
Qed.

(*
   * Antisymmetry of the reflection is the DEFINITION of its [≈]: the two
   order proofs handed in ARE the pair the coarser equivalence asks for. 

   --------
   * 反射的不对称性是其 [≈] 的定义：提交的两个顺序证明正是粗等价要求的那一对。
*)
Lemma PosetReflection_Antisymmetric (P : OrdObject)
  : OrdAntisymmetric (PosetReflection P).
Proof. intros x y Hxy Hyx; split; assumption. Defined.

Definition PosetReflectionObj (P : OrdObject) : Posets :=
  (PosetReflection P; PosetReflection_Antisymmetric P).

Program Definition reflection_proj (P : OrdObject)
  : P ~{Ord}~> PosetReflection P :=
  @Build_OrdHom P (PosetReflection P)
    {| morphism := fun x : carrier (ord_setoid P) => x |} _.
Next Obligation.
  intros P x y Hxy; split; apply ord_le_of_equiv.
  - exact Hxy.
  - symmetry; exact Hxy.
Qed.
Next Obligation. intros P x y H; exact H. Qed.

(** ** The universal property / ** 通用性质 *)

Program Definition poset_med {P D : OrdObject} (HD : OrdAntisymmetric D)
    (f : P ~{Ord}~> D) : PosetReflection P ~{Ord}~> D :=
  @Build_OrdHom (PosetReflection P) D
    {| morphism := fun x : carrier (ord_setoid P) => ord_fn f x |} _.
Next Obligation.
  intros P D HD f x y [Hxy Hyx]; simpl.
  exact (HD _ _ (ord_mono f x y Hxy) (ord_mono f y x Hyx)).
Qed.
Next Obligation. intros P D HD f x y H; exact (ord_mono f x y H). Qed.

Theorem poset_reflection_universal (P : OrdObject) :
  ∀ (d : Posets) (f : P ~{Ord}~> Incl Ord Pos_Sub d),
    ∃! g : PosetReflectionObj P ~{Posets}~> d,
      f ≈ fmap[Incl Ord Pos_Sub] g ∘ reflection_proj P.
Proof.
  intros d f.
  unshelve eexists.
  - exact (poset_med `2 d f; I).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

Definition poset_reflection_universal_arrow (P : OrdObject)
  : @UniversalArrow Ord Posets P (Incl Ord Pos_Sub) :=
  @universal_arrow_from_UMP Ord Posets P (Incl Ord Pos_Sub)
    (PosetReflectionObj P) (reflection_proj P)
    (poset_reflection_universal P).

Definition Poset_reflector : Ord ⟶ Posets :=
  LeftAdjointFunctorFromUniversalArrows (Incl Ord Pos_Sub)
    poset_reflection_universal_arrow.

Definition Poset_adj : Poset_reflector ⊣ Incl Ord Pos_Sub :=
  AdjunctionFromUniversalArrows (Incl Ord Pos_Sub)
    poset_reflection_universal_arrow.

Definition Poset_Reflective_in_Ord : Reflective Pos_Sub :=
  @Build_Reflective Ord Pos_Sub Pos_Sub_Full
    Poset_reflector Poset_adj.

(** ** Strict readbacks / ** 严格复述 *)

Example poset_reflector_obj (P : OrdObject) :
  `1 (fobj[Poset_reflector] P) = PosetReflection P := eq_refl.

Example poset_arrow_is_proj (P : OrdObject) :
  @arrow Ord Posets P (Incl Ord Pos_Sub)
    (poset_reflection_universal_arrow P)
    = reflection_proj P := eq_refl.

Example poset_arrow_obj (P : OrdObject) :
  @arrow_obj Ord Posets P (Incl Ord Pos_Sub)
    (poset_reflection_universal_arrow P)
    = PosetReflectionObj P := eq_refl.

Definition poset_unit (P : OrdObject)
  : P ~{Ord}~> Incl Ord Pos_Sub (fobj[Poset_reflector] P) :=
  @Category.Theory.Adjunction.unit _ _ _ _ Poset_adj P.

Example poset_unit_is_proj (P : OrdObject)
    (x : carrier (ord_setoid P)) :
  ord_fn (poset_unit P) x = ord_fn (reflection_proj P) x := eq_refl.

Lemma poset_unit_is_proj_hom (P : OrdObject) :
  poset_unit P ≈ reflection_proj P.
Proof. intro a; reflexivity. Defined.

Example poset_reflection_carrier (P : OrdObject) :
  carrier (ord_setoid (PosetReflection P)) = carrier (ord_setoid P)
  := eq_refl.

Example poset_reflection_order (P : OrdObject) :
  ord_le (PosetReflection P) = ord_le P := eq_refl.

(** ** The counit at a partial order / ** 偏序下的余单位 *)

Definition poset_reflect_iso (x : Posets) :
  fobj[Poset_reflector] (Incl Ord Pos_Sub x) ≅[Posets] x :=
  reflective_counit_iso Poset_Reflective_in_Ord x.

(** ** Non-vacuity: three preorders / ** 非空性：三个预序 *)

(*
   * The two-element set under the TOTAL relation: a preorder that is as far
   from a partial order as possible.  Its carrier setoid is the discrete
   one (Instance/Sets.v's [bool_setoid_object]), so the refutation of
   antisymmetry is settled by [discriminate] rather than by mapping out. 

   --------
   * 在 TOTAL 关系下的二元集合：一种尽可能远离偏序的预序。它的承载集合是离散的（Instance/Sets.v 的 [bool_setoid_object]），因此反对反对称性的证伪是由 [discriminate] 解决的，而不是通过映射出去。
*)
Program Definition Chaos2 : OrdObject := {|
  ord_setoid := bool_setoid_object;
  ord_le     := fun _ _ => True
|}.
Next Obligation. intro x; exact I. Qed.
Next Obligation. intros x y z Hxy Hyz; exact I. Qed.

Lemma Chaos2_not_antisymmetric : OrdAntisymmetric Chaos2 → False.
Proof. intro H; exact (Bool.diff_true_false (H true false I I)). Qed.

Lemma chaos2_merges :
  (true : carrier (ord_setoid (PosetReflection Chaos2))) ≈ false.
Proof. split; exact I. Defined.

(*
   * The naturals under [le]: already a partial order, so the reflection is
   inert on it and the counit isomorphism applies. 

   --------
   * 在 [le] 下的自然数：已经是一个偏序，因此反射在其上是惰性的，并且余单位同构适用。
*)
Program Definition NatLe : OrdObject := {|
  ord_setoid := {| carrier := nat ; is_setoid := eq_Setoid nat |};
  ord_le     := Nat.le
|}.
Next Obligation. intro x; apply Nat.le_refl. Qed.
Next Obligation. intros x y z Hxy Hyz; exact (Nat.le_trans _ _ _ Hxy Hyz). Qed.

Lemma NatLe_antisymmetric : OrdAntisymmetric NatLe.
Proof. intros x y Hxy Hyx; exact (Nat.le_antisymm x y Hxy Hyx). Qed.

Definition NatLePos : Posets := (NatLe; NatLe_antisymmetric).

Definition natle_reflect_iso :
  fobj[Poset_reflector] (Incl Ord Pos_Sub NatLePos) ≅[Posets] NatLePos :=
  poset_reflect_iso NatLePos.

Lemma natle_reflection_inert (x y : carrier (ord_setoid NatLe)) :
  (x : carrier (ord_setoid (PosetReflection NatLe))) ≈ y → x = y.
Proof. intros [Hxy Hyx]; exact (Nat.le_antisymm x y Hxy Hyx). Qed.

(*
   * A MIXED preorder: two mutually related points and one strictly above
   them.  The reflection merges exactly the pair and keeps the top apart. 

   --------
   * 一个混合的前序：两个相互关联的点和一个严格在它们之上的点。反射正好合并这对点，并将顶部保持分开。
*)
Inductive MixPt : Set := mleft | mright | mtop.

Definition mix_le (x y : MixPt) : Prop :=
  match x, y with
  | mtop, mtop => True
  | mtop, _    => False
  | _, _       => True
  end.

Program Definition MixOrd : OrdObject := {|
  ord_setoid := {| carrier := MixPt ; is_setoid := eq_Setoid MixPt |};
  ord_le     := mix_le
|}.
Next Obligation. intro x; destruct x; exact I. Qed.
Next Obligation. intros x y z; destruct x, y, z; simpl; tauto. Qed.

Lemma MixOrd_not_antisymmetric : OrdAntisymmetric MixOrd → False.
Proof. intro H; discriminate (H mleft mright I I). Qed.

Lemma mix_merges :
  (mleft : carrier (ord_setoid (PosetReflection MixOrd))) ≈ mright.
Proof. split; exact I. Defined.

Lemma mix_top_stays_apart :
  (mleft : carrier (ord_setoid (PosetReflection MixOrd))) ≈ mtop → False.
Proof. intros [_ H]; exact H. Qed.

Lemma mix_proj_merges :
  ord_fn (reflection_proj MixOrd) mleft
    ≈ ord_fn (reflection_proj MixOrd) mright.
Proof. exact mix_merges. Defined.
