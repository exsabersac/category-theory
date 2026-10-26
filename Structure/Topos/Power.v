Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Adjunction.Right.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(*
 [Category.Functor.Opposite] opens [functor_scope], after which a bare
 [C^op] on a CATEGORY parses as [Opposite_Functor C] and is rejected with
 “The term C has type Category while it is expected to have type ?C ⟶ ?D”.
 Reopening [category_scope] here restores the reading this file wants.
 Same family as the notation guards of Theory/Universal/Arrow/Dual.v and
 Instance/Rng/Mod.v. 

 --------
 [Category.Functor.Opposite] 打开 [functor_scope]，之后 CATEGORY 上的裸 [C^op] 解析为 [Opposite_Functor C] 并被拒绝，提示“术语 C 的类型是 Category，而预计的类型是 ?C ⟶ ?D”。在这里重新打开 [category_scope] 可以恢复该文件所需的读取。与 Theory/Universal/Arrow/Dual.v 和 Instance/Rng/Mod.v 中的符号保护属于同一家族。
*)
Open Scope category_scope.

(*
 The power-object functor of an elementary topos, and its self-adjointness
 on the right.

 nLab:      https://ncatlab.org/nlab/show/power+object
 nLab:      https://ncatlab.org/nlab/show/topos
 Wikipedia: https://en.wikipedia.org/wiki/Topos

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §IV.10,
 book p. 107 (`maclane:IV.10:remark2`), closes the topos section with one
 sentence and no proof:

 “The axioms for a topos have many useful consequences. For exam-
 ples, every topos has all finite colimits.”

 The standard route to that sentence is Paré's (1974): the contravariant
 power-object functor P = Ω^(−) : E^op ⟶ E is self-adjoint on the right and
 MONADIC, so E^op is EQUIVALENT to the Eilenberg-Moore category of the induced
 monad and therefore inherits E's finite limits; read in E those are finite
 colimits.  This file is step one and step two of that route: the functor, and
 the self-adjointness.  Monadicity is Structure/Topos/Monadic.v; the colimits
 are Structure/Topos/Colimits.v.  NONE of Mac Lane, Awodey or Seven Sketches
 proves the theorem, and Mac Lane-Moerdijk, the reference Mac Lane and Awodey
 send the reader to, was not available; the argument was reconstructed and
 CHECKED BY COMPILATION.

 THE FUNCTOR IS A PARTIAL APPLICATION AND RAISES NO OBLIGATION.  The
 internal hom [InternalHomFunctor C : C^op ∏ C ⟶ C] of
 Functor/Hom/Internal.v is contravariant in its FIRST argument, which is
 exactly the variance of P, so [Partial_l] at Ω is the whole definition
 and all three functor laws are inherited.  Two nearby constants are NOT
 donors, and both refusals are pinned in Test/ProbeToposColimits405.v:
 [Partial_r] fixes the first argument and varies the second, so it has
 the wrong variance; and [Exp_Functor] of
 Structure/Cartesian/Closed/Adjunction.v is covariant in the base with
 the exponent held fixed (that file's own header calls it “the partial
 application at a fixed exponent”), so its object action is (−)^S and
 not Ω^(−).

 STEP TWO CONSUMES NO SUBOBJECT CLASSIFIER, ONLY THE OBJECT Ω.  The issue
 routes the two-sided transposition through [relations_iso]
 (Structure/Topos.v), i.e. through subobjects of a × b.  That is not needed:
 the bijection E(a, Ω^b) ≅ E(b, Ω^a) is a fact about ANY object in ANY
 cartesian closed category, and the map is already in the tree as [flip]
 (Structure/Cartesian/Closed.v), [flip f := curry (uncurry f ∘ swap)].  What
 was missing is that [flip] is an INVOLUTION: a whole-tree search for an
 involution lemma about that [flip] returned only the list-reversal hypothesis
 [flip_involutive] of Lib/TList.v and Lib/NETList.v and Theory/Morphisms.v's
 [flip_invol] about an [Involutive] endomorphism (a substring sweep adds
 Construction/Free/Groupoid.v's [sflip_involutive], about a different flip),
 none of which is this [flip], and by SHAPE the only statement of the form
 [flip (flip f)] anywhere in the tree is [flip_flip] itself, which supplies it
 in four rewrites.

 THE FOUR NATURALITY FIELDS COLLAPSE TO TWO LEMMAS, and that is why the
 step is cheap.  With S = T = P and both legs of the isomorphism equal
 to [flip], [to_aor_nat_a] and [from_aor_nat_x] are one and the same
 statement ([flip_comp]) and [to_aor_nat_x] and [from_aor_nat_a] are the
 other ([flip_pow_comp]).  The three prior in-tree witnesses of S = T --
 Adjunction/Right.v's [Powerset_AdjointOnTheRight],
 Structure/Monoidal/Dual.v's [dual_self_adjoint_on_the_right] and
 Instance/InnerProduct/Galois.v's [perp_AdjointOnTheRight] -- build
 [aor] the same way, as a record literal whose [to] and [from] are one
 map.

 FIDELITY TO THE ISSUE'S OWN ROUTE is nevertheless recorded, as
 [pow_aor_is_relations]: transporting a morphism a ~> Pow b to the
 subobject of a × b it classifies, reindexing that subobject along
 [swap], and classifying back is [flip].  It holds at ≈ and is refused
 at [eq_refl] -- NOT because either leg of [relations_iso] is stuck
 (both reduce on the nose, and §(E) reads them back by [eq_refl]) but
 because the two sides are [curry] of the untransposed map composed
 with [swap] against [curry] of the characteristic map of a
 doubly-reindexed subobject, and reindexing introduces chosen pullback
 objects.  This is the one place the classifier enters the file, and
 only as a check.

 WHAT IS NOT HERE.  No monad: [pow_monad] would need
 [Adjunction_Induced_Monad] from Monad/Comparison.v, measured at +6
 modules on this file's closure, so it is declared in
 Structure/Topos/Monadic.v where the monadicity machinery is required
 anyway.  No naturality of [pow_aor_is_relations] in a or b.  No claim
 that the unit and the counit differ: they are the same term. 

 --------
 基本拓扑的幂对象函子及其在右侧的自伴性。

 nLab:       https://ncatlab.org/nlab/show/power+object 
 nLab:       https://ncatlab.org/nlab/show/topos 
 Wikipedia:  https://en.wikipedia.org/wiki/Topos 

 Mac Lane，《泛函数学家的范畴论》，第二版，第IV.10节，书页107（`maclane:IV.10:remark2`），以一句话而没有证明结束了拓扑论部分：

 “拓扑的公理有许多有用的推论。例如，每一个拓扑都有所有有限余积。”通向该结论的标准路径是 Paré（1974 年）的路径：逆变幂对象函子 P = Ω^(−) : E^op ⟶ E 在右侧自伴且是单子性的，因此 E^op 等价于其诱导单子的 Eilenberg-Moore 范畴，因此继承了 E 的有限极限；在 E 中读取时，这些是有限余极限。该文件是该路径的第一步和第二步：函子，以及自伴性。单子性在 Structure/Topos/Monadic.v 中；余极限在 Structure/Topos/Colimits.v 中。Mac Lane、Awodey 或 Seven Sketches 中没有人证明该定理，而 Mac Lane-Moerdijk（Mac Lane 和 Awodey 推荐读者参考的文献）无法获取；该论证已被重建并通过编译检查。函子是一个部分应用，并且不会引发任何义务。Functor/Hom/Internal.v 的内部 Hom [InternalHomFunctor C : C^op ∏ C ⟶ C] 在它的第一个参数上是逆变的，这正好是 P 的变异性，所以 [Partial_l] 在 Ω 处是完整定义，并且三条函子定律都被继承。两个相邻的常量不是供体，并且两个拒绝都固定在 Test/ProbeToposColimits405.v 中：[Partial_r] 固定第一个参数并改变第二个参数，因此它的变异性不正确；而 Structure/Cartesian/Closed/Adjunction.v 中的 [Exp_Functor] 在指数固定时对基数是协变的（该文件自身的头部称其为“在固定指数处的部分应用”），所以它的对象作用是 (−)^S，而不是 Ω^(−)。步骤二不消耗子对象分类器，只消耗对象 Ω。该问题通过 [relations_iso] (Structure/Topos.v) 处理双向换位，即通过 a × b 的子对象。这并非必要：双射 E(a, Ω^b) ≅ E(b, Ω^a) 是关于任意笛卡尔封闭范畴中任意对象的一个事实，并且该映射已经存在于树中，即 [flip] (Structure/Cartesian/Closed.v), [flip f := curry (uncurry f ∘ swap)]。缺失的是 [flip] 是一个倒置：对关于 [flip] 的倒置引理进行整棵树搜索仅返回了 Lib/TList.v 和 Lib/NETList.v 中的列表反转假设 [flip_involutive]，以及 Theory/Morphisms.v 中关于 [Involutive] 的 [flip_invol] 的一个自同态（子字符串扫描还添加了 Construction/Free/Groupoid.v 中的 [sflip_involutive]，关于一个不同的翻转），这些都不是 [flip]，并且根据 SHAPE，在树中任何地方唯一的 [flip (flip f)] 形式的陈述是 [flip_flip] 本身，它通过四次重写提供了该陈述。四个自然性场坍缩为两个引理，这就是为什么这一步很便宜。令 S = T = P 且同构的两条腿都等于 [flip]，[to_aor_nat_a] 和 [from_aor_nat_x] 是同一个陈述（[flip_comp]），而 [to_aor_nat_x] 和 [from_aor_nat_a] 是另一个（[flip_pow_comp]）。在此之前的三个树内证明 S = T 的证据——Adjunction/Right.v 的 [Powerset_AdjointOnTheRight]，Structure/Monoidal/Dual.v 的 [dual_self_adjoint_on_the_right] 和 Instance/InnerProduct/Galois.v 的 [perp_AdjointOnTheRight]——以相同方式构建 [aor]，作为一个记录字面值，其 [to] 和 [from] 是同一映射。对该问题自身路径的忠实性仍然被记录为，[pow_aor_is_relations]：将一个态射 a ~> Pow b 传送到它所分类的 a × b 的子对象，沿着 [swap] 对该子对象重新索引，然后再分类回去为 [flip]。它在 ≈ 上成立，但在 [eq_refl] 上被拒绝——不是因为 [relations_iso] 的任一边卡住（两者都精确归约，并且 §(E) 通过 [eq_refl] 重新读取它们），而是因为两边是未转置映射的一部分，与二重重新索引子对象的特征映射的 [swap] 对 [curry] 的组合，而重新索引引入了选定的拉回对象。这是分类器进入文件的唯一地点，而且仅作为检查。这里缺少的内容。没有单子：[pow_monad] 将需要来自 Monad/Comparison.v 的 [Adjunction_Induced_Monad]，在此文件的闭包上测得为 +6 个模块，因此它在 Structure/Topos/Monadic.v 中声明，在那里单子性机制是必需的。[pow_aor_is_relations] 在 a 或 b 中没有自然性。没有声称单位和余单位不同：它们是相同的项。
*)

Section ToposPower.

Context {C : Category}.
Context `{H : @ElementaryTopos C}.

(** ** (A) The power-object functor / **（A）幂对象函子 *)

(*
 P := Ω^(−), as the partial application of the internal hom at Ω.  Its
 contravariance is [InternalHomFunctor]'s in its first argument. 

 --------
 P := Ω^(−)，作为内部 Hom 在 Ω 上的偏应用。它在第一个参数上的逆变性与 [InternalHomFunctor] 相同。
*)
Definition PowF : C^op ⟶ C := Partial_l (InternalHomFunctor C) Ω.

(* Three readbacks, all on the nose. / 三次复述，全都准确无误。 *)
Example powf_obj (a : C) : fobj[PowF] a = Pow a := eq_refl.

Example powf_obj_exponent (a : C) : fobj[PowF] a = exponent_obj a Ω := eq_refl.

Example powf_map {a b : C} (f : b ~{C}~> a) :
  fmap[PowF] f = curry (id ∘ eval ∘ second f) := eq_refl.

(* * ** (B) [flip] is an involution, and its two composition laws / * ** (B) [flip] 是一个自反映射，以及它的两个组合规律 *)

(* NEW: no involution lemma for the cartesian-closed [flip] existed. / 最新：笛卡尔闭合的 [flip] 不存在 involution 引理。 *)
Lemma flip_flip {a b : C} (f : a ~> Ω^b) : flip (flip f) ≈ f.
Proof.
  unfold flip.
  rewrite uncurry_curry, <- comp_assoc, swap_invol, id_right.
  apply curry_uncurry.
Qed.

#[local] Program Instance flip_respects {a b : C} :
  Proper (equiv ==> equiv) (@flip C _ _ a Ω b).
Next Obligation. proper. unfold flip. now rewrites. Qed.

(*
 Naturality in the SOURCE: precomposition downstairs is P-image
 postcomposition upstairs. 

 --------
 源中的自然性：楼下的前组合是 P-像，楼上的后组合是 P-像。
*)
Lemma flip_comp {a a' b : C} (f : a ~> Ω^b) (g : a' ~> a) :
  flip (f ∘ g) ≈ fmap[PowF] g ∘ flip f.
Proof.
  unfold flip; simpl.
  rewrite uncurry_comp, curry_comp_l, id_left, <- !comp_assoc,
          <- first_second, !comp_assoc, eval_first, uncurry_curry,
          <- !comp_assoc, swap_second.
  reflexivity.
Qed.

(*
 Naturality in the EXPONENT: P-image precomposition downstairs is
 postcomposition upstairs. 

 --------
 指数中的自然性：在底层进行 P-像的前合成等于在顶层进行后合成。
*)
Lemma flip_pow_comp {a x x' : C} (p : a ~> Ω^x') (k : x ~> x') :
  flip (fmap[PowF] k ∘ p) ≈ flip p ∘ k.
Proof.
  apply uncurry_inj.
  unfold flip; simpl.
  rewrite uncurry_curry, uncurry_comp, uncurry_curry, uncurry_comp,
          uncurry_curry, id_left, <- (eval_first p), <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  unfork.
Qed.

(* * ** (C) Self-adjointness on the right / * **（C）右侧自伴性 *)

(* [flip] as a morphism of [Sets], used for BOTH legs of the isomorphism. / [flip] 作为 [Sets] 的一个态射，用于同构的两个部分。 *)
Program Definition flip_mor (a b : C) :
  {| carrier := a ~{C}~> Ω^b ; is_setoid := @homset C a (Ω^b) |}
    ~{Sets}~>
  {| carrier := b ~{C}~> Ω^a ; is_setoid := @homset C b (Ω^a) |} :=
  {| morphism := fun f => flip f |}.
Next Obligation. proper. unfold flip. now rewrites. Qed.

Program Definition pow_aor (a x : C) :
  @Isomorphism Sets
    {| carrier := @hom C a (PowF x); is_setoid := @homset C a (PowF x) |}
    {| carrier := @hom C x (PowF a); is_setoid := @homset C x (PowF a) |} :=
  {| to := flip_mor a x ; from := flip_mor x a |}.
Next Obligation. simpl; apply flip_flip. Qed.
Next Obligation. simpl; apply flip_flip. Qed.

(*
 Mac Lane §IV.2 definition 2's vocabulary (Adjunction/Right.v): the four
 naturality fields are [flip_comp], [flip_pow_comp], [flip_pow_comp],
 [flip_comp], in that order. 

 --------
 Mac Lane §IV.2 定义 2 的词汇（伴随/右.v）：四个自然性域依次是 [flip_comp]、[flip_pow_comp]、[flip_pow_comp]、[flip_comp]。
*)
Program Definition pow_self_adjoint : AdjointOnTheRight PowF PowF :=
  {| aor := pow_aor |}.
Next Obligation. apply flip_comp. Qed.
Next Obligation. apply flip_pow_comp. Qed.
Next Obligation. apply flip_pow_comp. Qed.
Next Obligation. apply flip_comp. Qed.

(*
 The ordinary adjunction it unpacks to.  In Theory/Adjunction.v's naming
 [Adjunction {C D} (F : D ⟶ C) (U : C ⟶ D)] this reads: the “top”
 category is C^op, the “bottom” is C, the LEFT adjoint is P^op and the
 RIGHT adjoint -- the monadic one -- is P. 

 --------
 它展开的普通伴随。在 Theory/Adjunction.v 的命名 [Adjunction {C D} (F : D ⟶ C) (U : C ⟶ D)] 中，这读作：
 “顶层”类别是 C^op，“底层”是 C，左伴随是 P^op，而右伴随——单子伴随——是 P。
*)
Definition pow_adjunction :
  @Adjunction (C^op) C (Opposite_Functor PowF) PowF :=
  Adjunction_of_AdjointOnTheRight pow_self_adjoint.

(* The two transposes ARE [flip], on the nose. / 这两个转置正好是 [flip]。 *)
Example pow_to_adj_is_flip {a x : C} (f : a ~> PowF x) :
  to (@adj (C^op) C (Opposite_Functor PowF) PowF pow_adjunction x a) f
    = flip f := eq_refl.

Example pow_from_adj_is_flip {a x : C} (f : x ~> PowF a) :
  from (@adj (C^op) C (Opposite_Functor PowF) PowF pow_adjunction x a) f
    = flip f := eq_refl.

(*
 The unit and the counit of a self-adjunction on the right are one and
 the same map, [flip id] -- classically the “singleton of singleton”
 Ω^(Ω^x) map.  Both readbacks are on the nose. 

 --------
 在右自伴随中的单位和余单位是同一个映射，即[flip id]——在经典上被称为“单例的单例” Ω^(Ω^x) 映射。两个回读都是完全一致的。
*)
Example pow_unit_is_flip_id {x : C} :
  @unit (C^op) C (Opposite_Functor PowF) PowF pow_adjunction x
    = flip (@id C (Pow x)) := eq_refl.

Example pow_counit_is_flip_id {x : C} :
  @counit (C^op) C (Opposite_Functor PowF) PowF pow_adjunction x
    = flip (@id C (Pow x)) := eq_refl.

(* * ** (D) The reduction lemma for precomposition / * ** (D) 预组合的约减引理 *)

(* P applied to m, precomposed with a transpose, is the transpose of the substituted map. Used at two sites in Structure/Topos/Monadic.v, [pow_ex_mono] and [pow_bc]. / 将 P 应用于 m，并预先与转置组合，是代入映射的转置。在 Structure/Topos/Monadic.v 的两个位置使用，[pow_ex_mono] 和 [pow_bc]。 *)
Lemma pow_precompose {z u x : C} (m : u ~> x) (h : z × x ~> Ω) :
  fmap[PowF] m ∘ curry h ≈ curry (h ∘ second m).
Proof.
  simpl.
  rewrite curry_comp_l, id_left, <- !comp_assoc, <- first_second,
          !comp_assoc, eval_first, uncurry_curry.
  reflexivity.
Qed.

(* * ** (E) Fidelity to the issue's [relations_iso] route / * **（E）忠实于问题的 [relations_iso] 路线 *)

(*
 BOTH legs of [relations_iso] reduce on the nose, which the brief for this
 work did not expect: the composite of two [Program]-elaborated setoid
 morphisms still converts to [curry ∘ char_sub] one way and to pulling
 truth back along the untransposed map the other. 

 --------
 [relations_iso] 的两条腿都在节点上减少，而这项工作的简报并未预料到这一点：两个 [Program] 精细化集合态射的复合仍然以一种方式转换为 [curry ∘ char_sub]，并通过非转置映射将真值拉回的方式转换为另一种方式。
*)
Example relations_iso_to_is_curry_char {a b : C} (s : SubObj (a × b)) :
  to (relations_iso a b) s = curry (char_sub s) := eq_refl.

Example relations_iso_from_is_reindex {a b : C} (f : a ~> Pow b) :
  from (relations_iso a b) f = sub_reindex (uncurry f) truth_subobject
  := eq_refl.

(*
 The issue's transposition: read f : a ~> Pow b as a subobject of a × b,
 turn that relation round with [swap], and read it back as b ~> Pow a. 

 --------
 问题的换位：将 f : a ~> Pow b 读作 a × b 的子对象，使用 [swap] 将该关系翻转，然后将其读回为 b ~> Pow a。
*)
Definition pow_relations {a b : C} (f : a ~> Pow b) : b ~> Pow a :=
  to (relations_iso b a) (sub_reindex swap (from (relations_iso a b) f)).

(*
 It agrees with [flip], hence with [aor], POINTWISE and at ≈.  The proof
 is [char_reindex] followed by the classifier round trip; no naturality
 of either isomorphism is used.  The [eq_refl] form is refused -- the two
 sides are [curry] of the untransposed map composed with [swap] on one
 side and [curry] of a characteristic map of a doubly-reindexed subobject
 on the other, and the reindexing introduces chosen pullback objects.
 Test/ProbeToposColimits405.v pins the refusal with this lemma as its
 control. 

 --------
 它与 [flip] 一致，因此与 [aor] 一致，在点上和在 ≈ 上也一致。证明是通过 [char_reindex]，然后是分类器的往返转换；没有使用任何同构的自然性。[eq_refl] 形式被拒绝——两边分别是未转置映射的 [curry] 与 [swap] 的组合，以及一边是双重重索引子对象的特征映射的 [curry]，并且重索引引入了选定的拉回对象。Test/ProbeToposColimits405.v 用这个引理作为控制来确认拒绝。
*)
Lemma pow_aor_is_relations {a b : C} (f : a ~> Pow b) :
  to (pow_aor a b) f ≈ pow_relations f.
Proof.
  assert (Hl : to (pow_aor a b) f ≈ curry (uncurry f ∘ swap))
    by reflexivity.
  assert (Hr : pow_relations f
                 ≈ curry (char_sub (sub_reindex swap
                     (sub_reindex (uncurry f) truth_subobject))))
    by reflexivity.
  rewrite Hl, Hr.
  apply curry_respects.
  symmetry.
  transitivity (char_sub (sub_reindex (uncurry f) truth_subobject) ∘ swap).
  - apply char_reindex.
  - apply compose_respects; [| reflexivity].
    apply (classifier_char_roundtrip (uncurry f)).
Qed.

End ToposPower.

Arguments PowF {C H}.
