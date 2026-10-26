Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Free.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * The underlying-set functor of R-modules is represented by R

   Book: Riehl, “Category Theory in Context”, 2nd ed., §2.1
   Example 2.1.5(iv), printed p. 56 (PDF pp. 76-77) —
   riehl:2.1:example5
   Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
   §III.1, printed p. 56 — maclane:III.1:remark2
   Book: Riehl, “Category Theory in Context”, 2nd ed., §4.1
   Exercise 4.1.v, printed p. 138 —
   riehl:4.1:exv, which asks for a proof that the free R-module
   construction is FUNCTORIAL in the generating set.  That
   exercise needs no work here and none is done: packaging the
   free module as a [UniversalArrow] and feeding it to
   Theory/Universal/Arrow.v's [AdjunctionFromUniversalArrows]
   delivers the functoriality as the [fmap] of the constructed
   left adjoint, and Instance/Mod/Free.v does exactly that
   ([FreeMod], with [free_module_adjunction] and
   [free_module_fmap_generators] recording that the induced action
   relabels basis vectors).  The citation is recorded here because
   this is the file the exercise's other half — the pointwise
   representability criterion — would be read against.
   nLab:      https://ncatlab.org/nlab/show/representable+functor
   nLab:      https://ncatlab.org/nlab/show/free+module
   Wikipedia: https://en.wikipedia.org/wiki/Representable_functor

   WHAT RIEHL ADDS TO THE FREE-MODULE CONSTRUCTION.  Instance/Mod/Free.v
   already proves that the free module on a generating setoid solves a
   universal mapping problem, and packages that as a [UniversalArrow]
   and an adjunction.  Riehl's Example 2.1.5(iv) says something that
   LOOKS like a corollary and is worth separating: the forgetful functor
   [RMod_Forget R] is REPRESENTABLE, and its representing object is R
   itself, the free module on ONE generator.  Two things are being
   claimed at once — that the ∃!-factorization property upgrades to a
   natural isomorphism of functors

   [Hom R,─]  ≅  RMod_Forget R      (in [RMod R, Sets])

   and that the representing object can be named on the nose as
   Instance/Mod.v's [Ring_RMod R], with no formal-sum carrier in sight.

   HOW IT IS PROVED, AND WHY NOT BY CITING THE FREE MODULE.  The route
   taken is the direct one: [ring_universal_element] exhibits [rig_one R]
   as a universal element of [RMod_Forget R] at [Ring_RMod R], because a
   module map out of R is determined by its value at 1 (h r ≈ h (r·1) ≈
   r · h 1) and every element m of every module is the value at 1 of the
   map r ↦ r·m.  That is four lines of module algebra and no formal sums.
   Routing through Instance/Mod/Free.v instead would have produced the
   representation at the object [FreeModObject SetsOne] — correct, but
   naming a quotient of formal expressions where Riehl names R.  What
   the free module then contributes is the COMPARISON, and it comes for
   free from the generic uniqueness machinery: [free_one_generator_iso]
   below is Theory/Universal/Element.v's [universal_element_iso] applied
   to the two universal elements, so “the free module on one generator
   is R” is a theorem here rather than a slogan, and it is proved
   without ever computing a normal form.

   WHAT IS DELIVERED.

   - [ring_universal_element], and its bundled form; the
   representation [rmod_representation] as a natural isomorphism in
   the functor category, and [rmod_representable] as an inhabitant
   of Functor/Representable.v's class;
   - the two Theory/Universal/Arrow.v encodings of the same content as
   a universal arrow from the one-point setoid;
   - [free_one_generator_iso], the canonical isomorphism between the
   free module on the singleton setoid and R, together with
   [free_one_generator_iso_unique] — the uniqueness clause, which is
   the part a bare [≅] would drop;
   - the witness at ℤ, where the represented set is the integers.

   WHAT IS NOT DELIVERED.  No claim that the representing object is
   unique on the nose (it is unique up to the unique isomorphism
   compatible with the universal elements, which is exactly what
   [universal_element_unique] gives and no more); no contravariant or
   enriched version; and no statement about [RMod_Forget_Ab], to which
   Functor/Representable.v's class does not even apply — that functor
   lands in [Ab], not in [Sets].  (Since #454 the Ab-level reading
   exists in general: Functor/Representable/Additive.v's [watt_ab_iso]
   upgrades a representation of [Ab_Forget ◯ T], for an additive
   Ab-valued T, to [HomAb A ≅ T] in the functor category into [Ab].
   It is not instantiated at [RMod_Forget_Ab] in this file;
   Instance/Mod/Watts.v's [watt_at_forget] instantiates it there, from
   this file's [rmod_representable], giving
   [HomAb (RMod_AbEnriched R) (Ring_RMod R) ≅ RMod_Forget_Ab R] with no
   hypothesis.) 

   --------
   * * R-模的底集合函子由 R 表示书籍：Riehl, 《Category Theory in Context》，第2版，第§2.1节
   示例 2.1.5(iv)，印刷版第56页（PDF第76-77页）—
   riehl:2.1:example5
   书籍：Mac Lane, 《Categories for the Working Mathematician》，第2版，
   §III.1节，印刷版第56页 — maclane:III.1:remark2
   书籍：Riehl, 《Category Theory in Context》，第2版，第§4.1节
   练习 4.1.v，印刷版第138页 —
   riehl:4.1:exv，该练习要求证明自由 R-模的构造在生成集合上是函子性的。这个练习在这里不需要工作，而且也没有进行：将自由模打包为 [UniversalArrow] 并输入到 Theory/Universal/Arrow.v 的 [AdjunctionFromUniversalArrows] 中，就会以构造的左伴随的 [fmap] 形式提供函子性，而 Instance/Mod/Free.v 正是这样做的（[FreeMod]，其中 [free_module_adjunction] 和 [free_module_fmap_generators] 记录了所引发的作用如何重新标记基向量）。引用之所以记录在这里，是因为这是练习的另一半——按点可表示性标准——将要参照阅读的文件。nLab: https://ncatlab.org/nlab/show/representable+functor  nLab: https://ncatlab.org/nlab/show/free+module  Wikipedia: https://en.wikipedia.org/wiki/Representable_functorRIEHL 对自由模构造的补充。Instance/Mod/Free.v 已经证明，在生成的集合等价类上的自由模解决一个普遍映射问题，并将其封装为一个 [UniversalArrow] 和一个伴随。Riehl 的例子 2.1.5(iv) 看起来像是一个推论，且值得单独提出：遗忘函子 [RMod_Forget R] 是可表示的，其表示对象就是 R 本身，即一个生成元的自由模。同时有两件事被断言——即存在唯一分解属性升级为函子自然同构

   [Hom R,─]   ≅  RMod_Forget R      (在 [RMod R, Sets] 中)

   并且表示对象可以直接命名为 Instance/Mod.v 的 [Ring_RMod R]，没有任何形式和的载体出现。如何证明，以及为什么不引用自由模。所采取的路径是直接的：[ring_universal_element] 展示 [rig_one R] 作为 [RMod_Forget R] 在 [Ring_RMod R] 的一个通用元素，因为从 R 出发的模映射由其在 1 的值决定（h r ≈ h (r·1) ≈ r · h 1），并且每个模的每个元素 m 都是映射 r ↦ r·m 在 1 的值。也就是说，这是四行模代数，没有形式和。改为通过 Instance/Mod/Free.v 路径将会在对象 [FreeModObject SetsOne] 处产生表示——这是正确的，但命名了一个 Riehl 命名为 R 的形式表达式的商。自由模随后贡献的是比较操作，它是从通用唯一性机制中免费获得的：下面的 [free_one_generator_iso] 是 Theory/Universal/Element.v 的 [universal_element_iso] 应用于两个通用元素，所以“一生成元的自由模是 R”在这里是一个定理而不是口号，而且它是在从未计算正规形式的情况下证明的。

   所交付的内容。- [ring_universal_element] 及其捆绑形式；在函子范畴中作为自然同构的表示 [rmod_representation]，以及作为 Functor/Representable.v 类的成员的 [rmod_representable]；
   - 两个 Theory/Universal/Arrow.v 对相同内容的编码，作为来自单元素集合的通用箭头；
   - [free_one_generator_iso]，即单元素集合上的自由模与 R 之间的典型同构，以及 [free_one_generator_iso_unique] — 唯一性条款，这是一个裸 [≅] 会忽略的部分；
   - 在 ℤ 上的见证，其中被表示的集合是整数。未提供的内容。没有声称表示对象在严格意义上是唯一的（它在与通用元素兼容的唯一同构下是唯一的，这正是 [universal_element_unique] 提供的，仅此而已）；没有协变或增强版本；也没有关于 [RMod_Forget_Ab] 的声明，Functor/Representable.v 的类甚至不适用于它——该函子落入 [Ab]，而不是 [Sets]。（自 #454 起，一般存在 Ab 级别的解释：Functor/Representable/Additive.v 的 [watt_ab_iso] 将对于加性 Ab 值的 T 的 [Ab_Forget ◯ T] 表示升级到 [HomAb A ≅ T]，在到 [Ab] 的函子范畴中）。它没有在此文件的 [RMod_Forget_Ab] 中实例化；
   Instance/Mod/Watts.v 的 [watt_at_forget] 在那里从
   此文件的 [rmod_representable] 实例化它，给出
   [HomAb (RMod_AbEnriched R) (Ring_RMod R) ≅ RMod_Forget_Ab R] 没有假设。)
*)

Section RingRepresents.

Context (R : RingObject).

(* * ** The module map determined by an element / * ** 由一个元素确定的模映射 *)

(*
   * For m in a module W, the map r ↦ r·m.  Each of the four obligations
   is a module law of W: respectfulness is [rm_smul_respects],
   preservation of zero is [rm_smul_zero_l], of sums
   [rm_smul_distr_r], and of the action [rm_smul_assoc] — the action of
   [Ring_RMod R] on itself BEING the multiplication of R. 

   --------
   * 对于模 W 中的元素 m，有映射 r ↦ r·m。 四个义务中的每一个都是 W 的模律：尊重性是 [rm_smul_respects]，零元的保持是 [rm_smul_zero_l]，加法的保持是 [rm_smul_distr_r]，作用的保持是 [rm_smul_assoc] —— [Ring_RMod R] 对自身的作用是 R 的乘法。
*)
Program Definition rmod_by_element (W : RModObject R)
  (m : carrier (cmon_setoid W)) : Ring_RMod R ~{RMod R}~> W := {|
  rm_hom := {| cmon_map := {| morphism := fun r => rm_smul W r m |} |}
|}.
Next Obligation.
  intros W m a b Hab; exact (rm_smul_respects W _ _ Hab _ _ (reflexivity m)).
Qed.
Next Obligation. intros W m; simpl; apply rm_smul_zero_l. Qed.
Next Obligation. intros W m a b; simpl; apply rm_smul_distr_r. Qed.
Next Obligation. intros W m r a; simpl; apply rm_smul_assoc. Qed.

(** A module map out of R is determined by its value at 1. / 从 R 映射出的模由其在 1 处的值决定。 *)
Lemma rmod_out_of_ring (W : RModObject R) (g : Ring_RMod R ~{RMod R}~> W)
  (r : carrier (rig_setoid R)) :
  cmon_map (rm_hom g) r
    ≈ rm_smul W r (cmon_map (rm_hom g) (rig_one R)).
Proof.
  transitivity (cmon_map (rm_hom g) (rig_mul R r (rig_one R))).
  - apply (proper_morphism (cmon_map (rm_hom g))).
    symmetry; apply rig_mul_one_r.
  - exact (rm_map_smul g r (rig_one R)).
Qed.

(** ** Riehl's Example 2.1.5(iv) / ** Riehl 的例子 2.1.5(iv) *)

(*
   * The unit of R is a universal element of the underlying-set functor.
   The factorization is [rmod_by_element], the commutation is
   [rm_smul_one], and the uniqueness is [rmod_out_of_ring]. 

   --------
   * R 的单位是基础集合函子的一种通用元素。
   因式分解是 [rmod_by_element]，交换是 [rm_smul_one]，唯一性是 [rmod_out_of_ring]。
*)
Definition ring_universal_element
  : AUniversalElement (RMod_Forget R) (Ring_RMod R).
Proof.
  unshelve econstructor.
  - exact (rig_one R).
  - intros W m.
    unshelve econstructor.
    + exact (rmod_by_element W m).
    + simpl; apply rm_smul_one.
    + intros g Hg r; simpl.
      symmetry.
      transitivity (rm_smul W r (cmon_map (rm_hom g) (rig_one R))).
      * exact (rmod_out_of_ring W g r).
      * exact (rm_smul_respects W _ _ (reflexivity r) _ _ Hg).
Defined.

Definition ring_universal_element_bundled : UniversalElement (RMod_Forget R) :=
  UniversalElement_of_AUniversalElement ring_universal_element.

(*
   * The representation as a NATURAL isomorphism in [[RMod R, Sets]] —
   Riehl's packaging, not merely the ∃! factorization property. 

   --------
   * 作为 [[RMod R, Sets] ] 中的一个自然同构的表示——Riehl 的封装，而不仅仅是 ∃! 分解性质。
*)
Definition rmod_representation
  : @Curried_Hom (RMod R) (Ring_RMod R) ≅[[RMod R, Sets]] RMod_Forget R :=
  ue_representation (RMod_Forget R) (Ring_RMod R) ring_universal_element.

Definition rmod_representable : Representable (RMod_Forget R) :=
  Representable_of_UniversalElement ring_universal_element_bundled.

(*
   * The same content as a universal arrow from the one-point setoid, in
   both of Theory/Universal/Arrow.v's encodings. 

   --------
   * 来自单点集合等价类的通用箭头的相同内容，在 Theory/Universal/Arrow.v 的两种编码中。
*)
Definition ring_auniversal_arrow
  : AUniversalArrow SetsOne (RMod_Forget R) (Ring_RMod R) :=
  AUniversalArrow_of_AUniversalElement (RMod_Forget R) (Ring_RMod R)
    ring_universal_element.

Definition ring_universal_arrow : UniversalArrow SetsOne (RMod_Forget R).
Proof.
  unshelve eapply
    (universal_arrow_from_UMP SetsOne (RMod_Forget R) (Ring_RMod R)).
  - exact (@universal_arrow _ _ _ _ _ ring_auniversal_arrow).
  - intros W f.
    unshelve econstructor.
    + exact (unique_obj (@universal_arrow_universal _ _ _ _ _
                           ring_auniversal_arrow W f)).
    + symmetry.
      exact (unique_property (@universal_arrow_universal _ _ _ _ _
                                ring_auniversal_arrow W f)).
    + intros v Hv.
      exact (uniqueness (@universal_arrow_universal _ _ _ _ _
                           ring_auniversal_arrow W f) v (symmetry Hv)).
Defined.

(*
   * ** The free module on one generator IS R

   Instance/Mod/Free.v's universal arrow at the singleton setoid is a
   universal element of the same functor, so the two representing
   objects are canonically isomorphic.  Nothing is computed: this is
   [universal_element_iso], and the uniqueness clause below is
   [universal_element_unique]. 

   --------
   * ** 单生成自由模是 R

   Instance/Mod/Free.v 中单元素集的通用箭头是同一函子下的一个通用元素，因此两个表示对象在典范意义上是同构的。没有进行任何计算：这是 [universal_element_iso]，下面的唯一性条款是 [universal_element_unique]。
*)

Definition free_one_universal_element
  : AUniversalElement (RMod_Forget R) (@FreeModObject R SetsOne) :=
  AUniversalElement_of_AUniversalArrow (RMod_Forget R)
    (@FreeModObject R SetsOne)
    (free_module_AUniversalArrow R SetsOne).

Definition free_one_generator_iso
  : @FreeModObject R SetsOne ≅[RMod R] Ring_RMod R :=
  universal_element_iso free_one_universal_element ring_universal_element.

(*
   * The isomorphism carrying the basis vector to 1 is the ONLY one: a
   bare [≅] would leave the free module's automorphisms in play. 

   --------
   * 将基向量映射到 1 的同构是唯一的：一个裸的 [≅] 会让自由模的自同构仍然起作用。
*)
Definition free_one_generator_iso_unique
  : Unique (fun i : @FreeModObject R SetsOne ≅[RMod R] Ring_RMod R =>
              fmap[RMod_Forget R] (to i)
                (@aue_elem _ (RMod_Forget R) _ free_one_universal_element)
                ≈ rig_one R) :=
  universal_element_unique free_one_universal_element ring_universal_element.

(*
   * The universal element of the free-module side is the basis vector at
   the unique point, definitionally. 

   --------
   * 自由模的一侧的通用元素是唯一点上的基向量，这是定义上的。
*)
Example free_one_universal_elem_is_generator :
  @aue_elem _ (RMod_Forget R) _ free_one_universal_element
    = @fv_gen R SetsOne ttt := eq_refl.

End RingRepresents.

(*
   * ** The witness at ℤ

   The represented set of the ℤ-module ℤ is the integers, and the
   mediating map is multiplication by the chosen integer, which
   computes. 

   --------
   * ** ℤ上的证人

   ℤ-模 ℤ 所表示的集合是整数，
   中介映射是乘以选定整数的映射，
   它会进行计算。
*)

Example int_universal_elem : @aue_elem _ (RMod_Forget Int_Ring) _
  (ring_universal_element Int_Ring) = 1%Z := eq_refl.

Example int_mediator_computes :
  cmon_map (rm_hom (rmod_by_element Int_Ring Int_RMod 5%Z)) 3%Z = 15%Z
  := eq_refl.
