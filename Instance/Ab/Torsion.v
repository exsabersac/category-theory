(*
   * * Torsion groups are coreflective in Ab, stated covariantly

   Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Springer GTM 5, §IV.3, printed p. 92 (PDF p. 101), read from the
   page image, catalog item maclane:IV.3:construction1: "A coreflective
   subcategory of Ab is the full subcategory of all torsion abelian
   groups (a group is torsion if all elements have finite order); the
   coreflector sends each abelian group A to the subgroup TA of all
   elements of finite order in A."  The definition is on printed p. 91
   (PDF p. 100): "Dually, A ⊂ B is coreflective in B when the inclusion
   functor A → B has a right adjoint."
   Riehl, "Category Theory in Context", §4.6, Example 4.6.13 (iii),
   printed p. 170 (PDF p. 190), read from the page image, for the other
   half of the pair: "The inclusion Ab_tf ↪ Ab of torsion-free abelian
   groups is reflective.  The reflector sends an abelian group A to the
   quotient A/TA by its torsion subgroup."  That half is #371's
   Instance/Ab/TorsionFree.v; Riehl does not list the coreflection.
   Riehl, §5.3, Exercise 5.3.ii, printed p. 197 (PDF p. 217), catalog
   item riehl:5.3:exii, is carried through at that reflection below.
   nLab: https://ncatlab.org/nlab/show/torsion+subgroup
   nLab: https://ncatlab.org/nlab/show/coreflective+subcategory

   BACKGROUND.  nLab's torsion-subgroup page defines the torsion
   subgroup of an abelian group as the subgroup of its elements of
   finite order, calls a group "pure torsion" when it coincides with it
   and "torsion-free" when it is trivial, and records that torsion and
   torsion-free classes of objects in an abelian category "were
   introduced axiomatically as a torsion theory (or torsion pair) in
   (Dickson 1963)".  The two halves of Mac Lane's page and exercise
   are the two sides of that pair in Ab: the torsion groups
   coreflective with coreflector A ↦ TA, the torsion-free groups
   reflective with reflector A ↦ A/TA.  This file is the first half;
   Instance/Ab/TorsionFree.v, whose header quotes the same paragraph,
   is the second.  That header was written before this file and lists
   this coreflection among what it does not deliver; its CORRECTION
   (#370) note there points here.

   WHAT IS DELIVERED, COVARIANTLY.  The reviewer's check for this item
   is that the coreflective example be stated covariantly, and it is:

   [torsion_coreflection : Incl Ab Torsion_Sub ⊣ torsion_coreflector]

   the inclusion LEFT adjoint to [torsion_coreflector : Ab ⟶
   TorsionCat], with no opposite category in its type.  It is built as
   a couniversal arrow per object: [torsion_couniversal] states the
   ∃!, whose arrow is the inclusion of TA ([torsion_incl], TorsionFree.v)
   and whose mediator [torsion_lift] corestricts a map out of a torsion
   group through TA, using that homomorphisms carry elements of finite
   order to elements of finite order with the same exponent
   ([torsion_map]); Theory/Universal/Arrow/Dual.v's
   [couniversal_arrow_from_UMP], [RightAdjointFunctorFromCouniversalArrows]
   and [AdjunctionFromCouniversalArrows] do the rest.  The record of
   Construction/Reflective.v, [Torsion_Coreflective : Coreflective
   Torsion_Sub], is then built from those covariant data by
   Construction/Reflective/Coreflective.v's [Coreflective_of_adjunction],
   and reading it back returns them on the nose (below).  The torsion
   predicate is #371's [torsion_mem], whose exponent is data; the
   subgroup is TorsionFree.v's [TorsionAb]; no choice principle is used.

   STRENGTHS, measured strict first.  Six [Example]s hold at
   [eq_refl]: the coreflection of A is TA ([torsion_coreflector_obj]);
   the couniversal arrow IS [torsion_incl A] ([torsion_coarrow_is_incl]);
   the counit applied to an element IS the inclusion applied to it
   ([torsion_counit_pointwise]); the record read back covariantly IS
   the covariant functor and adjunction ([torsion_record_coreflector],
   [torsion_record_adj], whole functor and whole adjunction); and the
   torsion-free monad at A is A/TA ([torsionfree_monad_obj]).  Falling
   back, each refusal pinned in Test/ProbeReflective370.v, whose import
   list carries this file's:
   - the counit as a morphism is only [≈] the inclusion
   ([torsion_counit_is_incl], from Dual.v's [counit_couniversal]).
   It is [torsion_incl A ∘ fmap[Incl] id] on the nose (accepted at
   [eq_refl]); against [torsion_incl A] its setoid-morphism
   component is refused at [eq_refl], and so is the whole record,
   with "cannot unify";
   CORRECTION (#1347): the setoid-morphism component now holds at
   [eq_refl] (the probe's N10, now a control), since Instance/Sets.v
   gives its identity's and composite's properness fields as terms;
   the whole record is still refused (N9);
   - the coreflector's arrow part is not [torsion_lift] on the nose:
   stating [fmap[torsion_coreflector] f] equal to the corestriction
   of [f ∘ torsion_incl A] is refused, the arrow part being the
   [unique_obj] of Theory/Universal/Arrow.v's [Qed]-closed
   [ump_universal_arrows] read in the opposite categories.

   NON-VACUITY.  ℤ/2 (Instance/Ab/Character/Finite.v's [ZMod2]) is
   torsion, so it is an object of the subcategory ([ZMod2_Torsion]) and
   the unit there is invertible ([ZMod2_coreflect_iso], Coreflective.v's
   [coreflective_unit_iso]).  ℤ × ℤ/2 (TorsionFree.v's [MixedAb]) is not
   torsion ([MixedAb_not_torsion]); its torsion part is not trivial
   ([mixed_tors_in_TA], [mixed_tors_in_TA_nonzero]); and the counit
   there is not invertible ([torsion_counit_MixedAb_not_iso]): an
   inverse would carry the generator (1, 0) into TA and make it torsion.
   At ℤ the torsion part is trivial ([ZAb_TA_trivial]).

   RIEHL 5.3.ii, AT THE TORSION-FREE REFLECTION.  #371's
   [TorsionFree_Reflective] is fed to Construction/Reflective/
   Idempotent.v: [TorsionFree_Monad], [TorsionFree_IdempotentMonad],
   and [TorsionFree_EM_MLocal], which is [Idempotent_EM_Equivalence]
   verbatim, the algebras equivalent to the monad's M-LOCAL objects.
   Riehl's Proposition 5.3.3 (ii) asks for the subcategory itself, and
   Construction/Reflective/Monadic.v supplies it:
   [TorsionFree_EM_Equivalence] (the comparison functor from
   [TorsionFree_Sub] is an equivalence) and [TorsionFree_Incl_Monadic].

   UNIVERSES, read by [About] under [Set Printing Universes] on all
   thirty-four named constants.  Each binder names the levels its
   statement fixes, then [+]: [u p] for [Ab@{u p}]; [a c p] for
   [IsTorsion] over [AbObject@{a c p}] (a fourth level, the result
   sort, is left to [+]); [p] for [TorsionAb_IsTorsion] over
   [AbObject@{p p p}], the only shape at which TorsionFree.v states
   the inclusion [torsion_incl] its proof uses; [a] for
   [ZMod2_IsTorsion]; [u] for the two ℤ/2 statements and the counit
   statement over [Ab@{u Set}]; and none, [@{+}], for
   [MixedAb_not_torsion], [mixed_tors_in_TA], its lemma and
   [ZAb_TA_trivial], whose levels are all their donors'.  No
   block carries an equation.  Thirty-one blocks carry an own [Set]
   bound: twenty-seven [Set < u] on [Ab]'s object level, which is
   [Ab]'s own bound ([About Ab]: [Set < u]; the [PropEquiv] field puts
   [Set+1] in [AbObject]'s sort), and four on a level only a donor
   names -- [TorsionAb_IsTorsion] through the [Ab] instance of
   [torsion_incl] in its proof, and [MixedAb_not_torsion],
   [mixed_tors_in_TA] and its lemma through [MixedAb]'s own
   [Set < u2] ([MixedAb_not_torsion@{u}] reads [¬ IsTorsion
   MixedAb@{Set u u u Set Set Set}] with [Set < u], and never mentions
   [Ab]).  Seven witnesses print [Set] in their instances --
   [ZMod2_IsTorsion], [ZMod2_Torsion], [ZMod2_coreflect_iso],
   [MixedAb_not_torsion], [mixed_tors_in_TA], its lemma and
   [torsion_counit_MixedAb_not_iso] -- because
   [ZMod2@{u} : AbObject@{u Set Set}] ([About ZMod2]; its carrier is
   [bool]).  Six blocks read [Set < Projections.u0], which in each
   follows from an own [Set] bound and the block's caps, and every
   global universe in every block is an upper bound.  Against a copy
   with every binder removed, compared under [Set Printing All], no
   constant lost a universe or gained an identification.

   AXIOMS.  All thirty-seven constants of this module, the thirty-four
   above and three [Program] obligations of [torsion_lift], are closed
   under the global context.

   NOT DELIVERED.
   - Nothing about torsion theories in general, and no statement
   that the torsion and torsion-free classes form one.
   - No idempotent comonad of the coreflection beyond what
   Construction/Reflective/FixedPoints.v's op-form
   [Coreflective_IdempotentMonad_op] gives when applied to
   [Torsion_Coreflective]; that application is not made here.
   - The coreflector's arrow part and the unit are not read back on
   the nose; only the counit is, pointwise.
   - No [Grp] analogue, and no p-primary refinement. 

   --------
   * * 扭力群在阿贝尔群中是余反射的，以协变形式表述麦克兰，《从事数学工作的数学家的范畴》，第2版，Springer GTM 5，第IV.3节，印刷版第92页（PDF第101页），根据页面图像阅读，目录条目 maclane:IV.3:construction1: “Ab 的一个余反射子范畴是所有挠性阿贝尔群的满子范畴（一个群是挠性群当且仅当其所有元素的阶均为有限）；余反射函子将每个阿贝尔群 A 发送到 A 中所有有限阶元素组成的子群 TA。” 定义见印刷版第91页（PDF第100页）：“对偶地，当包含函子 A → B 具有右伴随时，A ⊂ B 在 B 中是余反射的。” 里尔，《背景下的范畴论》，第4.6节，例4.6.13 (iii)，印刷版第170页（PDF第190页），根据页面图像阅读，配对的另一半为：“挠自由阿贝尔群的包含 Ab_tf ↪ Ab 是反射的。”反射子将阿贝尔群 A 发送到它的挠子子群所除的商群 A/TA。那一半是 #371 的 Instance/Ab/TorsionFree.v；Riehl 没有列出余反射。Riehl，第 5.3 节，练习 5.3.ii，印刷页 197（PDF 页 217），目录项 riehl:5.3:exii，在下面的反射中展开。nLab:  https://ncatlab.org/nlab/show/torsion+subgroup nLab:  https://ncatlab.org/nlab/show/coreflective+subcategory背景。nLab 的扭子子群页面将阿贝尔群的扭子子群定义为其有限阶元素的子群，当群与其重合时称该群为“纯扭子”，当其平凡时称为“无扭子”，并记录了在阿贝尔范畴中扭子类和无扭子类的对象“在 (Dickson 1963) 中被公理化地引入作为扭子理论（或扭子对）”。Mac Lane 页面和练习的两部分是 Ab 中该对的两侧：扭子群是共反射的，共反射子 F 将 A 映射为 TA，无扭子群是反射的，反射子将 A 映射为 A/TA。此文件是前半部分；Instance/Ab/TorsionFree.v，其标题引用了同一段落，是后半部分。该标题是在此文件之前编写的，并列出了它未提供的内容；其纠正（#370）注释指出了这一点。

   所提供的内容，共变的。审阅者对该项目的检查是核对关联示例是否以共变方式陈述，而它确实是：

   [torsion_coreflection : Incl Ab Torsion_Sub ⊣ torsion_coreflector]包含作为 [torsion_coreflector : Ab ⟶ TorsionCat] 的左伴随函数，其类型中没有对偶范畴。它被构建为每个对象的余普遍箭头：[torsion_couniversal] 陈述了 ∃!，其箭头是 TA ([torsion_incl], TorsionFree.v) 的包含，其中介 [torsion_lift] 通过 TA 对扭结群的映射进行余限制，使用了同态将有限阶的元素映射为相同指数的有限阶元素（[torsion_map]）；Theory/Universal/Arrow/Dual.v 的 [couniversal_arrow_from_UMP]、[RightAdjointFunctorFromCouniversalArrows] 和 [AdjunctionFromCouniversalArrows] 完成了其余部分。然后，Construction/Reflective.v 的记录 [Torsion_Coreflective : Coreflective Torsion_Sub] 就是从这些协变数据通过 Construction/Reflective/Coreflective.v 的 [Coreflective_of_adjunction] 构建的，读取它返回的数据正好与原数据一致（如下）。扭转谓词是 #371 的 [torsion_mem]，其指数是数据；子群是 TorsionFree.v 的 [TorsionAb]；未使用选择公理。优点，严格顺序测量。六个 [Example] 在 [eq_refl] 处保持：A 的核心反射是 TA ([torsion_coreflector_obj])；余普遍箭头是 [torsion_incl A] ([torsion_coarrow_is_incl])；将余单位应用于一个元素就是将其包含应用于它 ([torsion_counit_pointwise])；共变方式读回的记录是共变函子和挨附 ([torsion_record_coreflector], [torsion_record_adj], 整个函子和整个挨附)；A 处的无挠单子是 A/TA ([torsionfree_monad_obj])。回退，每个在 Test/ProbeReflective370.v 中固定的拒绝，其导入列表带有此文件的：- 余单位作为态射仅是 [≈] 包含 ([torsion_counit_is_incl]，来自 Dual.v 的 [counit_couniversal])。它在表面上是 [torsion_incl A ∘ fmap[Incl] id]（在 [eq_refl] 被接受）；对于 [torsion_incl A]，它的集体态射组件在 [eq_refl] 被拒绝，整个记录也是如此，显示“无法统一”；
   修正 (#1347)：集体态射组件现在在 [eq_refl]（探针的 N10，现在是控制）上成立，因为 Instance/Sets.v 给出了其恒等和复合的正确性字段作为项；
   整个记录仍被拒绝（N9）；
   - 核反射器的箭头部分在表面上不是 [torsion_lift]：声明 [fmap[torsion_coreflector] f] 等于 [f ∘ torsion_incl A] 的余限制被拒绝，箭头部分是 Theory/Universal/Arrow.v 的 [Qed] 封闭 [ump_universal_arrows]，在相反类别中读取。非空性。ℤ/2（Instance/Ab/Character/Finite.v 的 [ZMod2]）是挠性，因此它是子范畴（[ZMod2_Torsion]）的一个对象，并且那里的单位是可逆的（[ZMod2_coreflect_iso]，Coreflective.v 的 [coreflective_unit_iso]）。ℤ × ℤ/2（TorsionFree.v 的 [MixedAb]）不是挠性（[MixedAb_not_torsion]）；它的挠部分不是平凡的（[mixed_tors_in_TA]，[mixed_tors_in_TA_nonzero]）；而且那里的余单位不可逆（[torsion_counit_MixedAb_not_iso]）：一个逆会将生成元 (1, 0) 送入 TA 并使其成为挠元素。在 ℤ 处，挠部分是平凡的（[ZAb_TA_trivial]）。RIEHL 5.3.ii，无扭反射。#371 的 [TorsionFree_Reflective] 被输入到 Construction/Reflective/Idempotent.v：[TorsionFree_Monad]、[TorsionFree_IdempotentMonad] 和 [TorsionFree_EM_MLocal]，即逐字的 [Idempotent_EM_Equivalence]，该代数与该 monad 的 M-LOCAL 对象等价。Riehl 的命题 5.3.3 (ii) 需要子范畴本身，而 Construction/Reflective/Monadic.v 提供了它：[TorsionFree_EM_Equivalence]（来自 [TorsionFree_Sub] 的比较函子是一个等价函子）和 [TorsionFree_Incl_Monadic] 。UNIVERSES，由 [About] 在 [Set Printing Universes] 下读取，在所有三十四个命名常量上。每个绑定器命名其语句固定的层级，然后 [+]：[u p] 对于 [Ab@{u p}]；[a c p] 对于 [IsTorsion] 在 [AbObject@{a c p}] 上（第四个层级，结果类型，由 [+] 留下）；[p] 对于 [TorsionAb_IsTorsion] 在 [AbObject@{p p p}] 上，这是 TorsionFree.v 在其证明中使用包含关系 [torsion_incl] 的唯一形状；[a] 对于 [ZMod2_IsTorsion]；[u] 对于两个 ℤ/2 语句和 [Ab@{u Set}] 上的余单位语句；没有，[@{+}]，对于 [MixedAb_not_torsion]、[mixed_tors_in_TA]，它的引理和 [ZAb_TA_trivial]，其层级均为其捐赠者的层级。没有区块携带方程。三十一块携带自己的 [Set] 绑定：二十七块 [Set < u] 位于 [Ab] 的对象层次上，这是 [Ab] 自己的绑定（ZWZ79WZZ：ZWZ80WZZ；ZWZ81WZZ 字段将 ZWZ82WZZ 放入 ZWZ83WZZ 的排序中），还有四个仅在捐赠者命名的层次上——ZWZ84WZZ 通过 ZWZ85WZZ 的 ZWZ86WZZ 实例在其证明中，以及 ZWZ87WZZ、ZWZ88WZZ 及其引理通过 ZWZ89WZZ 自己的 ZWZ90WZZ（ZWZ91WZZ 读取 [¬ IsTorsion MixedAb@{Set u u u Set Set Set}] 与 ZWZ92WZZ，并且从未提到 ZWZ93WZZ）。七个见证人在他们的实例中打印 ZWZ94WZZ——ZWZ95WZZ、ZWZ96WZZ、ZWZ97WZZ、ZWZ98WZZ、ZWZ99WZZ，其引理和 ZWZ100WZZ——因为 ZWZ101WZZ（ZWZ102WZZ；其承载者是 ZWZ103WZZ）。六个区块显示 [Set < Projections.u0]，其中每个区块都遵循其自身的 [Set] 上界和区块的上限，并且每个区块中的每个全局宇宙都是一个上界。与移除了每个绑定器的副本在 [Set Printing All] 下比较时，没有任何常量失去宇宙或获得识别。

   公理。 本模块的全部三十七个常量，即上述的三十四个常量和三个 [Program] 的 [torsion_lift] 义务，在全局上下文下都是封闭的。未交付。
   - 完全没有关于挠理论的内容，也没有说明挠类和无挠类形成一个挠理论。
   - 除了 Construction/Reflective/FixedPoints.v 的对偶形式 [Coreflective_IdempotentMonad_op] 在应用于 [Torsion_Coreflective] 时给出的内容之外，没有核心反射的幂等协同单子；这里没有进行该应用。
   - 核心反射的箭头部分和单位态没有被直接读取；只有辅单位被逐点读取。
   - 没有 [Grp] 的类比，也没有 p-主要精细化。
*)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Monad.Comparison.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.Coreflective.
Require Import Category.Construction.Reflective.Monadic.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Ab.Character.Finite.
Require Import Category.Adjunction.Unitalization.
Require Import Category.Instance.Ab.TorsionFree.

Generalizable All Variables.

(* * ** The full subcategory of torsion groups / * ** 拥有全子范畴的扭群 *)

Definition IsTorsion@{a c p +} (A : AbObject@{a c p}) : Type :=
  ∀ x : carrier A, torsion_mem A x.

Definition Torsion_Sub@{u p +} : Subcategory Ab@{u p} :=
  @Build_Subcategory Ab@{u p} IsTorsion
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition TorsionCat@{u p +} : Category := Sub Ab@{u p} Torsion_Sub.

Definition Torsion_Full@{u p +} :
  Category.Construction.Subcategory.Full Ab@{u p} Torsion_Sub :=
  fun _ _ _ _ _ => I.

(* TA is torsion. Equality in the subgroup compares first projections, so the exponent of a member is the exponent it was built with. / TA 是扭转。在子群中比较的是第一个投影的相等性，因此成员的指数就是它被构建时的指数。 *)
Definition TorsionAb_IsTorsion@{p +} (A : AbObject@{p p p}) :
  IsTorsion (TorsionAb A).
Proof.
  intros [a [k [Hk Hka]]].
  exists k; split; [ exact Hk | ].
  pose proof (nat_smul_hom (torsion_incl A) k
                (existT _ a (existT _ k (Hk, Hka)))) as E.
  simpl in E |- *.
  exact (transitivity E Hka).
Defined.

(* Mac Lane's TA, as an object of the subcategory. / 作为子范畴的对象，Mac Lane 的 TA。 *)
Definition TorsionPart@{u p +} (A : Ab@{u p}) : TorsionCat :=
  (TorsionAb A; TorsionAb_IsTorsion A).

(* * ** The couniversal property of the torsion subgroup / * ** 孤子子群的共通性质 *)

(* A homomorphism carries an element of finite order to one of finite order, with the same exponent. / 同态将有限阶的元素映射到具有相同指数的有限阶元素。 *)
Definition torsion_map@{u p +} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (a : carrier A) :
  torsion_mem A a → torsion_mem B (cmon_map f a).
Proof.
  intros [k [Hk Hka]].
  exists k; split; [ exact Hk | ].
  rewrite <- nat_smul_hom, Hka.
  apply cmon_map_zero.
Defined.

(* The mediator: a homomorphism out of a torsion group lands in TA. / 中介：从挠子群出的同态映射落在TA中。 *)
Program Definition torsion_lift@{u p +} {T A : Ab@{u p}} (HT : IsTorsion T)
  (f : T ~{Ab@{u p}}~> A) : T ~{Ab@{u p}}~> TorsionAb A :=
  {| cmon_map := {| morphism := fun t : carrier T =>
       existT _ (cmon_map f t) (torsion_map f t (HT t)) |} |}.
Next Obligation. intros x y Hxy; simpl; now rewrite Hxy. Qed.
Next Obligation. simpl; apply cmon_map_zero. Qed.
Next Obligation. simpl; apply cmon_map_plus. Qed.

Theorem torsion_couniversal@{u p +} (A : Ab@{u p}) :
  ∀ (d : TorsionCat) (f : Incl Ab@{u p} Torsion_Sub d ~{Ab@{u p}}~> A),
    ∃! g : d ~{TorsionCat}~> TorsionPart A,
      f ≈ torsion_incl A ∘ fmap[Incl Ab@{u p} Torsion_Sub] g.
Proof.
  intros d f.
  unshelve eexists.
  - exact (torsion_lift `2 d f; I).
  - intro a; simpl; reflexivity.
  - intros g Hg a; simpl.
    exact (Hg a).
Defined.

Definition torsion_couniversal_arrow@{u p +} (A : Ab@{u p})
  : @CouniversalArrow Ab@{u p} TorsionCat A (Incl Ab@{u p} Torsion_Sub) :=
  @couniversal_arrow_from_UMP Ab@{u p} TorsionCat A (Incl Ab@{u p} Torsion_Sub)
    (TorsionPart A) (torsion_incl A) (torsion_couniversal A).

(* * ** The coreflection, stated covariantly / * ** 核反射，协变地表示 *)

Definition torsion_coreflector@{u p +} : Ab@{u p} ⟶ TorsionCat :=
  RightAdjointFunctorFromCouniversalArrows (Incl Ab@{u p} Torsion_Sub)
    torsion_couniversal_arrow.

(* Mac Lane's "coreflective": the inclusion has a RIGHT adjoint. / Mac Lane 的“余反射”：该包含函子有一个右伴随。 *)
Definition torsion_coreflection@{u p +} :
  Incl Ab@{u p} Torsion_Sub ⊣ torsion_coreflector :=
  AdjunctionFromCouniversalArrows (Incl Ab@{u p} Torsion_Sub)
    torsion_couniversal_arrow.

(* The packaged record of Construction/Reflective.v, built from the covariant data through Construction/Reflective/Coreflective.v. / Construction/Reflective.v 的打包记录，是从 Construction/Reflective/Coreflective.v 中的协变数据构建的。 *)
Definition Torsion_Coreflective@{u p +} : @Coreflective Ab@{u p} Torsion_Sub :=
  Coreflective_of_adjunction Torsion_Full torsion_coreflector
    torsion_coreflection.

(* * ** Readbacks: the counit is the inclusion of TA / * ** 回读：余单位是 TA 的包含 *)

Example torsion_coreflector_obj@{u p +} (A : Ab@{u p}) :
  `1 (fobj[torsion_coreflector] A) = TorsionAb A := eq_refl.

Example torsion_coarrow_is_incl@{u p +} (A : Ab@{u p}) :
  @coarrow Ab@{u p} TorsionCat A (Incl Ab@{u p} Torsion_Sub)
    (torsion_couniversal_arrow A)
    = torsion_incl A := eq_refl.

Definition torsion_counit@{u p +} (A : Ab@{u p})
  : Incl Ab@{u p} Torsion_Sub (fobj[torsion_coreflector] A) ~{Ab@{u p}}~> A :=
  @counit _ _ _ _ torsion_coreflection A.

Example torsion_counit_pointwise@{u p +} (A : Ab@{u p})
  (x : carrier (TorsionAb A)) :
  cmon_map (torsion_counit A) x = cmon_map (torsion_incl A) x := eq_refl.

Lemma torsion_counit_is_incl@{u p +} (A : Ab@{u p}) :
  torsion_counit A ≈ torsion_incl A.
Proof.
  exact (counit_couniversal (Incl Ab Torsion_Sub)
           torsion_couniversal_arrow A).
Qed.

(*
 Read back from the record, the coreflector and the adjunction are the
 covariant ones on the nose. 

 --------
 从记录中回读，核心反射器和附加是准确的协变。
*)
Example torsion_record_coreflector@{u p +} :
  @coreflector Ab@{u p} Torsion_Sub Torsion_Coreflective
    = torsion_coreflector := eq_refl.

Example torsion_record_adj@{u p +} :
  @coreflective_adj Ab@{u p} Torsion_Sub Torsion_Coreflective
    = torsion_coreflection := eq_refl.

(** ** Non-vacuity / ** 非空性 *)

(*
 ℤ/2 is torsion, so it is an object of the subcategory, and the unit of
 the coreflection there is invertible. 

 --------
 ℤ/2 是挠子群，因此它是该子范畴的一个对象，并且那里的余反射的单位是可逆的。
*)
Definition ZMod2_IsTorsion@{a +} : IsTorsion (ZMod2 : AbObject@{a Set Set}) :=
  ZMod2_all_torsion.

Definition ZMod2_Torsion@{u +} : Sub Ab@{u Set} Torsion_Sub :=
  (ZMod2; ZMod2_IsTorsion).

Definition ZMod2_coreflect_iso@{u +} :
  ZMod2_Torsion ≅[Sub Ab@{u Set} Torsion_Sub]
    fobj[coreflector Torsion_Coreflective]
      (fobj[Incl Ab@{u Set} Torsion_Sub] ZMod2_Torsion) :=
  coreflective_unit_iso Torsion_Coreflective ZMod2_Torsion.

(* ℤ × ℤ/2 is not torsion... / ℤ × ℤ/2 不是挠子... *)
Lemma MixedAb_not_torsion@{+} : IsTorsion MixedAb → False.
Proof. intro H; exact (mixed_gen_not_torsion (H mixed_gen)). Qed.

(* ...its torsion part is not trivial... / ...它的扭转部分并不平凡... *)
Definition mixed_tors_in_TA@{+} : carrier (TorsionAb MixedAb) :=
  existT _ mixed_tors mixed_tors_torsion.

Lemma mixed_tors_in_TA_nonzero@{+} :
  @equiv (carrier (TorsionAb MixedAb)) _ mixed_tors_in_TA
    (cmon_zero (TorsionAb MixedAb)) → False.
Proof. exact mixed_tors_not_zero. Qed.

(* ...and the counit there is not invertible: an inverse would carry the generator (1, 0) into TA and back, making it torsion. / ...并且那里余单位不可逆：一个逆元素会将生成元 (1, 0) 带入 TA 再带回来，使其成为扭元素。 *)
Theorem torsion_counit_MixedAb_not_iso@{u +} :
  IsIsomorphism (torsion_counit (MixedAb : Ab@{u Set})) → False.
Proof.
  intros [g Hfg _].
  apply mixed_gen_not_torsion.
  apply (torsion_resp MixedAb (projT1 (cmon_map g mixed_gen)) mixed_gen).
  - exact (Hfg mixed_gen).
  - exact (projT2 (cmon_map g mixed_gen)).
Qed.

(* The same at ℤ: its torsion part is trivial. / 在ℤ中也是一样：它的扭部分是平凡的。 *)
Lemma ZAb_TA_trivial@{+} (x : carrier (TorsionAb ZAb)) :
  @equiv (carrier (TorsionAb ZAb)) _ x (cmon_zero (TorsionAb ZAb)).
Proof. exact (ZAb_torsion_trivial (projT1 x) (projT2 x)). Qed.

(* * ** Riehl 5.3.ii at the torsion-free reflection (Mac Lane §IV.3 Ex. 2) / * ** Riehl 5.3.ii 在无扭反射处（Mac Lane §IV.3 练习 2） *)

Definition TorsionFree_Monad@{u p +} :
  @Monad Ab@{u p} (Incl Ab@{u p} TorsionFree_Sub ◯ TorsionFree_reflector) :=
  Reflective_Monad TorsionFree_Reflective.

Definition TorsionFree_IdempotentMonad@{u p +} :
  @IdempotentMonad Ab@{u p}
    (Incl Ab@{u p} TorsionFree_Sub ◯ TorsionFree_reflector)
    TorsionFree_Monad :=
  Reflective_IdempotentMonad TorsionFree_Reflective.

Example torsionfree_monad_obj@{u p +} (A : Ab@{u p}) :
  fobj[Incl Ab@{u p} TorsionFree_Sub ◯ TorsionFree_reflector] A
    = AbModTorsion A
  := eq_refl.

(*
 Idempotent.v's correspondence, fed a concrete record: the algebras of
 the induced monad are equivalent to its M-local objects... 

 --------
 Idempotent.v 的对应关系，输入一个具体记录：诱导幺半群的代数与其 M-局部对象是等价的…
*)
Definition TorsionFree_EM_MLocal@{u p +} :
  EquivalenceOfCategories
    (@idem_G Ab@{u p} _ TorsionFree_Monad TorsionFree_IdempotentMonad) :=
  @Idempotent_EM_Equivalence Ab@{u p} _ TorsionFree_Monad
    TorsionFree_IdempotentMonad.

(* ...and, Riehl's Proposition 5.3.3 (ii), to the subcategory itself. / ...以及，Riehl 的命题 5.3.3 (ii)，对于子范畴自身。 *)
Definition TorsionFree_EM_Equivalence@{u p +} :
  EquivalenceOfCategories
    (@reflective_comparison Ab@{u p} _ TorsionFree_Reflective) :=
  Reflective_EM_Equivalence TorsionFree_Reflective.

Definition TorsionFree_Incl_Monadic@{u p +} :
  Monadic (Incl Ab@{u p} TorsionFree_Sub) :=
  Reflective_Monadic TorsionFree_Reflective.
