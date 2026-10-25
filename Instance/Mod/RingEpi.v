Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Coproduct.
Require Import Category.Instance.Rng.Mod.
Require Import Category.Instance.Mod.Extension.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Monad.Comparison.
Require Import Category.Adjunction.FullFaithful.

Generalizable All Variables.

Open Scope category_scope.

(* * * Ring epimorphisms, restriction of scalars, and T-Mod in R-Mod / * * 环上同态满射、标量限制，以及 R-模中的 T-模 *)

(*
 nLab:  https://ncatlab.org/nlab/show/reflective+subcategory
 nLab:  https://ncatlab.org/nlab/show/restriction+of+scalars
 nLab:  https://ncatlab.org/nlab/show/epimorphism
 nLab:  https://ncatlab.org/nlab/show/localization+of+a+commutative+ring
 Book:  Riehl, "Category Theory in Context", Dover 2016, §4.6,
 Example 4.6.13 (iv), printed p. 170 (PDF p. 190) — catalog
 item riehl:4.6:example13, appended to issue #370
 Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 GTM 5, §IV.3, printed p. 92 (PDF p. 101) — the section whose
 examples issue #370 collects
 Docs:  The Stacks Project, Tag 04VM (§10.107, "Epimorphisms of
 rings") — the commutative-algebra account

 WHERE THIS COMES FROM.  Mac Lane's examples on p. 92 open "Here are
 some examples.  Ab is reflective in Grp." and go on to metric spaces,
 topological spaces and torsion groups; no module category is among
 them.  Issue #370
 also collects Riehl's roster of reflective subcategories, whose
 clause (iv) reads, quoted from the page image of p. 170:

 "As described in Example 4.1.10(xii), for any ring homomorphism
 φ: R → T, there exist adjoint functors [displayed: T ⊗_R − ⊣ φ*]
 the right adjoint being restriction of scalars and the left
 adjoint being extension of scalars.  The restriction of scalars
 functor is always faithful ... and is full if and only if
 φ: R → T is an epimorphism.  For such homomorphisms, restriction
 of scalars identifies _T Mod as a reflective subcategory of
 _R Mod.  Epimorphisms in Ring include all surjections but are not
 limited to the surjections.  The localizations define another important
 class of epimorphisms. ... The localization R → R[S⁻¹] is an
 initial object in the category whose objects are ring
 homomorphisms R → T that carry all of the elements of S to units
 in T."

 (The elided clause gives the reason for faithfulness: both module
 categories are faithful over Ab.)  This file is that clause.

 THE MATHEMATICS.  Restriction of scalars along φ changes no abelian
 group and no map; it forgets how T acts.  Fullness therefore says
 that every R-linear map between T-modules is automatically T-linear:
 the action of T is DETERMINED by that of R.  An epimorphism is the
 ring-level form of the same idea — a map out of T is determined by
 its composite with φ — and the two are equivalent.

 One direction is short.  If restriction is full, take ring maps
 g1, g2 : T → S with g1 φ ≈ g2 φ, make S a T-module twice (along g1
 and along g2), and observe that the identity of S is R-linear between
 the two; fullness makes it T-linear, and T-linearity at t · 1 says
 g1 t ≈ g2 t ([Restrict_Full_Epic]).

 The other direction, which Riehl states without proof, has a
 standard proof that is a trick worth recording.  Given T-modules M
 and N and an R-linear additive map f : M → N, work in the ring
 End(M ⊕ N) of additive endomorphisms of the direct sum
 ([AbEndRing]).  T acts on M ⊕ N diagonally, a ring map
 ρ : T → End(M ⊕ N) ([module_rep]).  The shear
 σ(m, n) = (m, n + f m) is an automorphism ([shear_iso]), and
 conjugating ρ by σ gives a second ring map ρ' = σ ρ σ⁻¹
 ([twisted_rep], through [EndRig_conj]), which computes to
 t ↦ ((m, n) ↦ (t m, t (n - f m) + f (t m))).  The two agree at t
 exactly when f commutes with t ([twist_fixed_of_linear],
 [linear_of_twist_fixed]).  R-linearity makes them agree after φ;
 φ epi makes them agree; so f is T-linear ([Epic_Restrict_Full]).

 WHAT IS DELIVERED.

 - [Restrict_Faithful], [Restrict_Full_Epic], [Epic_Restrict_Full] and
 [Restrict_Full_iff_Epic]: Riehl's "always faithful, and full if and
 only if φ is an epimorphism", for ARBITRARY rings R and T and any
 ring map φ.  No commutativity is assumed anywhere.
 - [TMod_Reflective_in_RMod], with its adjunction as its own constant
 [TMod_adj]: for φ epi WITH [CentralImage φ], T-Mod is reflective in
 R-Mod, with extension of scalars as reflector.
 The subcategory is [UnitFixed] of Instance/Mod/Extension.v's
 adjunction (Construction/Reflective/FixedPoints.v): the R-modules
 at which the unit M → Restrict (T ⊗ M) is invertible.  The record
 comes from [unit_fixed_reflective_of_idempotent], the induced monad
 being idempotent because the counit is invertible
 ([restrict_counit_iso], from Adjunction/FullFaithful.v's
 [right_adjoint_fully_faithful_iff_counit_iso]).
 - [Restrict_UnitFixed] and [TMod_equiv_UnitFixed]: restriction lands
 in that subcategory and is an equivalence onto it — full, faithful
 and essentially surjective, through Theory/Equivalence/
 FullFaithful.v's [FF_ESO_Equivalence] — which is what Riehl's
 "identifies T Mod as a reflective subcategory" means here.
 - [QMod_Reflective_in_ZMod], [QMod_equiv_UnitFixed] and
 [Restrict_ZtoQ_Full]: the instance at ℤ → ℚ, with no hypothesis
 left: Instance/Rng.v's [ZtoQ_epic] and Instance/Mod/Extension.v's
 [Q_central] discharge both.  Its modules are those of
 [RMod Int_Ring@{Set Set Set}]: Instance/Rng.v's [ZtoQ] is pinned at
 carrier level [Set] (UNIVERSES, below).
 - [ZMod_not_UnitFixed]: that reflection is proper.  ℤ, as a module
 over itself, is not in the subcategory: an inverse g of the unit η
 at ℤ would be ℤ-linear, η 1 = 1 ⊗ 1 is twice the element
 (1/2) · (1 ⊗ 1) of the ℚ-module ℚ ⊗ ℤ, and so 1 = g (η 1) would be
 even ([lia] closes the parity).
 - [InvertsSet], [IsLocalization] and [localization_epic]: a ring map
 initial among those inverting a family S is an epimorphism, for any
 S (Riehl's multiplicative closure is not needed).  Only the
 uniqueness half of the universal property is spent.
 - [ZtoQ_IsLocalization]: ℤ → ℚ is the localization at the positive
 integers, into any ring W at carrier level [Set], commutative or
 not.  The level is [ZtoQ]'s, which Instance/Rng.v pins at [Set]
 ([About ZtoQ_IsLocalization] reads [IsLocalization@{u0 Set u1 u
 u1} ZtoQ@{u0} PosZ@{u1}], the second universe being the rings'
 level); the mediator [loc_hom] itself is level-generic.  [loc_hom]
 sends a/b to ψ a · (ψ b)⁻¹, well defined because the image of ℤ
 commutes ([loc_images_commute]).  Uniqueness is proved directly, by
 cancelling ψ b ([loc_hom_unique]), and NOT through [ZtoQ_epic], so
 [ZtoQ_epic_of_localization] is an independent second proof of
 Instance/Rng.v's [ZtoQ_epic].

 STRENGTHS, MEASURED STRICT FIRST.  At [eq_refl]: the preimage that
 fullness returns IS the given additive map
 ([Epic_Restrict_Full_prefmap]: nothing is rebuilt); the twisted
 action computes on pairs ([twisted_rep_value]); the reflector's
 module at M IS [RestrictObj φ (ExtendObj φ Hc M)]
 ([TMod_reflector_obj]); the unit at m IS Riehl's 1 ⊗ m, that is
 [ext_gen φ M 1 m] ([TMod_unit_pointwise]); the inclusion after
 [Restrict_UnitFixed] IS restriction on objects
 ([Restrict_UnitFixed_incl]).  Refused at [eq_refl], pinned in
 Test/ProbeReflective370.v rather than here (a negative probe line in
 this file would add to [make todo]): the unit as a whole record
 against Instance/Mod/Extension.v's [extend_adj_unit] ("cannot unify
 "unit" and "extend_adj_unit phi Hc M""), the two being different
 terms that agree pointwise.  [TMod_equiv_UnitFixed] is an equivalence of
 categories, natural isomorphisms both ways, not an isomorphism.

 AXIOMS.  [Print Assumptions] on all 58 constants [Print Module]
 lists reports "Closed under the global context" for each.

 UNIVERSES, read by [About] under [Set Printing Universes] on every
 constant.  Each section declares [Universes u p] and takes its rings
 in [obj[Rng@{u p}]], so a ring is a [RingObject@{p p p}] and every
 section constant carries [Rng]'s own [Set < u] and [p < u].  The
 headline of the first half:

 Restrict_Full_iff_Epic@{u p u0} :
 Full (Restrict@{u u0 p} phi) ↔ Epic@{u p} phi
 ( * u p u0 |= Set < u, p < u, p < u0 * )

 which is [About Restrict]'s own shape ([Restrict@{u u0 u1}] with
 [Set < u], [u1 < u], [u1 < u0]): the proof adds no universe and no
 bound, so the test ring End(M ⊕ N) lives at the rings' own level [p]
 and epi ⇒ full holds at every level at which [Restrict] is formable.
 That needed the section [Shear] to take its [Ab] at [Ab@{u p}];
 left unannotated, the elaborator gave [Ab] a fresh object universe
 and the theorem one more universe than [Restrict].  [AbEndRing]
 keeps one auxiliary universe, [u0] in [AbEndRing@{u p u0}] with
 [p < u0]: its body instantiates Structure/AbCategory.v's
 [Ab_Preadditive@{u u0 p}], whose own [About] prints the same bound.
 [TMod_Reflective_in_RMod] carries ten universes; its record is
 [Reflective@{u u5 u u6 u p p}] over
 [extend_restrict_adjunction@{p p p p p p u u0 u1 u2 u3 u4}], all six
 ring universes of Instance/Mod/Extension.v's adjunction being [p]:
 the collapse that file's header measures for [Rng], nothing new.
 The ℤ → ℚ constants live at [Set], since Instance/Rng.v's [ZtoQ]
 maps [Int_Ring@{Set Set Set}] to [Q_Ring@{Set Set Set}]; every
 constant that mentions [Q_Ring] (these, [ZtoQ_inverts],
 [loc_morphism] and its successors) also carries [Set < flip.u0],
 [Set < flip.u1] and [Set < flip.u2], standard-library bounds that
 [About Q_Ring] prints on [Q_Ring] itself and that [Q_Rig] and
 [q_rig_setoid] do not carry.  So [QMod_Reflective_in_ZMod] and
 [ZMod_not_UnitFixed] are about [RMod Int_Ring@{Set Set Set}], and the
 W of [ZtoQ_IsLocalization] ranges over [obj[Rng@{u Set}]], rings at
 carrier level [Set]: at a W above [Set] its universal property is
 refused with "universe inconsistency: Cannot enforce Set = p"
 (pinned in Test/ProbeReflective370.v).  [loc_hom] is generic in the
 target: [Q_Ring@{p p p} ~{Rng}~> W] for W at any level; it is
 [ZtoQ] that is not.  [PosZ@{s}] has one universe and
 [inject_pos_nonzero] none.  [TMod_adj] carries the ten universes of
 [TMod_Reflective_in_RMod] and its bounds, and adds none.
 [loc_images_commute] and [loc_split] close with [Proof using W psi]:
 under the section's [Default Proof Using "All"] they would otherwise
 take the unused hypothesis [Hpsi], and [About] reads each as a
 statement about W and ψ alone.

 NOT DELIVERED.

 - The reflection without [CentralImage].  Instance/Mod/Extension.v
 builds extension of scalars from a tensor of two LEFT modules over
 one ring, which needs the image of φ central; its header names a
 genuine bimodule tensor product as the way out, and none is built.
 Restriction is fully faithful for every epi φ (above), and that
 half is free of it.  The hypothesis is carried by the left adjoint,
 and so by the subcategory and the record: the subcategory is
 [UnitFixed (extend_restrict_adjunction φ Hc)], cut out by that
 adjunction's unit, so [TMod_Reflective_in_RMod], [TMod_adj],
 [Restrict_UnitFixed] and [TMod_equiv_UnitFixed] all take [Hc].
 If every epimorphism out of a commutative ring has a commutative
 target (a classical result, not checked here),
 [CentralImage] is automatic for commutative R; nothing here states
 or uses that fact.
 - A general localization R[S⁻¹]: only the universal property is
 stated, and ℤ → ℚ is its one witness.  Instance/Rng/Frac.v's
 [frac_embed] is not shown epic here.
 - The characterizations of ring epimorphisms through T ⊗_R T (Stacks,
 Lemma 10.107.1, Tag 04VN).
 - Riehl's clause (v), sheafification, is left to a follow-up of issue
 #370: Theory/Sheaf/Category.v's sheaf predicate is under repair in
 issue #890. 

 --------
 nLab:   https://ncatlab.org/nlab/show/reflective+subcategory 
 nLab:   https://ncatlab.org/nlab/show/restriction+of+scalars 
 nLab:   https://ncatlab.org/nlab/show/epimorphism 
 nLab:   https://ncatlab.org/nlab/show/localization+of+a+commutative+ring 
 书籍:  Riehl, 《Category Theory in Context》，Dover 2016，第4.6节，
 示例 4.6.13 (iv)，印刷页 170（PDF 第 190 页）——目录项 riehl:4.6:example13，附加到 issue #370
 书籍:  Mac Lane，《Categories for the Working Mathematician》，第 2 版，
 GTM 5，第 IV.3 节，印刷页 92（PDF 第 101 页）—— issue #370 收集示例的章节
 文档:  The Stacks Project，标签 04VM（§10.107，“环的满射”）——交换代数的说明这来源于哪里。Mac Lane 在第 92 页的例子开头写道“这里有一些例子。Ab 在 Grp 中是自反的。”并继续涉及度量空间、拓扑空间和挠群；其中没有任何模范畴。问题 #370 还收集了 Riehl 的自反子范畴名录，其条款 (iv) 如第 170 页图片所引用如下：如示例 4.1.10(xii) 所述，对于任何环同态 φ: R → T，存在伴随函子 [displayed: T ⊗_R − ⊣ φ*]，其中右伴随为标量限制，左伴随为标量扩张。标量限制函子总是忠实的……当且仅当 φ: R → T 是一个满射时，它才是满的。对于这样的同态，标量限制将 _T Mod 作为 _R Mod 的一个反射子范畴来识别。环中的满射包括所有的满射映射，但不限于满射映射。局部化定义了另一类重要的满射映射……局部化 R → R [S⁻¹] 是一个初始对象，其所在范畴的对象是将 S 的所有元素映射为 T 单位元的环同态 R → T。(省略的分句给出了忠实度的原因：两个模范畴在Ab上都是忠实的。）这个文件就是那个分句。

 数学内容。沿着φ进行标量限制不会改变任何阿贝尔群和任何映射；它只是不考虑T如何作用。因此，完备性表示每个T模之间的R线性映射自动也是T线性映射：T的作用由R的作用决定。一个满射是同样思想在环层面的形式——来自T的映射由与φ组合后的映射决定——这两者是等价的。

 一个方向很短。如果限制是完备的，取环映射 g1, g2 : T → S 且 g1 φ ≈ g2 φ，使S成为两次T模（沿g1和g2），并观察S的恒等映射在两者之间是R线性的；完备性使其成为T线性，在t · 1处的T线性表明 g1 t ≈ g2 t ([Restrict_Full_Epic])。另一方向，Riehl 没有证明，但有一个标准证明，这是一个值得记录的技巧。给定 T-模 M 和 N 以及一个 R-线性加法映射 f : M → N，在直接和的加法自同构环 End(M ⊕ N) 中工作（[AbEndRing]）。T 在 M ⊕ N 上对角作用，一个环映射 ρ : T → End(M ⊕ N)（[module_rep]）。剪切映射 σ(m, n) = (m, n + f m) 是一个自同构（[shear_iso]），通过 σ 对 ρ 共轭得到第二个环映射 ρ' = σ ρ σ⁻¹（[twisted_rep]，通过 [EndRig_conj]），其计算为 t ↦ ((m, n) ↦ (t m, t (n - f m) + f (t m)))。两者在 t 上一致当且仅当 f 与 t 交换（[twist_fixed_of_linear]，[linear_of_twist_fixed]）。R-线性使它们在 φ 之后一致；φ 的满射性使它们一致；因此 f 是 T-线性的（[Epic_Restrict_Full]）。

 已交付内容。-  [Restrict_Faithful], [Restrict_Full_Epic], [Epic_Restrict_Full] 和 [Restrict_Full_iff_Epic]：Riehl 的“始终忠实，并且当且仅当 φ 是满射时才全”，适用于任意环 R 和 T 以及任何环映射 φ。这里不假设任何交换性。-  [TMod_Reflective_in_RMod]，及其作为自身常量的伴随 [TMod_adj]：对于 φ 为满射且有 [CentralImage φ]，T-Mod 在 R-Mod 中是反射子范畴，扩张标量作为反射函子。该子范畴是 Instance/Mod/Extension.v 中伴随（Construction/Reflective/FixedPoints.v）所对应的 [UnitFixed]：那些使单位 M → Restrict(T ⊗ M) 可逆的 R-模。该记录来自 [unit_fixed_reflective_of_idempotent]，诱导的 monad 是幂等的，因为余单位可逆（ZW24WZZ，来自 Adjunction/FullFaithful.v 的 [right_adjoint_fully_faithful_iff_counit_iso]）。- [Restrict_UnitFixed] 和 [TMod_equiv_UnitFixed]：在该子类别中的限制，并且是到该子类别的等价——通过 Theory/Equivalence/FullFaithful.v 的 [FF_ESO_Equivalence] 是满的、忠实的并且本质上是满射的——这就是 Riehl 所说的“将 T Mod 识别为反射子类别”在这里的意思。- [QMod_Reflective_in_ZMod]、[QMod_equiv_UnitFixed] 和 [Restrict_ZtoQ_Full]：在 ℤ → ℚ 的实例，没有剩余假设：Instance/Rng.v 的 [ZtoQ_epic] 和 Instance/Mod/Extension.v 的 [Q_central] 都完成了。它的模是 [RMod Int_Ring@{Set Set Set}] 的那些模：Instance/Rng.v 的 [ZtoQ] 在载体层级 [Set]（UNIVERSES，见下文）上被固定。- [ZMod_not_UnitFixed]：该反射是适当的。ℤ，作为自身的模，不属于该子范畴：在 ℤ 处单位 η 的逆元 g 将是 ℤ 线性的，η 1 = 1 ⊗ 1 是 ℚ 模 ℚ ⊗ ℤ 中元素 (1/2) · (1 ⊗ 1) 的两倍，因此 1 = g(η 1) 将是偶数（[lia] 封闭了奇偶性）。- [InvertsSet]、[IsLocalization] 和 [localization_epic]：在反转一个族 S 的那些映射中初始的环映射是一个满射，对于任意 S 都成立（不需要 Riehl 的乘法闭包）。只使用了泛性质的唯一性部分。- [ZtoQ_IsLocalization]：ℤ → ℚ 是在正整数处的局部化，映射到任意载体层面的环 W，无论是否交换。该级别是 [ZtoQ] 的，其 Instance/Rng.v 在 [Set] 定位
 （[About ZtoQ_IsLocalization] 读取 [IsLocalization@{u0 Set u1 u u1} ZtoQ@{u0} PosZ@{u1}]，第二个宇宙是环的级别）；中介 [loc_hom] 本身是级别通用的。[loc_hom] 将 a/b 发送到 ψ a · (ψ b)⁻¹，这是定义良好的，因为 ℤ 的像是交换的（[loc_images_commute]）。唯一性通过直接证明，方法是消去 ψ b（[loc_hom_unique]），而不是通过 [ZtoQ_epic]，因此 [ZtoQ_epic_of_localization] 是 Instance/Rng.v 的 [ZtoQ_epic] 的一个独立的第二个证明。优势，严格首先衡量。在 [eq_refl]：返回的满射前像就是给定的加法映射（[Epic_Restrict_Full_prefmap]：没有重建）；扭曲作用在对上计算（[twisted_rep_value]）；反射器在 M 处的模是 [RestrictObj φ (ExtendObj φ Hc M)]（[TMod_reflector_obj]）；在 m 处的单位是 Riehl 的 1 ⊗ m，即 [ext_gen φ M 1 m]（[TMod_unit_pointwise]）；在 [Restrict_UnitFixed] 之后的包含是对对象的限制（[Restrict_UnitFixed_incl]）。在 [eq_refl] 被拒绝，在 Test/ProbeReflective370.v 中固定，而不是在这里（该文件中的负探针行将增加到 [make todo]）：作为整体记录的单位针对 Instance/Mod/Extension.v 的 [extend_adj_unit]（"无法统一‘unit’和‘extend_adj_unit phi Hc M’"），这两个是不同的项，但按点一致。[TMod_equiv_UnitFixed] 是范畴的等价，两方向的自然同构，不是同构。公理。[Print Assumptions] 在所有 58 个常量上 [Print Module] 列出报告“在全局上下文下封闭”。

 宇宙，由 [About] 在 [Set Printing Universes] 下读取每个常量。每个部分声明 [Universes u p] 并在 [obj[Rng@{u p}] 中取其环，因此一个环是 [RingObject@{p p p}]，每个部分常量携带 [Rng] 自己的 [Set < u] 和 [p < u]。上半部分标题：

 Restrict_Full_iff_Epic@{u p u0} :
 Full (Restrict@{u u0 p} phi) ↔ Epic@{u p} phi
 ( * u p u0 |= 集合 < u, p < u, p < u0 * )这是 [About Restrict] 本身的形状（[Restrict@{u u0 u1}] 与 [Set < u]、[u1 < u]、[u1 < u0]）：证明没有增加任何宇宙和任何界限，所以测试环 End(M ⊕ N) 存在于环自身的级别 [p]，并且 epi ⇒ full 在 [Restrict] 可形成的每个级别都成立。这需要截面 [Shear] 在 [Ab@{u p}] 处取得其 [Ab]；如果未标注，精细化器会给 [Ab] 一个新的对象宇宙，并给定理一个比 [Restrict] 更多的宇宙。[AbEndRing] 保留了一个辅助宇宙，[u0] 在 [AbEndRing@{u p u0}] 中与 [p < u0] 一起使用：其主体实例化了 Structure/AbCategory.v 的 [Ab_Preadditive@{u u0 p}]，其自身的 [About] 打印出相同的界限。[TMod_Reflective_in_RMod] 拥有十个宇宙；它的记录是
 [Reflective@{u u5 u u6 u p p}] 超过
 [extend_restrict_adjunction@{p p p p p p u u0 u1 u2 u3 u4}] ，Instance/Mod/Extension.v 的附加中的所有六个环宇宙为 [p] ：
 该文件头测量 [Rng] 的崩溃，没有新内容。ℤ → ℚ 常数位于 [Set] ，因为 Instance/Rng.v 的 [ZtoQ] 
 将 [Int_Ring@{Set Set Set}] 映射到 [Q_Ring@{Set Set Set}]；每个提及 [Q_Ring] 的常数（这些，[ZtoQ_inverts] ，
 [loc_morphism] 及其后续项）也携带 [Set < flip.u0] ，
 [Set < flip.u1] 和 [Set < flip.u2]，标准库界限由 [About Q_Ring] 打印在 [Q_Ring] 本身上，而 [Q_Rig] 和
 [q_rig_setoid] 不携带。所以 [QMod_Reflective_in_ZMod] 和 [ZMod_not_UnitFixed] 是关于 [RMod Int_Ring@{Set Set Set}] 的，而 [ZtoQ_IsLocalization] 的 W 范围在 [obj[Rng@{u Set}] 之间，载体层的环为 [Set]：在 [Set] 之上的 W 上，它的通用性质被拒绝，显示“宇宙不一致：无法强制执行 Set = p”（固定在 Test/ProbeReflective370.v 中）。[loc_hom] 在目标中是通用的：对于任意级别的 W，[Q_Ring@{p p p} ~{Rng}~> W] 是通用的；而 [ZtoQ] 不是。[PosZ@{s}] 具有一个宇宙，而 [inject_pos_nonzero] 没有。[TMod_adj] 承载 [TMod_Reflective_in_RMod] 及其界的十个宇宙，并且没有新增。[loc_images_commute] 和 [loc_split] 以 [Proof using W psi] 结束：在该部分的 [Default Proof Using "All"] 下，否则它们将采用未使用的假设 [Hpsi]，而 [About] 将每个都作为关于 W 和 ψ 的独立陈述来读取。

 未交付。- 没有 [CentralImage] 的反射。实例/模块/扩展.v  
 从一个环上的两个左模的张量构建标量扩张，这需要 φ 的像是中心的；它的头文件将一个真正的双模张量积命名为解决方法，但没有构建。对于每个满射 φ（如上所述），限制是完全忠实的，且这一半是自由的。假设由左陪伴函子承载，因此也由子范畴和记录承载：子范畴是 [UnitFixed (extend_restrict_adjunction φ Hc)]，由该陪伴单位切出，所以 [TMod_Reflective_in_RMod]、[TMod_adj]、[Restrict_UnitFixed] 和 [TMod_equiv_UnitFixed] 都取 [Hc]。如果每个从交换环出的满射都有交换目标（一个经典结果，这里未验证），[CentralImage] 对交换 R 是自动的；此处没有陈述或使用该事实。- 一般化的局部化 R [S⁻¹]：仅说明了通用性质，并且 ℤ → ℚ 是它的一个例子。Instance/Rng/Frac.v 中的 [frac_embed] 在这里未显示为满射。 - 通过 T ⊗_R T 对环同态的表征（Stacks, Lemma 10.107.1, Tag 04VN）。 - Riehl 条款 (v)，纤维化（sheafification），留待问题 #370 的后续处理：Theory/Sheaf/Category.v 中的 sheaf 谓词在问题 #890 中正在修复。
*)

(* * ** The endomorphism ring of an abelian group / * ** 阿贝尔群的自同态环 *)

(*
 [EndRig] (Theory/Algebra/Rig.v) at the object [A] of [Ab], with
 [ab_hom_neg] (Structure/AbCategory.v) as its negation.  The instance
 of [LocallyPropositional] is passed by name: the record literal is
 elaborated before instance resolution would see it. 

 --------
 [EndRig]（Theory/Algebra/Rig.v）在对象 [A] 的 [Ab] 中，其否定为 [ab_hom_neg]（Structure/AbCategory.v）。[LocallyPropositional] 的实例是按名称传递的：记录字面量在实例解析看到它之前会被展开。
*)
Definition AbEndRing@{u p +} (A : obj[Ab@{u p}]) : obj[Rng@{u p}].
Proof.
  refine {| ring_rig :=
              @EndRig Ab@{u p} Ab_LocallyPropositional Ab_Preadditive A;
            ring_neg := fun g : A ~{Ab}~> A => ab_hom_neg g |}.
  - intros g h Hgh a; simpl.
    now rewrite (Hgh a).
  - intros g a; simpl.
    apply ab_neg_left.
Defined.

(* * ** Conjugation by an automorphism is a rig endomorphism / * **通过自同构的共轭是半环自同态 *)

Definition EndRig_conj@{o h +} {C : Category@{o h h}}
  {LP : LocallyPropositional C} (P : Preadditive C) {c : C} (i : c ≅ c) :
  RigHom (EndRig P c) (EndRig P c).
Proof.
  unshelve refine (@Build_RigHom (EndRig P c) (EndRig P c)
    {| morphism := fun x : c ~> c => to i ∘ x ∘ from i |} _ _ _ _);
    simpl.
  - intros x y Hxy.
    now rewrite Hxy.
  - rewrite compose_pzero_right.
    apply compose_pzero_left.
  - intros a b.
    rewrite compose_padd_left.
    apply compose_padd_right.
  - rewrite id_right.
    apply iso_to_from.
  - intros a b.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (from i) (to i)), iso_from_to, id_left.
    reflexivity.
Defined.

(* * ** A module structure is a ring map into the endomorphisms / * ** 模块结构是到自同态的环映射 *)

Definition smul_endo@{u p +} {T : obj[Rng@{u p}]} (M : obj[RMod T])
  (t : carrier (rig_setoid (ring_rig T))) : rm_ab M ~{Ab@{u p}}~> rm_ab M.
Proof.
  refine (@Build_CMonHom (rm_ab M) (rm_ab M)
            {| morphism := rm_smul M t;
               proper_morphism := fun m m' Hm =>
                 rm_smul_respects M t t (reflexivity t) m m' Hm |} _ _).
  - apply rm_smul_zero_r.
  - intros m n.
    apply rm_smul_distr_l.
Defined.

Definition module_rep@{u p +} {T : obj[Rng@{u p}]} (M : obj[RMod T]) :
  T ~{Rng@{u p}}~> AbEndRing (rm_ab M).
Proof.
  unshelve refine (@Build_RigHom (ring_rig T) (ring_rig (AbEndRing (rm_ab M)))
    {| morphism := smul_endo M |} _ _ _ _); simpl.
  - intros t t' Ht m; simpl.
    now rewrite Ht.
  - intro m; simpl.
    apply rm_smul_zero_l.
  - intros t s m; simpl.
    apply rm_smul_distr_r.
  - intro m; simpl.
    apply rm_smul_one.
  - intros t s m; simpl.
    apply rm_smul_assoc.
Defined.

(* * ** The shear of M ⊕ N along an additive map / * ** M ⊕ N 沿加法映射的切变 *)

Section Shear.

Local Set Default Proof Using "All".

Universes u p.

Context {T : obj[Rng@{u p}]}.
Context (M N : obj[RMod T]).
Context (f : rm_ab M ~{Ab@{u p}}~> rm_ab N).

Local Notation MN := (RMod_product M N).

(* (m, n) ↦ (m, n + f m) *)
Definition shear_to : rm_ab MN ~{Ab@{u p}}~> rm_ab MN.
Proof.
  unshelve refine (@Build_CMonHom (rm_ab MN) (rm_ab MN)
    {| morphism := fun p : carrier (cmon_setoid (rm_ab MN)) =>
         (fst p, cmon_plus N (snd p) (cmon_map f (fst p))) |} _ _).
  - intros [m n] [m' n'] [Hm Hn]; simpl in *.
    split; simpl; [ exact Hm |].
    now rewrite Hm, Hn.
  - split; simpl; [ reflexivity |].
    rewrite (cmon_map_zero f).
    apply cmon_plus_zero_l.
  - intros [m n] [m' n']; simpl.
    split; simpl; [ reflexivity |].
    rewrite (cmon_map_plus f m m').
    apply cmon_plus_interchange.
Defined.

(* (m, n) ↦ (m, n - f m) *)
Definition shear_from : rm_ab MN ~{Ab@{u p}}~> rm_ab MN.
Proof.
  unshelve refine (@Build_CMonHom (rm_ab MN) (rm_ab MN)
    {| morphism := fun p : carrier (cmon_setoid (rm_ab MN)) =>
         (fst p, ab_sub N (snd p) (cmon_map f (fst p))) |} _ _).
  - intros [m n] [m' n'] [Hm Hn]; simpl in *.
    split; simpl; [ exact Hm |].
    now rewrite Hm, Hn.
  - split; simpl; [ reflexivity |].
    rewrite (cmon_map_zero f).
    apply ab_sub_self.
  - intros [m n] [m' n']; simpl.
    split; simpl; [ reflexivity |].
    rewrite (cmon_map_plus f m m').
    symmetry; apply ab_sub_plus.
Defined.

Definition shear_iso : @Isomorphism Ab@{u p} (rm_ab MN) (rm_ab MN).
Proof.
  refine (@Build_Isomorphism Ab@{u p} (rm_ab MN) (rm_ab MN)
            shear_to shear_from _ _).
  - intros [m n]; simpl.
    split; simpl; [ reflexivity |].
    rewrite cmon_plus_comm.
    apply ab_add_sub_cancel.
  - intros [m n]; simpl.
    split; simpl; [ reflexivity |].
    rewrite (cmon_plus_comm N n).
    apply ab_sub_add_cancel.
Defined.

(* The diagonal action of T on M ⊕ N, conjugated by the shear. / T 在 M ⊕ N 上的对角作用，由剪切变换共轭。 *)
Definition twisted_rep : T ~{Rng}~> AbEndRing (rm_ab MN) :=
  (EndRig_conj Ab_Preadditive shear_iso
     : AbEndRing (rm_ab MN) ~{Rng}~> AbEndRing (rm_ab MN))
    ∘ module_rep MN.

(*
 It computes on pairs:
 t ↦ ((m, n) ↦ (t m, t (n - f m) + f (t m))). 

 --------
 它在对上进行计算：
 t ↦ ((m, n) ↦ (t m, t (n - f m) + f (t m)))。
*)
Example twisted_rep_value (t : carrier (rig_setoid (ring_rig T)))
  (m : carrier (cmon_setoid M)) (n : carrier (cmon_setoid N)) :
  cmon_map (rig_map twisted_rep t) (m, n)
    = (rm_smul M t m,
       cmon_plus N (rm_smul N t (ab_sub N n (cmon_map f m)))
                   (cmon_map f (rm_smul M t m))) := eq_refl.

(* Where f commutes with t, the twisted action at t IS the plain one. / 当 f 与 t 可交换时，t 的扭曲作用就是普通作用。 *)
Lemma twist_fixed_of_linear (t : carrier (rig_setoid (ring_rig T)))
  (Hlin : ∀ m, cmon_map f (rm_smul M t m) ≈ rm_smul N t (cmon_map f m)) :
  rig_map twisted_rep t ≈ rig_map (module_rep MN) t.
Proof.
  intros [m n]; simpl.
  split; simpl; [ reflexivity |].
  rewrite (Hlin m).
  unfold ab_sub.
  rewrite (rm_smul_distr_l N t n (ab_neg N (cmon_map f m))).
  rewrite (rm_smul_neg_r N t (cmon_map f m)).
  rewrite cmon_plus_comm.
  apply ab_add_sub_cancel.
Qed.

(* Conversely, agreement at t forces f to commute with t: evaluate at the pair (m, f m). / 相反，在 t 上的一致性迫使 f 与 t 交换：在对 (m, f m) 上进行求值。 *)
Lemma linear_of_twist_fixed (t : carrier (rig_setoid (ring_rig T)))
  (H : rig_map twisted_rep t ≈ rig_map (module_rep MN) t) :
  ∀ m, cmon_map f (rm_smul M t m) ≈ rm_smul N t (cmon_map f m).
Proof.
  intro m.
  destruct (H (m, cmon_map f m)) as [_ H2]; simpl in H2.
  rewrite ab_sub_self, rm_smul_zero_r, cmon_plus_zero_l in H2.
  exact H2.
Qed.

End Shear.

(* * ** Riehl 4.6.13 (iv): restriction is faithful, and full iff phi is epi / * ** Riehl 4.6.13 (iv)：限制是忠实的，当且仅当 φ 是满射时才是完全的 *)

Section RingEpi.

Universes u p.

Context {R T : obj[Rng@{u p}]}.
Context (phi : R ~{Rng@{u p}}~> T).

Definition Restrict_Faithful : Faithful (Restrict phi).
Proof. constructor; intros M N f g H a; exact (H a). Qed.

(*
 The identity of S, read as an R-linear map between the two
 phi-restrictions of S along g1 and along g2. 

 --------
 S 的恒等映射，被理解为沿 g1 和 g2 的 S 的两个 phi-限制之间的 R 线性映射。
*)
Definition two_actions_id {S : obj[Rng@{u p}]} (g1 g2 : T ~{Rng@{u p}}~> S)
  (Hg : g1 ∘ phi ≈ g2 ∘ phi) :
  RestrictObj phi (RestrictObj g1 (Ring_RMod S))
    ~{RMod R}~> RestrictObj phi (RestrictObj g2 (Ring_RMod S)).
Proof.
  unshelve refine (@Build_RModHom R
    (RestrictObj phi (RestrictObj g1 (Ring_RMod S)))
    (RestrictObj phi (RestrictObj g2 (Ring_RMod S))) (@cmon_hom_id _) _).
  intros r m; simpl.
  apply rig_mul_respects; [ exact (Hg r) | reflexivity ].
Defined.

(*
 Riehl's "only if": fullness lifts [two_actions_id] to a T-linear map,
 and T-linearity evaluated at t · 1 is g1 t ≈ g2 t. 

 --------
 Riehl 的“只有当”：丰满性将 [two_actions_id] 提升为 T 线性映射，且在 t · 1 处评价的 T 线性是 g1 t ≈ g2 t。
*)
Theorem Restrict_Full_Epic : Functor.Full (Restrict phi) → Epic phi.
Proof.
  intros HF.
  constructor; intros S g1 g2 Hg t.
  pose proof (@fmap_sur _ _ (Restrict phi) HF
                (RestrictObj g1 (Ring_RMod S)) (RestrictObj g2 (Ring_RMod S))
                (two_actions_id g1 g2 Hg)) as Hk.
  pose proof (rm_map_smul
                (@prefmap _ _ (Restrict phi) HF
                   (RestrictObj g1 (Ring_RMod S))
                   (RestrictObj g2 (Ring_RMod S))
                   (two_actions_id g1 g2 Hg))
                t (rig_one (ring_rig S))) as Hlin.
  simpl in Hlin.
  rewrite (Hk _), (Hk _) in Hlin.
  rewrite !rig_mul_one_r in Hlin.
  exact Hlin.
Qed.

(*
 Riehl's "if": an R-linear f between T-modules has twisted and plain
 actions agreeing after phi, hence everywhere, hence is T-linear. 

 --------
 Riehl 的“如果”：一个 T 模的 R 线性 f 在经过 φ 后，其扭曲和普通的作用一致，因此在任何地方都一致，因此是 T 线性的。
*)
Theorem Epic_Restrict_Full : Epic phi → Functor.Full (Restrict phi).
Proof.
  intros He.
  unshelve refine {| prefmap := fun M N f => _ |}.
  - refine (@Build_RModHom T M N (rm_hom f) _).
    intros t.
    apply (linear_of_twist_fixed M N (rm_hom f) t).
    refine (@epic _ _ _ phi He _ (twisted_rep M N (rm_hom f))
              (module_rep (RMod_product M N)) _ t).
    intros r.
    apply twist_fixed_of_linear.
    intro m.
    exact (rm_map_smul f r m).
  - intros M N f a; simpl.
    reflexivity.
Defined.

(* The preimage IS the given additive map: nothing is rebuilt. / 原像就是给定的加法映射：没有重建任何东西。 *)
Example Epic_Restrict_Full_prefmap (He : Epic phi) (M N : obj[RMod T])
  (f : Restrict phi M ~> Restrict phi N) :
  rm_hom (@prefmap _ _ _ (Epic_Restrict_Full He) M N f) = rm_hom f
  := eq_refl.

Definition Restrict_Full_iff_Epic : Functor.Full (Restrict phi) ↔ Epic phi :=
  (Restrict_Full_Epic, Epic_Restrict_Full).

End RingEpi.

(* * ** For an epimorphism, T-Mod is reflective in R-Mod / * ** 对于一个满射，T-模在R-模中是反射性的 *)

Section Reflection.

Local Set Default Proof Using "All".

Universes u p.

Context {R T : obj[Rng@{u p}]}.
Context (phi : R ~{Rng@{u p}}~> T).
Context (Hc : CentralImage phi).
Context (He : Epic phi).

Let A := extend_restrict_adjunction phi Hc.

Definition restrict_counit_iso (N : RMod T) :
  IsIsomorphism (@counit _ _ _ _ A N) :=
  fst (@right_adjoint_fully_faithful_iff_counit_iso _ _ _ _ A)
      (Epic_Restrict_Full phi He, Restrict_Faithful phi) N.

Definition restrict_idempotent :
  @IdempotentMonad (RMod R) (Restrict phi ◯ ExtendScalars phi Hc)
    (Adjunction_Induced_Monad A).
Proof.
  constructor; intro x.
  exact (fmap_IsIsomorphism (Restrict phi) _
           (restrict_counit_iso (ExtendScalars phi Hc x))).
Defined.

Definition TMod_Reflective_in_RMod : Reflective (UnitFixed A) :=
  unit_fixed_reflective_of_idempotent A restrict_idempotent.

(*
 The record's adjunction, as its own constant: the reflector left
 adjoint to the inclusion of the unit-fixed modules. 

 --------
 记录的连接，作为它自身的常数：反射器左连接到单位固定模的包含。
*)
Definition TMod_adj :
  reflector TMod_Reflective_in_RMod ⊣ Incl (RMod R) (UnitFixed A) :=
  reflective_adj TMod_Reflective_in_RMod.

Example TMod_reflector_obj (M : RMod R) :
  `1 (fobj[reflector TMod_Reflective_in_RMod] M)
    = RestrictObj phi (ExtendObj phi Hc M) := eq_refl.

(* The unit is Riehl's m ↦ 1 ⊗ m, pointwise on the nose. / 该单位是 Riehl 的 m ↦ 1 ⊗ m，对每一点都是精确的。 *)
Example TMod_unit_pointwise (M : RMod R) (m : carrier (cmon_setoid M)) :
  cmon_map
    (rm_hom (@unit _ _ _ _ (reflective_adj TMod_Reflective_in_RMod) M)) m
    = ext_gen phi M (rig_one (ring_rig T)) m := eq_refl.

(* Restriction lands in the unit-fixed subcategory and identifies T-Mod with it. / 限制位于单位固定子类别中，并将 T-Mod 与其识别。 *)
Definition Restrict_UnitFixed_obj (N : RMod T) :
  Sub (RMod R) (UnitFixed A) :=
  (Restrict phi N; unit_iso_of_counit_iso A N (restrict_counit_iso N)).

Definition Restrict_UnitFixed : RMod T ⟶ Sub (RMod R) (UnitFixed A).
Proof.
  unshelve refine
    {| fobj := Restrict_UnitFixed_obj
     ; fmap := fun N N' g => (fmap[Restrict phi] g; I) |}.
  - intros N N' g g' Hg; simpl.
    exact (@fmap_respects _ _ (Restrict phi) N N' g g' Hg).
  - intro N; simpl.
    exact (@fmap_id _ _ (Restrict phi) N).
  - intros N N' N'' g g'; simpl.
    exact (@fmap_comp _ _ (Restrict phi) N N' N'' g g').
Defined.

Example Restrict_UnitFixed_incl (N : RMod T) :
  fobj[Incl (RMod R) (UnitFixed A)] (fobj[Restrict_UnitFixed] N)
    = fobj[Restrict phi] N := eq_refl.

#[local] Instance Restrict_UnitFixed_Full : Functor.Full Restrict_UnitFixed.
Proof.
  unshelve econstructor.
  - intros N N' g.
    exact (@prefmap _ _ (Restrict phi) (Epic_Restrict_Full phi He)
             N N' (`1 g)).
  - intros N N' g.
    exact (@fmap_sur _ _ (Restrict phi) (Epic_Restrict_Full phi He)
             N N' (`1 g)).
Defined.

#[local] Instance Restrict_UnitFixed_Faithful : Faithful Restrict_UnitFixed.
Proof.
  constructor; intros N N' g g' H.
  exact (@fmap_inj _ _ (Restrict phi) (Restrict_Faithful phi) N N' g g' H).
Defined.

#[local] Instance Restrict_UnitFixed_ESO :
  EssentiallySurjective Restrict_UnitFixed.
Proof.
  unshelve econstructor.
  - intros x.
    exact (ExtendScalars phi Hc (`1 x)).
  - intros [M HM].
    refine (Full_sub_iso (RMod R) (UnitFixed A) (UnitFixed_Full A) _ HM _).
    exact (iso_sym (IsIsoToIso _ HM)).
Defined.

Definition TMod_equiv_UnitFixed :
  EquivalenceOfCategories Restrict_UnitFixed :=
  FF_ESO_Equivalence Restrict_UnitFixed.

End Reflection.

(* * ** The witness: Q-modules in Z-modules / * ** 证人：Z-模中的Q-模 *)

Definition Restrict_ZtoQ_Full@{+} : Functor.Full (Restrict ZtoQ) :=
  Epic_Restrict_Full ZtoQ ZtoQ_epic.

Definition QMod_Reflective_in_ZMod@{+} :
  Reflective (UnitFixed (extend_restrict_adjunction ZtoQ Q_central)) :=
  TMod_Reflective_in_RMod ZtoQ Q_central ZtoQ_epic.

Definition QMod_equiv_UnitFixed@{+} :
  EquivalenceOfCategories
    (Restrict_UnitFixed ZtoQ Q_central ZtoQ_epic) :=
  TMod_equiv_UnitFixed ZtoQ Q_central ZtoQ_epic.

(* * ** Localizations are epimorphisms / * ** 局部化是满射 *)

Section Localization.

Universes u p.

Context {R L : obj[Rng@{u p}]}.
Context (phi : R ~{Rng@{u p}}~> L).
Context (S : carrier (rig_setoid (ring_rig R)) → Type).

(*
 psi carries every element of S to a two-sided unit; the inverse is
 data. 

 --------
 ψ 将 S 的每个元素映射到一个双边单位；逆元是数据。
*)
Definition InvertsSet {W : obj[Rng@{u p}]} (psi : R ~{Rng@{u p}}~> W) : Type :=
  ∀ s, S s → ∃ v : carrier (rig_setoid (ring_rig W)),
    (rig_mul (ring_rig W) (rig_map psi s) v ≈ rig_one (ring_rig W)) ∧
    (rig_mul (ring_rig W) v (rig_map psi s) ≈ rig_one (ring_rig W)).

(*
 Riehl's "initial object in the category whose objects are ring
 homomorphisms R → T that carry all of the elements of S to units". 

 --------
 Riehl 的“在其对象是将 S 的所有元素映射为单位元的环同态 R → T 的范畴中的初始对象”。
*)
Definition IsLocalization : Type :=
  InvertsSet phi ∧
  (∀ (W : obj[Rng@{u p}]) (psi : R ~{Rng@{u p}}~> W),
      InvertsSet psi → ∃! chi : L ~{Rng@{u p}}~> W, chi ∘ phi ≈ psi).

(* Only the uniqueness half is spent: g1 ∘ phi inverts S, and g1, g2 both factor it. / 只有唯一性部分被使用：g1 ∘ phi 反转 S，并且 g1、g2 都将其分解。 *)
Theorem localization_epic : IsLocalization → Epic phi.
Proof.
  intros [Hphi Huniv].
  constructor; intros W g1 g2 Hg.
  assert (Hinv : InvertsSet (g1 ∘ phi)).
  { intros s Hs.
    destruct (Hphi s Hs) as [v [Hl Hr]].
    exists (rig_map g1 v); split; simpl.
    - rewrite <- rig_map_mul.
      rewrite (proper_morphism (rig_map g1) _ _ Hl).
      apply rig_map_one.
    - rewrite <- rig_map_mul.
      rewrite (proper_morphism (rig_map g1) _ _ Hr).
      apply rig_map_one. }
  destruct (Huniv W (g1 ∘ phi) Hinv) as [chi Hchi Hu].
  transitivity chi.
  - symmetry; apply Hu; reflexivity.
  - apply Hu; symmetry; exact Hg.
Qed.

End Localization.

(* * ** The witness: Z -> Q is the localization at the positive integers / * ** 该证据：Z -> Q 是在正整数处的局部化 *)

(* Required here rather than at the head of the file, for the reason Instance/Mod/Extension.v gives: QArith's import shadows [equiv]. / 这里需要而不是在文件头部，原因是 Instance/Mod/Extension.v 报告：QArith 的导入覆盖了 [equiv]。 *)
Require Import Coq.QArith.QArith.

Definition PosZ@{s +} (z : Z) : Type@{s} := ∃ p : positive, z = Z.pos p.

Lemma inject_pos_nonzero@{} (p : positive) : ~ (inject_Z (Z.pos p) == 0)%Q.
Proof. intro H; unfold inject_Z, Qeq in H; simpl in H; discriminate H. Qed.

Lemma ZtoQ_inverts@{+} : InvertsSet (R := Int_Ring) PosZ ZtoQ.
Proof.
  intros s [p Hp]; subst s.
  exists (/ inject_Z (Z.pos p))%Q; split; simpl.
  - apply Qmult_inv_r, inject_pos_nonzero.
  - rewrite Qmult_comm; apply Qmult_inv_r, inject_pos_nonzero.
Qed.

Section Factor.

Local Set Default Proof Using "All".

Universes u p.

Context (W : obj[Rng@{u p}]).
Context (psi : Int_Ring ~{Rng@{u p}}~> W).
Context (Hpsi : InvertsSet (R := Int_Ring) PosZ psi).

Local Notation "x · y" := (rig_mul (ring_rig W) x y)
  (at level 40, left associativity).
Local Notation ps := (rig_map psi).

(* The chosen inverse of psi b, for b a positive integer. / ψ(b) 的选定逆函数，其中 b 为正整数。 *)
Definition loc_inv (b : positive) : carrier (rig_setoid (ring_rig W)) :=
  `1 (Hpsi (Z.pos b) (b; eq_refl)).

Lemma loc_inv_r (b : positive) :
  ps (Z.pos b) · loc_inv b ≈ rig_one (ring_rig W).
Proof. exact (fst `2 (Hpsi (Z.pos b) (b; eq_refl))). Qed.

Lemma loc_inv_l (b : positive) :
  loc_inv b · ps (Z.pos b) ≈ rig_one (ring_rig W).
Proof. exact (snd `2 (Hpsi (Z.pos b) (b; eq_refl))). Qed.

(*
 The image of Z is commutative, whatever W is: the hypothesis [Hpsi]
 is not used, and the explicit [Proof using] keeps it out of the
 lemma's type. 

 --------
 Z 的像是交换的，无论 W 是什么：假设 [Hpsi] 没有被使用，而显式的 [Proof using] 将其保持在引理类型之外。
*)
Lemma loc_images_commute (a b : Z) : ps a · ps b ≈ ps b · ps a.
Proof using W psi.
  rewrite <- !rig_map_mul.
  apply (proper_morphism (rig_map psi)).
  exact (Z.mul_comm a b).
Qed.

Lemma loc_cancel (x y : carrier (rig_setoid (ring_rig W))) (b : positive) :
  x · ps (Z.pos b) ≈ y · ps (Z.pos b) → x ≈ y.
Proof.
  intro H.
  rewrite <- (rig_mul_one_r (ring_rig W) x),
          <- (rig_mul_one_r (ring_rig W) y).
  rewrite <- (loc_inv_r b).
  rewrite <- !rig_mul_assoc.
  now rewrite H.
Qed.

(* a/b ↦ psi a · (psi b)⁻¹ / a/b ↦ psi a · (psi b)⁻¹ *)
Definition loc_fun (q : Q) : carrier (rig_setoid (ring_rig W)) :=
  ps (Qnum q) · loc_inv (Qden q).

Lemma loc_fun_spec (q : Q) : loc_fun q · ps (Z.pos (Qden q)) ≈ ps (Qnum q).
Proof.
  unfold loc_fun.
  rewrite rig_mul_assoc, loc_inv_l.
  apply rig_mul_one_r.
Qed.

Lemma loc_split (x : carrier (rig_setoid (ring_rig W))) (b1 b2 : positive) :
  x · ps (Z.pos (b1 * b2)) ≈ (x · ps (Z.pos b1)) · ps (Z.pos b2).
Proof using W psi.
  change (Z.pos (b1 * b2)) with (Z.pos b1 * Z.pos b2)%Z.
  rewrite rig_map_mul.
  symmetry; apply rig_mul_assoc.
Qed.

Lemma loc_fun_respects (q1 q2 : Q) : (q1 == q2)%Q → loc_fun q1 ≈ loc_fun q2.
Proof.
  intro H.
  unfold Qeq in H.
  apply (loc_cancel _ _ (Qden q1 * Qden q2)).
  rewrite !loc_split.
  rewrite loc_fun_spec.
  rewrite (rig_mul_assoc (ring_rig W) (loc_fun q2)).
  rewrite (loc_images_commute (Z.pos (Qden q1)) (Z.pos (Qden q2))).
  rewrite <- (rig_mul_assoc (ring_rig W) (loc_fun q2)).
  rewrite loc_fun_spec.
  rewrite <- !rig_map_mul.
  apply (proper_morphism (rig_map psi)).
  exact H.
Qed.

Lemma loc_fun_add (q1 q2 : Q) :
  loc_fun (q1 + q2)%Q ≈ rig_add (ring_rig W) (loc_fun q1) (loc_fun q2).
Proof.
  apply (loc_cancel _ _ (Qden q1 * Qden q2)).
  rewrite loc_fun_spec.
  rewrite (rig_distr_r (ring_rig W)).
  rewrite !loc_split.
  rewrite loc_fun_spec.
  rewrite (rig_mul_assoc (ring_rig W) (loc_fun q2)).
  rewrite (loc_images_commute (Z.pos (Qden q1)) (Z.pos (Qden q2))).
  rewrite <- (rig_mul_assoc (ring_rig W) (loc_fun q2)).
  rewrite loc_fun_spec.
  rewrite <- !rig_map_mul, <- rig_map_add.
  reflexivity.
Qed.

Lemma loc_fun_mul (q1 q2 : Q) :
  loc_fun (q1 * q2)%Q ≈ loc_fun q1 · loc_fun q2.
Proof.
  apply (loc_cancel _ _ (Qden q1 * Qden q2)).
  rewrite (loc_fun_spec (q1 * q2)%Q).
  rewrite loc_split.
  rewrite (rig_mul_assoc (ring_rig W) (loc_fun q1 · loc_fun q2)).
  rewrite (loc_images_commute (Z.pos (Qden q1)) (Z.pos (Qden q2))).
  rewrite <- (rig_mul_assoc (ring_rig W) (loc_fun q1 · loc_fun q2)).
  rewrite (rig_mul_assoc (ring_rig W) (loc_fun q1) (loc_fun q2)).
  rewrite (loc_fun_spec q2).
  rewrite (rig_mul_assoc (ring_rig W) (loc_fun q1) (ps (Qnum q2))).
  rewrite (loc_images_commute (Qnum q2) (Z.pos (Qden q1))).
  rewrite <- (rig_mul_assoc (ring_rig W) (loc_fun q1)
                (ps (Z.pos (Qden q1)))).
  rewrite (loc_fun_spec q1).
  rewrite <- rig_map_mul.
  reflexivity.
Qed.

Lemma loc_inv_one : loc_inv 1 ≈ rig_one (ring_rig W).
Proof.
  apply (rig_inv_unique (ring_rig W) (ps (Z.pos 1))).
  - apply loc_inv_l.
  - rewrite rig_mul_one_r.
    apply (rig_map_one psi).
Qed.

Definition loc_morphism :
  SetoidMorphism (rig_setoid (ring_rig Q_Ring)) (rig_setoid (ring_rig W)).
Proof.
  unshelve refine {| morphism := loc_fun |}.
  intros q1 q2 H.
  apply loc_fun_respects.
  exact H.
Defined.

Definition loc_hom : Q_Ring ~{Rng}~> W.
Proof.
  unshelve refine (@Build_RigHom (ring_rig Q_Ring) (ring_rig W)
    loc_morphism _ _ _ _); simpl.
  - unfold loc_fun; simpl.
    rewrite (rig_map_zero psi).
    apply rig_mul_zero_l.
  - exact loc_fun_add.
  - unfold loc_fun; simpl.
    rewrite loc_inv_one, (rig_map_one psi).
    apply rig_mul_one_r.
  - exact loc_fun_mul.
Defined.

Lemma loc_hom_factors (z : Z) : rig_map loc_hom (inject_Z z) ≈ ps z.
Proof.
  simpl; unfold loc_fun; simpl.
  rewrite loc_inv_one.
  apply rig_mul_one_r.
Qed.

(* Uniqueness, directly and not through [ZtoQ_epic]: any factorization satisfies [loc_fun]'s defining equation, and that equation cancels. / 唯一性，直接通过而不是通过 [ZtoQ_epic]：任何分解都满足 [loc_fun] 的定义方程，并且该方程被抵消。 *)
Lemma loc_hom_unique (v : Q_Ring ~{Rng}~> W) :
  (∀ z : Z, rig_map v (inject_Z z) ≈ ps z) → loc_hom ≈ v.
Proof.
  intros Hv q.
  apply (loc_cancel _ _ (Qden q)).
  simpl.
  rewrite loc_fun_spec.
  rewrite <- (Hv (Z.pos (Qden q))), <- (Hv (Qnum q)).
  rewrite <- rig_map_mul.
  apply (proper_morphism (rig_map v)).
  symmetry.
  exact (Q_num_den q).
Qed.

End Factor.

Definition ZtoQ_IsLocalization@{+} : IsLocalization ZtoQ PosZ.
Proof.
  split; [ exact ZtoQ_inverts |].
  intros W psi Hpsi.
  unshelve refine {| unique_obj := loc_hom W psi Hpsi |}.
  - intro z; exact (loc_hom_factors W psi Hpsi z).
  - intros v Hv.
    apply loc_hom_unique.
    intro z; exact (Hv z).
Defined.

(* A second proof of Instance/Rng.v's [ZtoQ_epic], through the lemma. / 通过引理，对 Instance/Rng.v 的 [ZtoQ_epic] 的第二个证明。 *)
Definition ZtoQ_epic_of_localization@{+} : Epic ZtoQ :=
  localization_epic ZtoQ PosZ ZtoQ_IsLocalization.

(* * ** The reflection at ℤ → ℚ is proper / * ** 在 ℤ → ℚ 的反射是适当的 *)

Require Import Coq.micromega.Lia.

(*
 ℤ itself is not in the subcategory: were the unit η at ℤ invertible,
 its inverse g would be ℤ-linear, and η 1 = 1 ⊗ 1 is twice the element
 (1/2)·(1 ⊗ 1) of the ℚ-module, so 1 = g (η 1) would be even. 

 --------
 ℤ 本身不在子范畴中：如果 ℤ 上的单位 η 可逆，其逆元素 g 将是 ℤ 线性的，而 η 1 = 1 ⊗ 1 是 ℚ 模的元素 (1/2)·(1 ⊗ 1) 的两倍，所以 1 = g(η 1) 将是偶数。
*)
Theorem ZMod_not_UnitFixed@{+} :
  sobj (RMod Int_Ring) (UnitFixed (extend_restrict_adjunction ZtoQ Q_central))
    (Ring_RMod Int_Ring) → False.
Proof.
  intros [g _ Hgf].
  pose (X := ExtendObj ZtoQ Q_central (Ring_RMod Int_Ring)).
  pose (y := ext_gen ZtoQ (Ring_RMod Int_Ring) (rig_one (ring_rig Q_Ring)) 1%Z
         : carrier (cmon_setoid (rm_ab X))).
  pose (z := rm_smul X (1 # 2)%Q y : carrier (cmon_setoid (rm_ab X))).
  assert (E1 : y ≈ rm_smul X (rig_map ZtoQ 2%Z) z).
  { unfold z.
    rewrite <- rm_smul_assoc.
    transitivity (rm_smul X (rig_one (ring_rig Q_Ring)) y).
    - symmetry; apply rm_smul_one.
    - apply rm_smul_respects; [ vm_compute; reflexivity | reflexivity ]. }
  pose proof (@rm_map_smul Int_Ring _ _ g 2%Z z) as Hlin.
  pose proof (proper_morphism (cmon_map (rm_hom g)) _ _ E1) as H2.
  assert (E : 1%Z = (2 * cmon_map (rm_hom g) z)%Z)
    by exact (eq_trans (eq_sym (Hgf 1%Z)) (eq_trans H2 Hlin)).
  lia.
Qed.
