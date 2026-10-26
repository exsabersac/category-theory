(*
   * * The dual space, the double dual, and the evaluation transformation

   The founding example of the subject.  Eilenberg and Mac Lane's 1945
   paper opens by contrasting two isomorphisms of a finite-dimensional
   vector space: the one with its dual, which exists but requires a
   basis, and the one with its double dual, which is given
   “simultaneously” for all spaces and mentions no basis.  The word
   they coined for the second phenomenon is “natural”, and the square
   they drew to define it is the naturality square of
   Theory/Natural/Transformation.v (whose header essay tells this
   story).  This file supplies the positive half of that contrast, in
   the vocabulary the library already has.

   SOURCES.  Mac Lane, “Categories for the Working Mathematician”, 2nd
   ed., §I.4 remark 2 (printed p. 17): the double-dual map is natural,
   the map to the dual is not.  §II.2 construction 3 (printed
   pp. 33-34): the dual as a CONTRAVARIANT functor on the category of
   ALL vector spaces over a field.  Awodey, “Category Theory”, 2nd ed.,
   §7.5 Example 7.12: the double-dual natural transformation, presented
   as the double transpose of the evaluation map.  Riehl, “Category
   Theory in Context”, §1.4 Example 1.4.4(i)-(ii): the dual functor and
   the evaluation transformation, with the remark that the family is
   natural for vector spaces of ANY dimension, and that only its
   INVERTIBILITY needs finite-dimensionality.  (The locations follow
   the convention of issue jwiegley/category-theory#256; the printed
   texts were not consulted while writing this file, so the page
   numbers repeat the issue's and are not independently claimed.)

   SCOPE, stated up front because it is the one decision that shapes
   the file.  Everything through [double_dual_natural] is developed over
   ALL F-modules — that is, over [Vct_F F], which is Instance/FdVect.v's
   name for [RMod (field_ring F)] and contains the
   infinite-dimensional spaces along with the rest.  So Mac Lane's
   §II.2 construction 3 is delivered at the generality he states it,
   and Riehl's “natural for vector spaces of any dimension” is a
   THEOREM here rather than an out-of-scope remark: [Dual],
   [DoubleDual], [eta] and [double_dual_natural] carry no
   finite-dimensionality hypothesis anywhere.  Finite dimension enters
   exactly once, at [double_dual_iso], and it enters as the CHOSEN
   COORDINATES that Instance/FdVect.v's [FdVectObject] carries — which
   is what lets the inverse be written down rather than merely shown to
   exist.  (That file's own header explains why a basis is data and not
   a theorem here; nothing below spends a choice principle.)

   WHAT THE DUAL IS.  V* is the module of linear maps V → F, where F is
   read as a module over itself — Instance/Mod.v's [Ring_RMod], which is
   the whole of the dualizing datum.  So the carrier of V* is
   [RModHom V (Ring_RMod (field_ring F))] and its setoid is
   Instance/Mod.v's [RModHom_Setoid] reused unchanged; addition, zero
   and negation of functionals are [rmod_hom_add], [rmod_hom_zero] and
   [rmod_hom_neg] (the last built here, from Structure/AbCategory.v's
   [ab_hom_neg] plus one linearity obligation).  Only the SCALAR ACTION
   is new, and it is the sole place in V*'s own construction where the
   base ring's COMMUTATIVITY is spent: (r·φ)(s·v) = r·s·φ(v) has to be
   s·r·φ(v) for r·φ to be linear, so [dual_smul_linear] calls
   [field_comm].  Over a non-commutative ring the dual of a left module
   is a right module, and that is exactly the step that would break.
   (Commutativity recurs in the finite-dimensional half, to slide a
   coefficient past a value: the file's four calls to [field_comm] are
   [dual_smul_linear], [dual_coeffs_smul], [dual_expand_coord] and the
   first triangle of [double_dual_iso], and there are no others.)

   EVALUATION.  [eta V] sends a vector v to the functional
   “evaluate at v”, φ ↦ φ(v).  Awodey presents this as the double
   transpose of the evaluation map V* × V → F; that reading is prose
   here and not a definition, because the library carries no cartesian
   closed structure on [Vct_F F] to transpose along (no tensor product
   of modules, hence no internal hom).  The literal definition is what
   is used.  Its naturality square commutes by [reflexivity] at each
   point — both sides are φ(f v) — which is the formal residue of the
   observation that no choice is made in defining it.

   THE FINITE-DIMENSIONAL HALF.  [DualFdObj V] equips V* with
   coordinates: the j-th coordinate of φ is its value at the j-th basis
   vector of V, and the tuple c is expanded to the functional
   v ↦ Σ_j c_j · (coordinates of v)_j.  Both round trips are basis
   bookkeeping over Instance/Matr.v's finite-sum engine and
   Instance/FdVect.v's [msum]/[msum_hom]/[msum_std]; the substantial
   one is [dual_expand_coord], φ ≈ Σ_j φ(e_j)·e^j, which is proved
   through [fdv_expand_msum] (a vector IS the sum of its coordinates
   against the basis) exactly as Instance/FdVect.v's [matrix_of_sur]
   proves fullness.  [double_dual_iso] then exhibits the two-sided
   inverse of [eta] explicitly, and [fd_dual_pointwise_iso] records
   that V and V* are isomorphic pointwise as well — the isomorphism
   that Eilenberg and Mac Lane point at and reject, obtained here by
   composing the coordinate isomorphisms through F^n, hence visibly
   basis-dependent.

   THE NEGATIVE HALF is NOT here.  That V ≅ V* cannot be made natural
   is the refutation, and it lives in Instance/FdVect/NonNatural.v;
   Riehl's Example 1.4.4(vii), the tensor-hom side, is in
   Instance/FdVect/Tensor.v.  Both are separate files by design, so
   that the positive results above stay free of the machinery a
   refutation needs.

   THE STAR-AUTONOMOUS CONNECTION, stated exactly.
   Structure/Monoidal/StarAutonomous.v defines [double_dual d :=
   dual d ◯ (dual d)^op] over a symmetric monoidal closed base, and its
   class asks for [star_double_dual], an isomorphism from x to its
   double dual, together with the naturality field [star_natural].
   [DoubleDual] below is built in the same shape,
   and [double_dual_natural] and [double_dual_iso] are the two fields'
   concrete analogues, so this file is the INHABITANT PATTERN that
   class has otherwise been asserted to have.  It is NOT an instance of
   the class and does not claim to be: [StarAutonomous] is stated over
   [SymMonClosed], which [Vct_F F] lacked when this was written; since
   Instance/Mod/Closed.v's [RMod_SymMonClosed] (2026-08-31) it has
   one, and Instance/FdVect/NoRightAdjoint.v (#433) reads StarAutonomous.v's
   [dual] off it: isomorphic to [Dual] ([dual_iso359]), not convertible.

   One packaging note in the same spirit: the headline is delivered
   as a PAIR — [double_dual_natural] (a transformation at [Vct_F],
   any dimension) and [double_dual_iso] (per finite-dimensional
   object) — and no single [FdVect]-level “natural isomorphism”
   artifact bundles them.  There is no obstruction: [DualFd ◯
   (DualFd)^op] typechecks with its object action computing to
   [DualFdObj (DualFdObj −)] by [eq_refl], and its evaluation
   transformation would have the same components; the pair is what
   the issue's verification block names, so the bundle is left as a
   mechanical corollary rather than built. 

   --------
   * * 对偶空间、双重对偶和评估变换

   该主题的奠基示例。Eilenberg 和 Mac Lane 在 1945 年的论文开头，通过对比有限维向量空间的两种同构来展开讨论：一种是与其对偶空间的同构，这种同构存在但需要基底；另一种是与其双重对偶空间的同构，这种同构对所有空间都是“同时”给出的，并且不提及任何基底。他们为第二种现象创造的词是“自然”(natural)，他们画出的定义该现象的方框图就是 Theory/Natural/Transformation.v 中的自然性方框图（其头部文章讲述了这个故事）。该文件提供了这种对比的正面部分，使用的是库中已有的词汇。来源。Mac Lane，《为了工作的数学家而写的范畴论》，第2版，第I.4节 注释2（印刷版第17页）：双对偶映射是自然的，而到对偶的映射不是自然的。第II.2节 构造3（印刷版第33-34页）：作为一个在所有域上向量空间范畴上的逆变函子。Awodey，《范畴论》，第2版，第7.5节 示例7.12：双对偶自然变换，以评价映射的双转置形式呈现。Riehl，《语境中的范畴论》，第1.4节 示例1.4.4(i)-(ii)：对偶函子和评价变换，并备注该族对任何维数的向量空间都是自然的，并且只有其可逆性需要有限维。（位置遵循 jwiegley/category-theory#256 期刊的惯例；在编写此文件时未查阅印刷文本，因此页码重复了期刊的页码，并非独立标注。）范围，一开始就说明，因为这是决定整个文件结构的关键决策。从 [double_dual_natural] 开始的所有内容都是在所有 F-模上开发的——也就是在 [Vct_F F] 上开发的，这是 Instance/FdVect.v 对 [RMod (field_ring F)] 的命名，并包含无限维空间以及其他内容。因此，Mac Lane §II.2 构造 3 在他所陈述的一般性下被实现，而 Riehl 所说的“对任意维度的向量空间自然”在这里是定理，而不是超出范围的备注：[Dual]、[DoubleDual]、[eta] 和 [double_dual_natural] 根本不携带任何有限维假设。有限维度只在 [double_dual_iso] 处出现，而且是作为 Instance/FdVect.v 的 [FdVectObject] 所携带的所选坐标——这正是使得逆可以写出来，而不仅仅是被证明存在的原因。（该文件的标题本身解释了为什么基础在这里是数据而不是定理；下面的内容没有用到选择公理。）什么是对偶。V* 是从 V 到 F 的线性映射的模，其中 F 被看作是自身上的模——Instance/Mod.v 中的 [Ring_RMod]，这就是整个对偶化数据。因此 V* 的承载集合是 [RModHom V (Ring_RMod (field_ring F))]，其集合论等价关系是 Instance/Mod.v 中的 [RModHom_Setoid] 不变复用；函数的加法、零元素和取反分别是 [rmod_hom_add]、[rmod_hom_zero] 和 [rmod_hom_neg]（最后一个在此构建，来自 Structure/AbCategory.v 的 [ab_hom_neg] 加上一个线性义务）。唯一新的部分是标量作用，这是 V* 自身构造中唯一需要使用基环交换性的位置：(r·φ)(s·v) = r·s·φ(v) 为了使 r·φ 线性，必须是 s·r·φ(v)，因此 [dual_smul_linear] 调用了 [field_comm]。在非交换环上，左模的对偶是右模，这正是会出问题的一步。(交换性在有限维部分中反复出现，用于将系数滑过一个数值：文件中对 [field_comm] 的四次调用是 [dual_smul_linear]、[dual_coeffs_smul]、[dual_expand_coord] 以及 [double_dual_iso] 的第一个三角形，并且没有其他调用。)评估。[eta V] 将向量 v 发送到泛函“在 v 处求值”，即 φ ↦ φ(v)。Awodey 将其表示为评估映射 V* × V → F 的双重转置；这种理解在这里是说明性的，而不是定义，因为库中没有 [Vct_F F] 的笛卡尔闭结构可供转置（没有模的张量积，因此也没有内部 Hom）。实际使用的是字面定义。它的自然性平方在每个点上由 [reflexivity] 交换——两边都是 φ(f v)——这是观察到定义中没有做任何选择的形式残余。有限维部分。[DualFdObj V] 为 V* 配置坐标：φ 的第 j 个坐标是其在 V 的第 j 个基向量上的取值，且元组 c 被展开为函数 v ↦ Σ_j c_j · (v 的坐标)_j。两个往返转换都是 Instance/Matr.v 的有限求和引擎和 Instance/FdVect.v 的 [msum] / [msum_hom] / [msum_std] 上的基底记录工作；实质性的部分是 [dual_expand_coord]，φ ≈ Σ_j φ(e_j)·e^j，通过 [fdv_expand_msum] 证明（一个向量就是其在基下坐标的和），正如 Instance/FdVect.v 的 [matrix_of_sur] 证明其完备性一样。[double_dual_iso] 然后明确展示了 [eta] 的双向逆，而 [fd_dual_pointwise_iso] 记录了 V 和 V* 在逐点意义下也是同构的——这是 Eilenberg 和 Mac Lane 指出并否定的同构，这里通过通过 F^n 组合坐标同构得到，因此显然依赖基底。

   负半部分不存在。V ≅ V* 无法自然化是驳斥的内容，它位于 Instance/FdVect/NonNatural.v；Riehl 的例子 1.4.4(vii)，张量-同构方面，位于 Instance/FdVect/Tensor.v。这两个文件是分开设计的，因此上述正面结果保持不受驳斥所需机制的影响。星自主连接，精确定义。Structure/Monoidal/StarAutonomous.v 在对称单模闭基上定义了 [double_dual d := dual d ◯ (dual d)^op]，其类要求 [star_double_dual]，一个从 x 到其双重对偶的同构，以及自然性字段 [star_natural]。下面的 [DoubleDual] 以相同的形式构建，而 [double_dual_natural] 和 [double_dual_iso] 则是两个字段的具体对应物，因此这个文件是类本应声明拥有的驻留者模式。它不是该类的实例，也没有声称是：[StarAutonomous] 是在 [SymMonClosed] 上声明的，而 [Vct_F F] 在编写时缺少它；自 Instance/Mod/Closed.v 的 [RMod_SymMonClosed]（2026-08-31）以来，它已有一个，而 Instance/FdVect/NoRightAdjoint.v (#433) 从 StarAutonomous.v 的 [dual] 上读取它：同构于 [Dual]（[dual_iso359]），不可转换。同样精神下的一个包装说明：标题是成对提供的——[double_dual_natural]（在[Vct_F]处的一个变换，任何维度）和[double_dual_iso]（每个有限维对象）——没有单一的[FdVect]级“自然同构”工件将它们捆绑起来。不存在障碍：[DualFd ◯ (DualFd)^op] 类型检查其对象作用计算为[DualFdObj (DualFdObj −)]，通过[eq_refl]，其评价变换会有相同的分量；这对是问题的验证块所命名的，因此捆绑被保留为一个机械推论，而不是构建的。
*)

(*
 [Coq.QArith.QArith] is imported FIRST, mirroring Instance/FdVect.v's
 import order and for its reason: it exports
 [Corelib.Relations.Relation_Definitions.equiv], which would otherwise
 shadow [Category.Lib.Setoid.equiv] and break every [Proper] signature
 below. 

 --------
 [Coq.QArith.QArith] 首先被导入，镜像 Instance/FdVect.v 的导入顺序以及其原因：它导出 [Corelib.Relations.Relation_Definitions.equiv]，否则 [Category.Lib.Setoid.equiv] 会被遮蔽，并且会破坏下面的每个 [Proper] 签名。
*)
Require Import Coq.QArith.QArith.
Require Import Coq.Vectors.Fin.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.
Require Import Category.Instance.FdVect.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * ** Negation of a module homomorphism

   Instance/Mod.v supplies pointwise addition and the zero map
   ([rmod_hom_add], [rmod_hom_zero], for its [RMod_Preadditive]
   instance) but no negation, [Preadditive] not demanding one.  The
   group part is Structure/AbCategory.v's [ab_hom_neg]; the only new
   obligation is that the negated map is still linear, which is
   Instance/Mod.v's [rm_smul_neg_r]. 

   --------
   * ** 模同态的取反

   Instance/Mod.v 提供了逐点加法和零映射
   （[rmod_hom_add]、[rmod_hom_zero]，用于它的[RMod_Preadditive]实例），但没有取反操作，[Preadditive] 并未要求提供。群部分来自 Structure/AbCategory.v 的 [ab_hom_neg]；唯一新增的义务是取反后的映射仍然是线性的，这一点由 Instance/Mod.v 的 [rm_smul_neg_r] 提供。
*)
Program Definition rmod_hom_neg {R : RingObject} {M N : RModObject R}
        (f : RModHom M N) : RModHom M N := {|
  rm_hom := ab_hom_neg (rm_hom f)
|}.
Next Obligation.
  intros R M N f r m; simpl.
  rewrite (rm_map_smul f r m).
  symmetry; apply rm_smul_neg_r.
Qed.

Section DualSpace.

Context (F : FieldObject).

(*
   * ** The dual module V*

   Its carrier is the linear functionals V → F, with F read as a module
   over itself; its setoid is Instance/Mod.v's, so two functionals are
   the same when they agree pointwise. 

   --------
   * ** 对偶模 V*

   它的载体是线性泛函 V → F，其中 F 被视为自身上的模；它的集合类型是 Instance/Mod.v 中的集合类型，因此当两个泛函在每一点上都相等时，它们被认为相同。
*)

Definition dual_setoid (V : RModObject (field_ring F)) : SetoidObject := {|
  carrier   := RModHom V (Ring_RMod (field_ring F));
  is_setoid := @RModHom_Setoid (field_ring F) V (Ring_RMod (field_ring F))
|}.

(*
   * Addition and the zero functional are Instance/Mod.v's, so every
   monoid law is the corresponding law of F applied at each vector. 

   --------
   * 加法和零函数是 Instance/Mod.v 的，所以每个幺半群定律都是在每个向量上应用的 F 的相应定律。
*)
Program Definition dual_cmon (V : RModObject (field_ring F)) :
  CMonObject := {|
  cmon_setoid := dual_setoid V;
  cmon_zero   := @rmod_hom_zero (field_ring F) V (Ring_RMod (field_ring F));
  cmon_plus   := @rmod_hom_add (field_ring F) V (Ring_RMod (field_ring F))
|}.
Next Obligation.
  intros V f f' Hf g g' Hg v; simpl.
  now rewrite (Hf v), (Hg v).
Qed.
Next Obligation. intros V f g h v; simpl; apply rig_add_assoc. Qed.
Next Obligation. intros V f g v; simpl; apply rig_add_comm. Qed.
Next Obligation. intros V f v; simpl; apply rig_add_zero_l. Qed.

Program Definition dual_ab (V : RModObject (field_ring F)) : AbObject := {|
  ab_cmon := dual_cmon V;
  ab_neg  := @rmod_hom_neg (field_ring F) V (Ring_RMod (field_ring F))
|}.
Next Obligation.
  intros V f g Hfg v; simpl.
  now rewrite (Hfg v).
Qed.
Next Obligation. intros V f v; simpl; apply (ring_neg_l F). Qed.

(*
   * *** The scalar action, and the one use of commutativity

   (r·φ)(v) := r · φ(v).  Preservation of zero and of addition are
   annihilation and distributivity in F.  The remaining law — that r·φ
   is still LINEAR — is where the base ring's commutativity is spent:
   (r·φ)(s·v) computes to r·(s·φ(v)), and linearity demands
   s·(r·φ(v)). 

   --------
   * *** 标量作用，以及交换律的唯一用途

   (r·φ)(v) := r · φ(v)。零元和加法的保持在 F 中表现为消去性和分配律。剩下的规律——即 r·φ 仍然是线性的——则需要基环的交换律来实现：(r·φ)(s·v) 计算为 r·(s·φ(v))，而线性性要求 s·(r·φ(v))。
*)

Lemma dual_smul_zero (V : RModObject (field_ring F))
  (r : carrier (rig_setoid F)) (f : RModHom V (Ring_RMod (field_ring F))) :
  rig_mul F r (cmon_map (rm_hom f) (cmon_zero V)) ≈ rig_zero F.
Proof.
  rewrite (cmon_map_zero (rm_hom f)).
  apply rig_mul_zero_r.
Qed.

Lemma dual_smul_plus (V : RModObject (field_ring F))
  (r : carrier (rig_setoid F)) (f : RModHom V (Ring_RMod (field_ring F))) :
  ∀ v w, rig_mul F r (cmon_map (rm_hom f) (cmon_plus V v w))
           ≈ rig_add F (rig_mul F r (cmon_map (rm_hom f) v))
                       (rig_mul F r (cmon_map (rm_hom f) w)).
Proof.
  intros v w.
  rewrite (cmon_map_plus (rm_hom f) v w).
  apply rig_distr_l.
Qed.

Lemma dual_smul_linear (V : RModObject (field_ring F))
  (r : carrier (rig_setoid F)) (f : RModHom V (Ring_RMod (field_ring F))) :
  ∀ s v, rig_mul F r (cmon_map (rm_hom f) (rm_smul V s v))
           ≈ rig_mul F s (rig_mul F r (cmon_map (rm_hom f) v)).
Proof.
  intros s v.
  rewrite (rm_map_smul f s v).
  rewrite <- (rig_mul_assoc F r s (cmon_map (rm_hom f) v)).
  rewrite (field_comm F r s).
  apply (rig_mul_assoc F s r (cmon_map (rm_hom f) v)).
Qed.

Program Definition dual_smul (V : RModObject (field_ring F))
        (r : carrier (rig_setoid F))
        (f : RModHom V (Ring_RMod (field_ring F))) :
  RModHom V (Ring_RMod (field_ring F)) := {|
  rm_hom := {|
    cmon_map      := {| morphism := fun v =>
                          rig_mul F r (cmon_map (rm_hom f) v) |};
    cmon_map_zero := dual_smul_zero V r f;
    cmon_map_plus := dual_smul_plus V r f
  |};
  rm_map_smul := dual_smul_linear V r f
|}.
Next Obligation.
  intros V r f v w Hvw; simpl.
  now rewrite Hvw.
Qed.

(*
   * Mac Lane §II.2 construction 3's object assignment: the dual of an
   ARBITRARY F-module, with no finiteness hypothesis. 

   --------
   * Mac Lane §II.2 构造3的对象赋值：任意F-模的对偶，没有有限性假设。
*)
Program Definition DualMod (V : RModObject (field_ring F)) :
  RModObject (field_ring F) := {|
  rm_ab   := dual_ab V;
  rm_smul := dual_smul V
|}.
Next Obligation.
  intros V r s Hrs f g Hfg v; simpl.
  now rewrite Hrs, (Hfg v).
Qed.
Next Obligation. intros V r f g v; simpl; apply rig_distr_l. Qed.
Next Obligation. intros V r s f v; simpl; apply rig_distr_r. Qed.
Next Obligation. intros V r s f v; simpl; apply rig_mul_assoc. Qed.
Next Obligation. intros V f v; simpl; apply rig_mul_one_l. Qed.

(*
   * ** The dual functor

   On arrows the dual acts by PRECOMPOSITION, which is why it is
   contravariant: f : V → W carries a functional on W to one on V.
   Every law below is [reflexivity] at each vector, composition of
   functions being associative on the nose. 

   --------
   * ** 双对函子

   对箭头来说，双对函子通过**前合成**作用，这就是它为什么是逆变的原因：f : V → W 将 W 上的一个泛函带到 V 上的一个泛函。
   下面的每条定律在每个向量上都是  [reflexivity] ，函数的复合在形式上是结合的。
*)

Definition dual_precompose {V W : RModObject (field_ring F)}
  (f : RModHom V W) : RModHom (DualMod W) (DualMod V).
Proof.
  unshelve notypeclasses refine
    (@Build_RModHom (field_ring F) (DualMod W) (DualMod V)
       (@Build_CMonHom (dual_cmon W) (dual_cmon V)
          (@Build_SetoidMorphism _ _ _ _
             (fun g => @rmod_hom_compose (field_ring F) V W
                         (Ring_RMod (field_ring F)) g f) _) _ _) _).
  - intros g g' Hg v; exact (Hg _).
  - intro v; reflexivity.
  - intros g h v; reflexivity.
  - intros r g v; reflexivity.
Defined.

(*
   * Mac Lane §II.2 construction 3 / Riehl §1.4 Example 1.4.4(i): the
   dual as a contravariant functor on ALL F-vector spaces. 

   --------
   * Mac Lane §II.2 构造 3 / Riehl §1.4 示例 1.4.4(i)：作为对所有 F-向量空间的逆变函子的对偶。
*)
Program Definition Dual : (Vct_F F)^op ⟶ Vct_F F := {|
  fobj := DualMod;
  fmap := fun V W (f : W ~{Vct_F F}~> V) => dual_precompose f
|}.
Next Obligation.
  intros V W f g Hfg h v; simpl.
  apply (proper_morphism (cmon_map (rm_hom h))).
  exact (Hfg v).
Qed.
Next Obligation. intros V f v; simpl; reflexivity. Qed.
Next Obligation. intros V W X f g h v; simpl; reflexivity. Qed.

(*
   * The double dual, in the shape Structure/Monoidal/StarAutonomous.v
   gives [double_dual]: the contravariant functor composed with its own
   opposite, which is covariant. 

   --------
   * 在 Structure/Monoidal/StarAutonomous.v 中的双对偶  
   给出了 [double_dual]：与其自身对偶组合的逆变函子，它是协变的。
*)
Definition DoubleDual : Vct_F F ⟶ Vct_F F := Dual ◯ Dual^op.

(* * ** Evaluation [eta V] sends a vector to “evaluate at it”. Each law is the corresponding law of the functional being evaluated, so the family is defined without reference to any basis — which is what will make it natural. / * ** 评估 [eta V] 发送一个向量去“在其上评估”。每条律都是被评估的函数对应的律，所以这个族的定义不依赖于任何基——这正是使其自然的原因。 *)

Program Definition dual_ev (V : RModObject (field_ring F))
        (v : carrier (cmon_setoid V)) :
  RModHom (DualMod V) (Ring_RMod (field_ring F)) := {|
  rm_hom := {|
    cmon_map      := {| morphism := fun f => cmon_map (rm_hom f) v |};
    cmon_map_zero := reflexivity _;
    cmon_map_plus := fun f g => reflexivity _
  |};
  rm_map_smul := fun r f => reflexivity _
|}.
Next Obligation. intros V v f g Hfg; simpl; exact (Hfg v). Qed.

Program Definition eta (V : RModObject (field_ring F)) :
  V ~{Vct_F F}~> DoubleDual V := {|
  rm_hom := {|
    cmon_map := {| morphism := dual_ev V |}
  |}
|}.
Next Obligation.
  intros V v w Hvw f; simpl.
  apply (proper_morphism (cmon_map (rm_hom f))).
  exact Hvw.
Qed.
Next Obligation. intros V f; simpl; apply (cmon_map_zero (rm_hom f)). Qed.
Next Obligation.
  intros V v w f; simpl.
  apply (cmon_map_plus (rm_hom f) v w).
Qed.
Next Obligation. intros V r v f; simpl; apply (rm_map_smul f r v). Qed.

(*
   * Mac Lane §I.4 remark 2 / Awodey §7.5 Example 7.12 / Riehl §1.4
   Example 1.4.4(ii): evaluation is NATURAL, at every dimension.  Both
   orientations of the square hold by [reflexivity] at each vector and
   each functional — both composites send (v, φ) to φ(f v) — and no
   hypothesis on V, W or f is used. 

   --------
   * Mac Lane §I.4 注释 2 / Awodey §7.5 示例 7.12 / Riehl §1.4  
   示例 1.4.4(ii)：在每一个维度上，评估是自然的。正方形的两种方向在每个向量和每个泛函上都由 [reflexivity] 成立——两个复合映射都将 (v, φ) 映射为 φ(f v)——且没有使用关于 V、W 或 f 的任何假设。
*)
Program Definition double_dual_natural : Id[Vct_F F] ⟹ DoubleDual := {|
  transform := eta
|}.
Next Obligation. intros V W f v g; simpl; reflexivity. Qed.
Next Obligation. intros V W f v g; simpl; reflexivity. Qed.

End DualSpace.

(*
   * ** The finite-dimensional half

   Everything above is basis-free.  From here on the CHOSEN
   COORDINATES of Instance/FdVect.v's [FdVectObject] are used, and only
   they: no space is assumed to have a basis, since carrying one is
   what being an object of [FdVect F] means. 

   --------
   * ** 有限维的一半

   上面的一切都是无基的。从这里开始，使用了 Instance/FdVect.v 的 [FdVectObject] 的所选坐标，并且仅使用它们：不假设空间有基，因为携带一个基正是作为 [FdVect F] 对象的意义所在。
*)

Section FiniteDimensional.

Context (F : FieldObject).

(*
   * The j-th basis vector: the expansion of the j-th standard tuple.
   Instance/FdVect.v's [std_basis] is Instance/Matr.v's Kronecker
   [delta], reused, so the collapse lemmas apply to it directly. 

   --------
   * 第 j 个基向量：第 j 个标准元组的展开。  
   Instance/FdVect.v 的 [std_basis] 是 Instance/Matr.v 的 Kronecker [delta] ，被重复使用，因此坍塌引理可以直接应用于它。
*)
Definition fdv_basis (V : FdVectObject F) (j : Fin.t (fdv_dim V)) :
  carrier (cmon_setoid (fdv_mod V)) :=
  fdv_expand V (std_basis F (fdv_dim V) j).

(*
   * In the ring read as a module over itself, Instance/FdVect.v's
   commutative-monoid sum IS Instance/Matr.v's [fin_sum]: the two
   recursions coincide, the monoid operations of [Ring_RMod] being the
   rig's own.  One induction, and the rest of the file may move between
   the two vocabularies freely. 

   --------
   * 在作为自身的模的环中阅读，Instance/FdVect.v 的交换幺半群和为 Instance/Matr.v 的 [fin_sum]：两个递归一致，[Ring_RMod] 的幺半群运算就是环自身的运算。一种归纳法，其余文件可以在这两种词汇之间自由切换。
*)
Lemma msum_ring {p : nat} (f : Fin.t p → carrier (rig_setoid F)) :
  msum (ab_cmon (rm_ab (Ring_RMod (field_ring F)))) f
    ≈ fin_sum (field_ring F) f.
Proof.
  revert f.
  induction p as [| k IHk]; intros f; simpl.
  - reflexivity.
  - apply rig_add_respects; [ reflexivity |].
    apply (IHk (fun i => f (Fin.FS i))).
Qed.

(*
   * A vector IS the sum of its coordinates against the basis.  This is
   Instance/FdVect.v's [std_expand] transported along the chosen
   coordinates: expand the standard tuple, push [fdv_expand] through
   the sum by [msum_hom] at [std_expand_hom], and read the result
   coordinatewise by [msum_std]. 

   --------
   * 向量就是其坐标在基底下的和。这是 Instance/FdVect.v 的 [std_expand] 沿所选坐标的传递：展开标准元组，通过 [msum_hom] 在 [std_expand_hom] 推动 [fdv_expand] 通过求和，并通过 [msum_std] 按坐标读取结果。
*)
Lemma fdv_expand_msum (V : FdVectObject F)
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  fdv_expand V c
    ≈ msum (fdv_mod V)
        (fun j => rm_smul (fdv_mod V) (c j) (fdv_basis V j)).
Proof.
  transitivity (fdv_expand V
    (msum (std_cmon F (fdv_dim V))
       (fun j i => rig_mul F (c j) (std_basis F (fdv_dim V) j i)))).
  { apply fdv_expand_respects; intro i.
    symmetry.
    transitivity (fin_sum (field_ring F)
      (fun j => rig_mul F (c j) (std_basis F (fdv_dim V) j i))).
    - apply (msum_std F
               (fun j i => rig_mul F (c j) (std_basis F (fdv_dim V) j i)) i).
    - transitivity (fin_sum (field_ring F)
        (fun j => rig_mul F (c j) (delta (field_ring F) j i))).
      + apply fin_sum_respects; intro j.
        apply rig_mul_respects; [ reflexivity |].
        apply delta_sym.
      + apply (fin_sum_delta_r (field_ring F) i c). }
  transitivity (msum (fdv_mod V)
    (fun j => fdv_expand V
                (fun i => rig_mul F (c j) (std_basis F (fdv_dim V) j i)))).
  { apply (msum_hom (rm_hom (std_expand_hom F V))
             (fun j i => rig_mul F (c j) (std_basis F (fdv_dim V) j i))). }
  apply msum_respects; intro j.
  apply (fdv_expand_smul V (c j) (std_basis F (fdv_dim V) j)).
Qed.

(*
   * A functional applied to an expanded tuple: linearity spent once,
   against the expansion above. 

   --------
   * 作用于展开元组的函数式：线性使用一次，针对上面的展开。
*)
Lemma dual_apply_expand (V : FdVectObject F)
  (f : RModHom (fdv_mod V) (Ring_RMod (field_ring F)))
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  cmon_map (rm_hom f) (fdv_expand V c)
    ≈ fin_sum (field_ring F)
        (fun j => rig_mul F (c j)
                    (cmon_map (rm_hom f) (fdv_basis V j))).
Proof.
  transitivity (cmon_map (rm_hom f)
    (msum (fdv_mod V)
       (fun j => rm_smul (fdv_mod V) (c j) (fdv_basis V j)))).
  { apply (proper_morphism (cmon_map (rm_hom f))).
    apply fdv_expand_msum. }
  transitivity (msum (ab_cmon (rm_ab (Ring_RMod (field_ring F))))
    (fun j => cmon_map (rm_hom f)
                (rm_smul (fdv_mod V) (c j) (fdv_basis V j)))).
  { apply (msum_hom (rm_hom f)
             (fun j => rm_smul (fdv_mod V) (c j) (fdv_basis V j))). }
  transitivity (msum (ab_cmon (rm_ab (Ring_RMod (field_ring F))))
    (fun j => rig_mul F (c j) (cmon_map (rm_hom f) (fdv_basis V j)))).
  { apply msum_respects; intro j.
    apply (rm_map_smul f (c j) (fdv_basis V j)). }
  apply msum_ring.
Qed.

(*
   * *** The dual basis

   The tuple c is expanded to the functional v ↦ Σ_j c_j · v_j, where
   v_j are v's chosen coordinates.  Linearity of that functional is
   linearity of [fdv_coord] under the sum, with [dual_coeffs_smul]
   spending commutativity to slide the scalar out of the sum. 

   --------
   * *** 对偶基

   元组 c 被展开为函数 v ↦ Σ_j c_j · v_j，其中
   v_j 是 v 的所选坐标。该函数的线性性是
   在求和下 [fdv_coord] 的线性性，并且 [dual_coeffs_smul]
   利用交换性将标量移出求和符号。
*)

Lemma dual_coeffs_zero (V : FdVectObject F)
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  fin_sum (field_ring F)
    (fun j => rig_mul F (c j) (fdv_coord V (cmon_zero (fdv_mod V)) j))
    ≈ rig_zero F.
Proof.
  transitivity (fin_sum (field_ring F)
    (fun _ : Fin.t (fdv_dim V) => rig_zero F)).
  - apply fin_sum_respects; intro j.
    rewrite (fdv_coord_zero V j).
    apply rig_mul_zero_r.
  - apply fin_sum_zero.
Qed.

Lemma dual_coeffs_plus (V : FdVectObject F)
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  ∀ v w, fin_sum (field_ring F)
           (fun j => rig_mul F (c j)
                       (fdv_coord V (cmon_plus (fdv_mod V) v w) j))
         ≈ rig_add F
             (fin_sum (field_ring F)
                (fun j => rig_mul F (c j) (fdv_coord V v j)))
             (fin_sum (field_ring F)
                (fun j => rig_mul F (c j) (fdv_coord V w j))).
Proof.
  intros v w.
  transitivity (fin_sum (field_ring F)
    (fun j => rig_add F (rig_mul F (c j) (fdv_coord V v j))
                        (rig_mul F (c j) (fdv_coord V w j)))).
  - apply fin_sum_respects; intro j.
    rewrite (fdv_coord_plus V v w j).
    apply rig_distr_l.
  - apply fin_sum_add.
Qed.

Lemma dual_coeffs_smul (V : FdVectObject F)
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  ∀ r v, fin_sum (field_ring F)
           (fun j => rig_mul F (c j)
                       (fdv_coord V (rm_smul (fdv_mod V) r v) j))
         ≈ rig_mul F r
             (fin_sum (field_ring F)
                (fun j => rig_mul F (c j) (fdv_coord V v j))).
Proof.
  intros r v.
  transitivity (fin_sum (field_ring F)
    (fun j => rig_mul F r (rig_mul F (c j) (fdv_coord V v j)))).
  - apply fin_sum_respects; intro j.
    rewrite (fdv_coord_smul V r v j).
    rewrite <- (rig_mul_assoc F (c j) r (fdv_coord V v j)).
    rewrite (field_comm F (c j) r).
    apply (rig_mul_assoc F r (c j) (fdv_coord V v j)).
  - symmetry; apply fin_sum_mul_l.
Qed.

Program Definition dual_of_coeffs (V : FdVectObject F)
        (c : Fin.t (fdv_dim V) → carrier (rig_setoid F)) :
  RModHom (fdv_mod V) (Ring_RMod (field_ring F)) := {|
  rm_hom := {|
    cmon_map      := {| morphism := fun v => fin_sum (field_ring F)
                          (fun j => rig_mul F (c j) (fdv_coord V v j)) |};
    cmon_map_zero := dual_coeffs_zero V c;
    cmon_map_plus := dual_coeffs_plus V c
  |};
  rm_map_smul := dual_coeffs_smul V c
|}.
Next Obligation.
  intros V c v w Hvw; simpl.
  apply fin_sum_respects; intro j.
  apply rig_mul_respects; [ reflexivity |].
  exact (fdv_coord_respects V v w Hvw j).
Qed.

(*
   * The first round trip: the coefficients of an expanded tuple are the
   tuple back, because the j-th basis vector has coordinates delta. 

   --------
   * 第一次往返：展开元组的系数是元组本身，因为第 j 个基向量的坐标是 delta。
*)
Lemma dual_coord_expand (V : FdVectObject F)
  (c : Fin.t (fdv_dim V) → carrier (rig_setoid F))
  (i : Fin.t (fdv_dim V)) :
  cmon_map (rm_hom (dual_of_coeffs V c)) (fdv_basis V i) ≈ c i.
Proof.
  simpl.
  transitivity (fin_sum (field_ring F)
    (fun j => rig_mul F (c j) (delta (field_ring F) j i))).
  - apply fin_sum_respects; intro j.
    apply rig_mul_respects; [ reflexivity |].
    apply (fdv_coord_expand V (std_basis F (fdv_dim V) i) j).
  - apply (fin_sum_delta_r (field_ring F) i c).
Qed.

(*
   * The second round trip, the substantial one: a functional IS the sum
   of its values at the basis against the coordinate functionals.
   Expand v in the basis, apply f through the sum, and commute. 

   --------
   * 第二次往返，实质性的那次：一个泛函 IS 等于它在基上对坐标泛函的值的总和。将 v 在基中展开，通过求和应用 f，然后交换顺序。
*)
Lemma dual_expand_coord (V : FdVectObject F)
  (f : RModHom (fdv_mod V) (Ring_RMod (field_ring F)))
  (v : carrier (cmon_setoid (fdv_mod V))) :
  cmon_map (rm_hom (dual_of_coeffs V
    (fun j => cmon_map (rm_hom f) (fdv_basis V j)))) v
    ≈ cmon_map (rm_hom f) v.
Proof.
  simpl.
  transitivity (fin_sum (field_ring F)
    (fun j => rig_mul F (fdv_coord V v j)
                (cmon_map (rm_hom f) (fdv_basis V j)))).
  { apply fin_sum_respects; intro j.
    apply field_comm. }
  symmetry.
  transitivity (cmon_map (rm_hom f) (fdv_expand V (fdv_coord V v))).
  { apply (proper_morphism (cmon_map (rm_hom f))).
    symmetry; apply fdv_expand_coord. }
  apply (dual_apply_expand V f (fdv_coord V v)).
Qed.

(*
   * V* with coordinates: same dimension, the j-th coordinate of a
   functional being its value at the j-th basis vector. 

   --------
   * V* 的坐标：相同维度，第 j 个坐标是函数在第 j 个基向量上的值。
*)
Program Definition DualFdObj (V : FdVectObject F) : FdVectObject F := {|
  fdv_mod    := DualMod F (fdv_mod V);
  fdv_dim    := fdv_dim V;
  fdv_coord  := fun f j => cmon_map (rm_hom f) (fdv_basis V j);
  fdv_expand := dual_of_coeffs V
|}.
Next Obligation. intros V f g Hfg i; exact (Hfg _). Qed.
Next Obligation.
  intros V c d Hcd v; simpl.
  apply fin_sum_respects; intro j.
  apply rig_mul_respects; [ apply Hcd | reflexivity ].
Qed.
Next Obligation. intros V c i; apply dual_coord_expand. Qed.
Next Obligation. intros V f v; apply dual_expand_coord. Qed.
Next Obligation. intros V f g i; simpl; reflexivity. Qed.
Next Obligation. intros V r f i; simpl; reflexivity. Qed.

(*
   * The dual functor restricted to the finite-dimensional category: the
   same arrow action, precomposition, since a hom of [FdVect F] IS a
   hom of the underlying modules. 

   --------
   * 双函子限制到有限维范畴：相同的箭头作用，预组合，因为  [FdVect F] 的一个同态是其底层模的一个同态。
*)
Program Definition DualFd : (FdVect F)^op ⟶ FdVect F := {|
  fobj := DualFdObj;
  fmap := fun V W (f : W ~{FdVect F}~> V) => dual_precompose F f
|}.
Next Obligation.
  intros V W f g Hfg h v; simpl.
  apply (proper_morphism (cmon_map (rm_hom h))).
  exact (Hfg v).
Qed.
Next Obligation. intros V f v; simpl; reflexivity. Qed.
Next Obligation. intros V W X f g h v; simpl; reflexivity. Qed.

(*
   * The j-th vector of the dual basis is the j-th coordinate
   functional — the equation that names it a dual basis. 

   --------
   * 对偶基的第 j 个向量是第 j 个坐标函数——命名它为对偶基的方程。
*)
Lemma dual_basis_coord (V : FdVectObject F) (j : Fin.t (fdv_dim V))
  (v : carrier (cmon_setoid (fdv_mod V))) :
  cmon_map (rm_hom (fdv_basis (DualFdObj V) j)) v ≈ fdv_coord V v j.
Proof.
  unfold fdv_basis; simpl.
  transitivity (fin_sum (field_ring F)
    (fun l => rig_mul F (delta (field_ring F) j l) (fdv_coord V v l))).
  - apply fin_sum_respects; intro l.
    apply rig_mul_respects; [ apply delta_sym | reflexivity ].
  - apply (fin_sum_delta_l (field_ring F) j (fun l => fdv_coord V v l)).
Qed.

(*
   * *** Evaluation is invertible in finite dimension

   The inverse reads a functional-on-functionals off its values at the
   dual basis and expands the resulting tuple in V's own basis.  The
   right triangle is [dual_apply_expand] used twice — once in V, once
   in V* — bridged by [dual_expand_coord] and closed by commuting the
   two factors; the left triangle is [dual_basis_coord] (each dual
   basis vector IS a coordinate functional) followed by V's own
   [fdv_expand_coord]. 

   --------
   * *** 在有限维中，评价是可逆的

   逆映射通过取在对偶基上的值来读取一个泛函作用于泛函的结果，并将得到的元组在 V 自身的基中展开。右三角形是  [dual_apply_expand] ，使用了两次——一次在 V 中，一次在 V* 中——通过  [dual_expand_coord] 连接，并通过交换两个因子闭合；左三角形是  [dual_basis_coord] （每个对偶基向量本身就是一个坐标泛函），随后是 V 自身的  [fdv_expand_coord] 。
*)

Program Definition eta_inv (V : FdVectObject F) :
  DoubleDual F (fdv_mod V) ~{Vct_F F}~> fdv_mod V := {|
  rm_hom := {|
    cmon_map := {| morphism := fun P =>
      fdv_expand V (fun j => cmon_map (rm_hom P)
                               (fdv_basis (DualFdObj V) j)) |}
  |}
|}.
Next Obligation.
  intros V P Q Hpq; simpl.
  apply fdv_expand_respects; intro j.
  exact (Hpq _).
Qed.
Next Obligation. intros V; simpl; apply fdv_expand_zero. Qed.
Next Obligation. intros V P Q; simpl; apply fdv_expand_plus. Qed.
Next Obligation. intros V r P; simpl; apply fdv_expand_smul. Qed.

(*
   * Mac Lane §I.4 remark 2 / Riehl §1.4 Example 1.4.4(ii), the half that
   needs finite dimension: the component of [double_dual_natural] at a
   finite-dimensional space is an isomorphism.  Naturality was proved
   without this hypothesis; invertibility is what it buys. 

   --------
   * Mac Lane §I.4 注释 2 / Riehl §1.4 示例 1.4.4(ii)，需要有限维度的那一半：在有限维空间上的  [double_dual_natural]  的分量是一个同构。自然性是在没有这个假设的情况下证明的；可逆性是它所带来的。
*)
Program Definition double_dual_iso (V : FdVectObject F) :
  IsIsomorphism (eta F (fdv_mod V)) := {|
  two_sided_inverse := eta_inv V
|}.
Next Obligation.
  intros V P f.
  transitivity (fin_sum (field_ring F)
    (fun j => rig_mul F
                (cmon_map (rm_hom P) (fdv_basis (DualFdObj V) j))
                (cmon_map (rm_hom f) (fdv_basis V j)))).
  { apply (dual_apply_expand V f
             (fun j => cmon_map (rm_hom P)
                         (fdv_basis (DualFdObj V) j))). }
  transitivity (fin_sum (field_ring F)
    (fun j => rig_mul F
                (cmon_map (rm_hom f) (fdv_basis V j))
                (cmon_map (rm_hom P) (fdv_basis (DualFdObj V) j)))).
  { apply fin_sum_respects; intro j; apply field_comm. }
  symmetry.
  transitivity (cmon_map (rm_hom P)
    (dual_of_coeffs V (fun j => cmon_map (rm_hom f) (fdv_basis V j)))).
  { apply (proper_morphism (cmon_map (rm_hom P))).
    intro v; symmetry; apply dual_expand_coord. }
  apply (dual_apply_expand (DualFdObj V) P
           (fun j => cmon_map (rm_hom f) (fdv_basis V j))).
Qed.
Next Obligation.
  intros V v.
  transitivity (fdv_expand V (fdv_coord V v)).
  { apply fdv_expand_respects; intro j.
    apply dual_basis_coord. }
  apply fdv_expand_coord.
Qed.

(*
   * *** The pointwise isomorphism V ≅ V*, and why it is not the point

   Both spaces carry the same dimension, so composing the coordinate
   isomorphisms of Instance/FdVect.v through F^n gives an isomorphism
   between them.  It is EXACTLY as canonical as the chosen coordinates
   are, which is to say not at all: a different basis on V gives a
   different map.  That no choice of such maps is natural is the
   content of Instance/FdVect/NonNatural.v; here only their existence
   is recorded, so that the contrast with [double_dual_iso] — proved
   above with no choice anywhere — can be drawn. 

   --------
   * *** 点同构 V ≅ V*，以及为什么它不是点

   两个空间的维数相同，因此坐标
   Instance/FdVect.v 的同构映射到 F^n 得到一个同构
   它们之间。它和所选坐标完全一样正则
   是，也就是说完全不是：V 上不同的基给出
   不同的映射。没有这样的映射是自然选择的，这是
   Instance/FdVect/NonNatural.v 的内容;这里仅有它们的存在
   被记录下来，因此与[double_dual_iso]的对比——证明
   上方无处可选——可以画出来。
*)
Program Definition fd_dual_pointwise_iso (V : FdVectObject F) :
  fdv_mod V ≅[Vct_F F] fdv_mod (DualFdObj V) := {|
  to   := @rmod_hom_compose (field_ring F) (fdv_mod V)
            (std_mod F (fdv_dim V)) (fdv_mod (DualFdObj V))
            (std_expand_hom F (DualFdObj V)) (std_coord_hom F V);
  from := @rmod_hom_compose (field_ring F) (fdv_mod (DualFdObj V))
            (std_mod F (fdv_dim V)) (fdv_mod V)
            (std_expand_hom F V) (std_coord_hom F (DualFdObj V))
|}.
Next Obligation.
  intros V f.
  transitivity (fdv_expand (DualFdObj V) (fdv_coord (DualFdObj V) f)).
  { apply fdv_expand_respects; intro j.
    apply (fdv_coord_expand V (fdv_coord (DualFdObj V) f) j). }
  apply fdv_expand_coord.
Qed.
Next Obligation.
  intros V v.
  transitivity (fdv_expand V (fdv_coord V v)).
  { apply fdv_expand_respects; intro j.
    apply (fdv_coord_expand (DualFdObj V) (fdv_coord V v) j). }
  apply fdv_expand_coord.
Qed.

End FiniteDimensional.

(*
   * ** Acceptance tests

   First the structural identities, which hold by [eq_refl] and so are
   checks on the definitions rather than on any proof: the double dual
   really is the dual twice, the dual space carries the same dimension,
   and the components of [double_dual_natural] really are [eta]. 

   --------
   * ** 验收测试

   首先是结构恒等式，它们由 [eq_refl] 保持，因此是对定义的检查，而不是对任何证明的检查：双重对偶确实是对偶两次，对偶空间具有相同的维度，并且 [double_dual_natural] 的分量确实是 [eta] 。
*)

Example double_dual_is_dual_twice (F : FieldObject)
  (V : RModObject (field_ring F)) :
  fobj[DoubleDual F] V = DualMod F (DualMod F V) := eq_refl.

Example dual_fd_dim (F : FieldObject) (V : FdVectObject F) :
  fdv_dim (DualFdObj F V) = fdv_dim V := eq_refl.

Example dual_fd_mod (F : FieldObject) (V : FdVectObject F) :
  fdv_mod (DualFdObj F V) = DualMod F (fdv_mod V) := eq_refl.

Example transform_is_eta (F : FieldObject)
  (V : RModObject (field_ring F)) :
  transform[double_dual_natural F] V = eta F V := eq_refl.

(*
   * *** Dimension two over the rationals

   [StdVect Q_Field 2] is ℚ², whose chosen coordinates are the
   identity, so every value below reduces to a rational literal by
   computation. 

   --------
   * *** 有理数上的二维

   [StdVect Q_Field 2] 是 ℚ²，其选择的坐标是恒等，所以下面的每个值通过计算都可以化简为有理数字面量。
*)

Definition q2 : FdVectObject Q_Field := StdVect Q_Field 2.

Definition qvec : carrier (cmon_setoid (fdv_mod q2)) :=
  fin2 (5 # 1) (6 # 1).

(*
   * The first dual basis vector of ℚ²: the functional reading off the
   first coordinate, obtained from [DualFdObj]'s expansion rather than
   written down by hand — so these two lines check [dual_basis_coord]
   computationally. 

   --------
   * ℚ² 的第一个对偶基向量：读取第一个坐标的泛函，由 [DualFdObj] 的展开式获得，而不是手工写出——因此这两行从计算上检查 [dual_basis_coord]。
*)
Definition qphi :
  carrier (cmon_setoid (fdv_mod (DualFdObj Q_Field q2))) :=
  fdv_basis Q_Field (DualFdObj Q_Field q2) Fin.F1.

Example q_dual_basis_first :
  cmon_map (rm_hom qphi) qvec = (5 # 1)%Q := eq_refl.

Example q_dual_basis_second :
  cmon_map (rm_hom (fdv_basis Q_Field (DualFdObj Q_Field q2)
                      (Fin.FS Fin.F1))) qvec = (6 # 1)%Q := eq_refl.

(** Evaluation: η(v) applied to φ is φ applied to v. / 评价：η(v) 应用于 φ 等于 φ 应用于 v。 *)
Example q_eta_apply :
  cmon_map (rm_hom (cmon_map (rm_hom (eta Q_Field (fdv_mod q2))) qvec))
    qphi = (5 # 1)%Q := eq_refl.

(** The first dual basis vector of the DOUBLE dual. / 双重对偶的第一个对偶基向量。 *)
Definition qPhi : carrier (cmon_setoid
  (fdv_mod (DualFdObj Q_Field (DualFdObj Q_Field q2)))) :=
  fdv_basis Q_Field (DualFdObj Q_Field (DualFdObj Q_Field q2)) Fin.F1.

(*
   * The inverse of evaluation carries it back to the first basis vector
   of ℚ², namely (1, 0) — computed, not asserted. 

   --------
   * 评价的逆运算将其带回 ℚ² 的第一个基向量，即 (1, 0)——是计算得到的，而非断言的。
*)
Example q_eta_inv_first :
  cmon_map (rm_hom (eta_inv Q_Field q2)) qPhi Fin.F1 = (1 # 1)%Q := eq_refl.

Example q_eta_inv_second :
  cmon_map (rm_hom (eta_inv Q_Field q2)) qPhi (Fin.FS Fin.F1)
    = (0 # 1)%Q := eq_refl.

(*
   * ... and evaluating that vector recovers Φ: an instance of
   [double_dual_iso]'s right triangle whose two sides compute. 

   --------
   * ... 并且评估该向量可以恢复 Φ：[double_dual_iso] 的一个直角三角形实例，其两条边可以计算。
*)
Example q_double_dual_roundtrip :
  cmon_map (rm_hom (cmon_map (rm_hom (eta Q_Field (fdv_mod q2)))
    (cmon_map (rm_hom (eta_inv Q_Field q2)) qPhi))) qphi
    = cmon_map (rm_hom qPhi) qphi := eq_refl.

(*
   * The basis-dependent isomorphism ℚ² ≅ (ℚ²)*: it carries (5,6) to the
   functional 5x + 6y, whose value at (5,6) is 61. 

   --------
   * 基于基的同构 ℚ² ≅ (ℚ²)*：它将 (5,6) 映射到函数 5x + 6y，该函数在 (5,6) 的值是 61。
*)
Example q_pointwise_iso :
  cmon_map (rm_hom (cmon_map
    (rm_hom (to (fd_dual_pointwise_iso Q_Field q2))) qvec)) qvec
    = (61 # 1)%Q := eq_refl.
