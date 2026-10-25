Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Terminal.
Require Import Category.Theory.Equivalence.Pullback.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Adjunction.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Terminal.
Require Import Category.Structure.Limit.Cartesian.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Structure.Topos.Power.
Require Import Category.Structure.Topos.Monadic.
Require Import Category.Structure.Topos.Colimits.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Adjunction.Right.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Pushout.
Require Import Category.Instance.FinSet.Topos.

Generalizable All Variables.
Open Scope category_scope.

(*
Measured negatives for Structure/Topos/{Power,Monadic,Colimits}.v and
   Theory/Equivalence/Pullback.v.

   A passing refutation command prints NOTHING, so every one below was
   stripped ONE AT A TIME, compiled alone, and its whole error read; the
   KIND is read off the error TEXT, not guessed:

     FORMABILITY -- "universe inconsistency" / "Cannot enforce";
     TYPING      -- a plain "has type ... while it is expected to have
                    type ..." with no cannot-unify and no universe clause;
     CONVERSION  -- "cannot unify" between two terms of ONE type.

   Every constant a refutation REFERENCES also appears OUTSIDE every refutation,
   in a [Check] control or a positive [Example]; the exceptions are the
   instrument's deliberately absent name and the five names the refutations
   themselves DECLARE, which never enter the environment.

   The FinSet section lives HERE and not in Structure/Topos/Colimits.v for
   a MEASURED reason: requiring Instance/FinSet/Topos costs that file's
   transitive closure +6 modules, above the +5 the plan allowed, and a
   sanity example must not make every consumer of the general theorem pay
   for the finite model.

--------
测量了 Structure/Topos/{Power,Monadic,Colimits}.v 和 Theory/Equivalence/Pullback.v 的负数。

一个通过反驳的命令什么也不打印，所以下面的每一个都被一次一次剥离，单独编译，并读取其整个错误；类型是从错误文本中读取的，而不是猜测的：

可形成性 -- “宇宙不一致” / “无法强制执行”；
类型 -- 一个简单的“具有类型...，而预计应具有类型...”而没有无法统一和没有宇宙条款；
转换 -- 两个同一类型的项之间“无法统一”。

每一个常量 a refutation REFERENCES 同样出现在每一个 refutation 之外，
   在 [Check] 控制或一个正的 [Example] 中；例外的是该
   仪器故意缺失的名称以及反驳本身 DECLARE 的五个名称，这些名称永远不会进入环境。

FinSet 部分位于这里，而不是 Structure/Topos/Colimits.v，原因是经过深思熟虑的：需要 Instance/FinSet/Topos 会使该文件的传递闭包增加 6 个模块，超出了计划允许的 5 个模块，而且一个合理的示例不应让一般定理的每个使用者都为有限模型付出代价。
*)

(** ** Instrument check: a deliberately absent name / ** 乐器检查：一个故意缺席的名字 *)

Fail Check p405_this_name_does_not_exist.

(** ** (1) Positive controls over an arbitrary topos / ** (1) 任意拓扑上的正控制 *)

Section ProbeGeneral.

Context {C : Category}.
Context `{HT : @ElementaryTopos C}.

Example p405_op_op : (C^op)^op = C := eq_refl.

Example p405_powf_obj (a : C) : fobj[PowF] a = Pow a := eq_refl.

Example p405_powf_map {a b : C} (f : b ~{C}~> a) :
  fmap[PowF] f = curry (id ∘ eval ∘ second f) := eq_refl.

Definition p405_ok_handedness : Opposite_Functor PowF ⊣ PowF :=
  pow_adjunction.

Definition p405_powf_typed : C^op ⟶ C := PowF.

Check @pow_self_adjoint.
Check @pow_aor.
Check @pow_relations.
Check @pow_aor_is_relations.
Check @pow_monad.
Check @flip_flip.
Check @flip_comp.
Check @flip_pow_comp.
Check @pow_precompose.
Check @relations_iso_to_is_curry_char.
Check @relations_iso_from_is_reindex.
Check @topos_balanced.
Check @topos_diag.
Check @sing.
Check @sing_Monic.
Check @char_diag_swap.
Check @flip_sing.
Check @PowF_Faithful.
Check @PowF_ReflectsIsos.
Check @IsIso_of_op.
Check @op_IsIso_of.
Check @second_Monic.
Check @sub_push.
Check @sub_push_respects.
Check @sub_reindex_push.
Check @pow_mem.
Check @char_mem.
Check @char_sub_inj.
Check @eval_pow_square.
Check @mem_pow_square.
Check @ex_mono.
Check @pow_ex_mono.
Check @IsPullback_sym.
Check @second_pullback.
Check @first_second_pullback.
Check @bc_mono.
Check @coreflexive_equalizer_pullback.
Check @pow_bc.
Check @pow_fmap_comp.
Check @pow_split_coequalizer.
Check @pow_PreservesReflexiveCoequalizers.
Check @pow_equivalence.
Check @power_object_monadic.
Check @topos_HasEqualizers.
Check @topos_finitely_complete.
Check @op_HasCoequalizers.
Check @op_HasReflexiveCoequalizers.
Check @EM_Terminal.
Check @EM_HasPullbacks.
Check @EM_Pullback.
Check @em_pb_carrier.
Check @em_pb_p1.
Check @em_pb_p2.
Check @topos_Initial.
Check @topos_HasPullbacks_op.
Check @topos_Cocartesian.
Check @topos_HasCoequalizers.
Check @topos_HasPushouts.
Check @topos_has_finite_colimits.
Check @is_pullback_jointly_monic.
Check @pullback_transport_leg.
Check @IsPullback_transport.
Check @HasPullbacks_transport.
Check @Partial_r.
Check @InternalHomFunctor.
Check @Exp_Functor.
Check @Terminal_transport.
Check @crude_monadicity.
Check @Cartesian_of_HasPullbacks_Terminal.
Check @Terminal_Limit.
Check @Cartesian_Limit.
Check @relations_iso.
Check @SubObj.
Check @Ω.
Check @curry.
Check @flip.

(*
The exponential endofunctor of Structure/Cartesian/Closed/Adjunction.v
   is covariant in the base with the exponent held FIXED, so its object
   action is (-)^Ω and not Ω^(-).

--------
Structure/Cartesian/Closed/Adjunction.v 的指数自函子在底数上是协变的，指数保持固定，所以它的对象作用是 (-)^Ω 而不是 Ω^(-)。
*)
Example p405_exp_functor_obj (a : C) :
  fobj[@Exp_Functor C _ _ Ω] a = exponent_obj Ω a := eq_refl.

(** ** (2) TYPING negatives / ** (2) 打字否定词 *)

(*
[Partial_r] fixes the FIRST argument of the bifunctor and varies the
   second, so it has the wrong variance for the power object: the
   internal hom is contravariant in its first argument only.

--------
[Partial_r] 固定了双函子（bifunctor）的第一个参数并改变第二个参数，因此它的方变性对幂对象来说是错误的：内部 Hom 仅在其第一个参数中是逆变的。
*)
Fail Definition p405_partial_r_typing : C^op ⟶ C :=
  Partial_r (InternalHomFunctor C) Ω.

(*
The adjunction runs P^op ⊣ P and not the other way round, even though
   both ascriptions are well formed as TYPES.

--------
这个伴随关系是 P^op ⊣ P，而不是反过来，尽管这两种指定作为类型都是形式正确的。
*)
Fail Definition p405_swapped_handedness : PowF ⊣ Opposite_Functor PowF :=
  pow_adjunction.

(** ** (3) CONVERSION negatives / ** (3) 变换否定 *)

(* The exponential endofunctor's object action is not the power object. / 指数自函子的对象作用不是幂对象。 *)
Fail Example p405_exp_is_pow (a : C) :
  fobj[@Exp_Functor C _ _ Ω] a = Pow a := eq_refl.

(*
The fidelity lemma holds at ≈ and NOT on the nose: the two sides are
   [curry] of the untransposed map composed with [swap] on one side, and
   [curry] of the characteristic map of a doubly reindexed subobject on
   the other, and reindexing introduces chosen pullback objects.

--------
忠实引理在 ≈ 上成立，而不是完全相等：两边分别是未转置映射与一侧的 [swap] 组合的 [curry]，以及另一侧双重重新索引子对象的特征映射的 [curry]，而重新索引会引入选定的拉回对象。
*)
Fail Example p405_relations_strict {a b : C} (f : a ~> Pow b) :
  to (pow_aor a b) f = pow_relations f := eq_refl.

Example p405_relations_equiv {a b : C} (f : a ~> Pow b) :
  to (pow_aor a b) f ≈ pow_relations f := pow_aor_is_relations f.

End ProbeGeneral.

(** ** (4) FORMABILITY negatives: why the [Limit] route is not taken / ** (4) 可成形性缺点：为什么不采用 [Limit] 路径 *)

(*
[Terminal_Limit] and [Cartesian_Limit] are stated over
   [Category@{u Set Set}]: they pin the ambient category's hom AND proof
   universes to the literal [Set].  At a category whose hom-and-proof
   universe is declared STRICTLY ABOVE [Set] both are refused, while the
   elementary transports and the headline theorem itself are accepted at
   exactly those levels.  This measurement is what justifies building
   Structure/Topos/Colimits.v out of [Terminal]/[HasPullbacks] records
   rather than out of [Limit].

--------
[Terminal_Limit] 和 [Cartesian_Limit] 作用于 [Category@{u Set Set}]：它们将环境范畴的同态和证明宇宙固定到字面量 [Set]。在同态和证明宇宙声明为严格高于 [Set] 的范畴中，它们都被拒绝，而基本传输和标题定理本身在恰好这些级别上被接受。这种测量正是建立 Structure/Topos/Colimits.v 使用 [Terminal]/[HasPullbacks] 记录而不是 [Limit] 的理由。
*)

Section UniverseBoundary.

Universes uo uh.
Constraint Set < uh.

Context (Cu : Category@{uo uh uh}).

Fail Check (Terminal_Limit Cu).

Fail Check (Cartesian_Limit Cu).

(* Controls at the very same declared levels. / 在完全相同的声明级别进行控制。 *)
Check (@Terminal_transport Cu Cu).
Check (@crude_monadicity Cu Cu).
Check (@Cartesian_of_HasPullbacks_Terminal Cu).
Check (@HasPullbacks_transport Cu Cu).
Check (@topos_has_finite_colimits Cu).
Check (@power_object_monadic Cu).
Check (@topos_finitely_complete Cu).
Check (Cu^op).
Check (@Terminal Cu).

End UniverseBoundary.

(*
A SECOND, INDEPENDENT FORMABILITY MEASUREMENT, and the one that
   justifies routing the self-adjointness through [flip] rather than
   through the issue's [relations_iso].  Packaging subobjects of a × b as
   an OBJECT of [Sets] identifies C's object universe with its hom
   universe: at a topos whose objects are declared STRICTLY BELOW its
   homs, [relations_iso] and everything built on it are refused, while
   [Pow], [PowF], [pow_aor] and the whole adjunction are accepted.  So
   [pow_relations] and [pow_aor_is_relations] are FIDELITY CHECKS that
   cost a universe identification, and no constant on the proof path
   pays it.  [SubObj] itself is accepted, so the identification belongs
   to the [Sets]-packaging and not to the subobject record.

--------
第二个、独立的可形成性测量，也是那个证明通过 [flip] 而不是通过该问题的 [relations_iso] 来路由自伴性的测量。将 a × b 的子对象打包为 [Sets] 对象将 C 的对象宇宙与其 Hom 宇宙识别：在一个其对象被严格声明在其 Hom 之下的拓扑中，[relations_iso] 及其所有构建内容都会被拒绝，而 [Pow]、[PowF]、[pow_aor] 及整个伴随结构都会被接受。因此，[pow_relations] 和 [pow_aor_is_relations] 是忠实性检查，它们消耗一个宇宙识别，并且证明路径上的任何常量都不支付这个代价。[SubObj] 本身是被接受的，因此该识别属于 [Sets] 打包，而不属于子对象记录。
*)

Section RelationsBoundary.

Universes vo vh.
Constraint vo < vh.

Context (Cv : Category@{vo vh vh}).
Context (Hv : @ElementaryTopos Cv).

Check (@Pow Cv Hv).
Check (@PowF Cv Hv).
Check (@pow_aor Cv Hv).
Check (@pow_self_adjoint Cv Hv).
Check (@pow_adjunction Cv Hv).
Check (@power_object_monadic Cv Hv).
Check (@topos_has_finite_colimits Cv Hv).
Check (@SubObj Cv).

Fail Check (@relations_iso Cv Hv).

Fail Check (@pow_relations Cv Hv).

End RelationsBoundary.

(*
THE DONOR OF hom = proof, PINNED.  Every constant of the four library
   files is over [C : Category@{u u0 u0}] -- hom identified with proof in the
   BINDER, with no such equation in any constraint block -- and that
   identification is INHERITED.  Here is the measurement: at hom and proof
   levels declared strictly apart, the hom-set and the identity are accepted
   while [ElementaryTopos], [IsPullback] and [HasPullbacks] are each refused
   ALONE with "Cannot enforce wp = wh" -- three FORMABILITY refutations, the
   category, its hom-set and its identity standing as the controls that separate
   each class from its argument.  [ElementaryTopos] is the donor met first by
   the 103 topos-facing constants whose type carries it (the other three,
   [IsIso_of_op], [op_IsIso_of] and [sub_push], are transparent [Definition]s
   that [Set Default Proof Using "All"] does not reach, and get it from
   [Opposite] and from [Monic] and [SubObj] respectively); [IsPullback] and
   [HasPullbacks] are the ones Theory/Equivalence/Pullback.v's six meet, and
   that file's [is_pullback_jointly_monic] has a LITERALLY EMPTY constraint
   block over that very binder.  Read "each refused alone" as sufficiency and
   not independence: [Monic], [Cartesian], [Terminal], [SubObj], [Closed],
   [SubobjectClassifier] and [Opposite] are refused the same way, while
   [IsIsomorphism] alone is accepted (measured, not pinned).

--------
同源者 hom 的捐赠者 = 证明，已固定。四个库文件中的每一个常量都位于 [C : Category@{u u0 u0}] 之上 —— 在 BINDER 中，hom 被认定为 proof，而在任何约束块中都没有这样的等式 —— 并且这种认定是继承的。以下是测量结果：当 hom 和 proof 级别严格分开声明时，hom 集合和恒等式被接受，而 [ElementaryTopos]、[IsPullback] 和 [HasPullbacks] 单独被拒绝，显示“无法强制 wp = wh” —— 三个可形成性驳回，其类别、hom 集合和恒等式作为控件，将每个类与其参数区分开。
[ElementaryTopos] 是捐赠者，首先被 103 个面向 topos 的常量遇到，这些常量的类型承载它（其他三个，[IsIso_of_op]、[op_IsIso_of] 和 [sub_push]，是透明的 [Definition]，[Set Default Proof Using "All"] 无法到达它们，并分别从 [Opposite]、[Monic] 和 [SubObj] 获取）；[IsPullback] 和 [HasPullbacks] 是 Theory/Equivalence/Pullback.v 的六个 meet 中的两个，并且该文件的 [is_pullback_jointly_monic] 对该束缚器上有一个字面上的空约束块。将“each refused alone” 理解为充分性而非独立性：[Monic]、[Cartesian]、[Terminal]、[SubObj]、[Closed]、[SubobjectClassifier] 和 [Opposite] 以相同方式被拒绝，而 [IsIsomorphism] 单独被接受（测量，而非固定）。
*)

Section DonorBoundary.

Universes wo wh wp.
Constraint wh < wp.

Context (Cw : Category@{wo wh wp}) (x y z P : Cw)
  (f : x ~> z) (g : y ~> z) (p1 : P ~> x) (p2 : P ~> y).

(* Controls at the very same declared levels. / 在完全相同的声明级别进行控制。 *)
Check (x ~> y).
Check (id[x]).
Check @ElementaryTopos.
Check @IsPullback.
Check @HasPullbacks.

Fail Check (@ElementaryTopos Cw).

Fail Check (@IsPullback Cw x y z f g P p1 p2).

Fail Check (@HasPullbacks Cw).

End DonorBoundary.

(** ** (5) The FinSet sanity check / ** (5) FinSet 健全性检查 *)

(*
Two [Cartesian] structures on one category have canonically isomorphic
   product objects.  Stated here because the tree has no such uniqueness
   lemma: a whole-tree search for a statement of the shape
   [product_obj _ ≅ product_obj _] returns nothing, and
   Structure/Cartesian.v carries only [ump_products].  Read at FinSet^op
   it is the uniqueness of binary COPRODUCTS.

--------
一个类别上的两个 [Cartesian] 结构拥有典型同构的积对象。在此说明是因为该树没有这样的唯一性引理：在整棵树中搜索形如 [product_obj _ ≅ product_obj _] 的陈述不会返回任何结果，而 Structure/Cartesian.v 只包含 [ump_products]。在以 FinSet^op 阅读时，这是二元余积的唯一性。
*)
Program Definition cartesian_unique_iso {D : Category}
        (P Q : @Cartesian D) (a b : D) :
  @product_obj D P a b ≅ @product_obj D Q a b := {|
  to   := @fork D Q _ a b (@exl D P a b) (@exr D P a b) ;
  from := @fork D P _ a b (@exl D Q a b) (@exr D Q a b)
|}.
Next Obligation.
  rewrite <- (@fork_exl_exr D Q a b).
  apply (@ump_products D Q _ a b _ _ _); split.
  - rewrite comp_assoc, (@exl_fork D Q _ a b _ _),
            (@exl_fork D P _ a b _ _).
    reflexivity.
  - rewrite comp_assoc, (@exr_fork D Q _ a b _ _),
            (@exr_fork D P _ a b _ _).
    reflexivity.
Qed.
Next Obligation.
  rewrite <- (@fork_exl_exr D P a b).
  apply (@ump_products D P _ a b _ _ _); split.
  - rewrite comp_assoc, (@exl_fork D P _ a b _ _),
            (@exl_fork D Q _ a b _ _).
    reflexivity.
  - rewrite comp_assoc, (@exr_fork D P _ a b _ _),
            (@exr_fork D Q _ a b _ _).
    reflexivity.
Qed.

(*
THE FIRST [HasCoequalizers FinSet] THE TREE HAS EVER HAD: no .v file declares
   a constant of that type, [FinSet_Coequalizer] occurs nowhere at all, and the
   two .v mentions of the phrase -- Instance/Sets/Coequalizer.v and
   Instance/Sets/Coequalizer/Interconnect.v -- are NOT-DELIVERED notes about
   those files.  A plain [Definition], NOT an [Instance]: a chosen coequalizer
   must not become globally resolvable.

--------
第一个 [HasCoequalizers FinSet] 树曾有过：没有 .v 文件声明这种类型的常量，[FinSet_Coequalizer] 根本不存在，而且该短语的两个 .v 提及——Instance/Sets/Coequalizer.v 和 Instance/Sets/Coequalizer/Interconnect.v——都是关于这些文件的未交付备注。一个普通的 [Definition]，而不是 [Instance]：选定的共同化必不得成为全局可解析的。
*)
Definition FinSet_derived_HasCoequalizers : HasCoequalizers FinSet :=
  @topos_HasCoequalizers FinSet FinSet_Topos.

Definition FinSet_derived_finite_colimits :
  @Initial FinSet * @Cocartesian FinSet * @HasCoequalizers FinSet
    * @HasPushouts FinSet :=
  @topos_has_finite_colimits FinSet FinSet_Topos.

Check (@power_object_monadic FinSet FinSet_Topos : Monadic PowF).

(*
The derived initial object agrees with FinSet's computable one -- up to
   ISOMORPHISM, not on the nose.  The [eq_refl] form is refused with a
   CONVERSION error, and its cause is NOT isolated: the derived object is
   [crude_monadicity]'s quasi-inverse [Crude_Inverse] at [EM_Terminal]'s object
   (Structure/Topos/Colimits.v's [topos_Initial_obj] reads that back at
   [eq_refl]), i.e. the reflexive coequalizer Monad/Monadicity/Crude.v chooses
   through [op_HasReflexiveCoequalizers] and [topos_HasEqualizers]; that chain
   never consumes [PowF_ReflectsIsos] -- [Crude_Inverse] takes no [ReflectsIsos]
   argument, [refl] entering Crude.v only at [crude_theta_iso] and one
   [Proof using] -- and no experiment names the constant that blocks the
   reduction.

--------
派生的初始对象与 FinSet 的可计算对象一致——是同构的，而不是完全相等。[eq_refl] 形式会因为转换错误而被拒绝，其原因并未被隔离：派生对象是 [crude_monadicity] 的准逆 [Crude_Inverse]，在 [EM_Terminal] 的对象上（Structure/Topos/Colimits.v 的 [topos_Initial_obj] 会在 [eq_refl] 处读取该对象），即反射余等化器 Monad/Monadicity/Crude.v 通过 [op_HasReflexiveCoequalizers] 和 [topos_HasEqualizers] 进行选择；该链从未消耗 [PowF_ReflectsIsos]——[Crude_Inverse] 不接受任何 [ReflectsIsos] 参数，[refl] 只在 [crude_theta_iso] 和一个 [Proof using] 处进入 Crude.v——且没有实验命名阻碍规约的常量。
*)
Fail Example p405_finset_initial_strict :
  @initial_obj FinSet (@topos_Initial FinSet FinSet_Topos)
    = @initial_obj FinSet FinSet_Initial := eq_refl.

Definition finset_derived_initial_iso :
  @initial_obj FinSet (@topos_Initial FinSet FinSet_Topos)
    ≅[FinSet] @initial_obj FinSet FinSet_Initial :=
  initial_unique (@topos_Initial FinSet FinSet_Topos) FinSet_Initial.

(*
The derived binary coproduct agrees with FinSet's computable one, read
   as the uniqueness of products in FinSet^op.

--------
导出的二元余积与 FinSet 的可计算余积一致，可理解为 FinSet^op 中积的唯一性。
*)
Definition finset_derived_coproduct_iso (m n : FinSet) :
  @Coprod FinSet (@topos_Cocartesian FinSet FinSet_Topos) m n
    ≅[FinSet^op] @Coprod FinSet FinSet_Cocartesian m n :=
  @cartesian_unique_iso (FinSet^op)
    (@topos_Cocartesian FinSet FinSet_Topos) FinSet_Cocartesian m n.

(*
The derived pushout agrees with FinSet's computable one, by the
   pre-existing [pullback_unique] read in FinSet^op.

--------
通过在 FinSet^op 中预先存在的 [pullback_unique] 读取，派生推出与 FinSet 的可计算推出一致。
*)
Definition finset_derived_pushout_iso {x y z : FinSet}
           (f : x ~> y) (g : x ~> z) :
  pushout_apex (@pushout FinSet (@topos_HasPushouts FinSet FinSet_Topos)
                  x y z f g)
    ≅[FinSet^op] pushout_apex (@pushout FinSet FinSet_HasPushouts x y z f g)
  := @pullback_unique (FinSet^op) y z x f g _ _.

Check @FinSet_Topos.
Check @FinSet_Initial.
Check @FinSet_Cocartesian.
Check @FinSet_HasPushouts.
Check @initial_unique.
Check @pullback_unique.
Check @ump_products.
Check @cartesian_unique_iso.
Check @finset_derived_initial_iso.
Check @finset_derived_coproduct_iso.
Check @finset_derived_pushout_iso.
Check @FinSet_derived_HasCoequalizers.
Check @FinSet_derived_finite_colimits.
