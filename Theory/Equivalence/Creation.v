Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.Limit.

Generalizable All Variables.

(** * Equivalences create limits, and right adjoints preserve cones / * 等价产生限制，右伴随保持圆锥 *)

(*
nLab: https://ncatlab.org/nlab/show/created+limit
   nLab: https://ncatlab.org/nlab/show/adjoint+functor#preservation

   [equivalence_creates_limits] (Theory/Equivalence/Limit.v) transports
   a limit; on its own it relates neither the apexes nor the legs, and its
   name has been ahead of its statement.  This file closes the gap in the
   strong direction, keeping the name: [equivalence_CreatesLimit] exhibits
   the existing constant as the existence datum of a genuine [CreatesLimit]
   instance (Structure/Limit/Creation.v), with the comparison supplied by
   uniqueness of limits up to cone isomorphism and the reflection clause by
   [ff_reflect_ump] — every equivalence is full and faithful, and the leg
   hypothesis discharges by [reflexivity] because the legs of [FCone] ARE
   the image legs.  No constant is renamed, so [equivalence_creates_colimits]
   (Theory/Equivalence/Limit.v) and every downstream user are untouched.

   The construction above does not give a strict lift: the apex
   [equivalence_creates_limits] produces is the quasi-inverse of the given
   apex, related to it only by an isomorphism.  That is the case Riehl's
   remark on Definition 3.4.7 (Category Theory in Context, 2nd ed., p. 105)
   has in mind — strict creation is not invariant under equivalence, so no
   strict witness is available for a general [F].  It is not a claim about
   every equivalence: [Id[C]] is one, and it strictly creates every limit,
   both clauses by [reflexivity].  [Id_CreatesAllLimits] below is therefore
   offered as a [CreatesLimit] witness only; the strict class is witnessed
   at generality by [EM_Forget] (Monad/Eilenberg/Moore/Limit.v).

   The cone-level reading of RAPL, [right_adjoint_PreservesLimitCone],
   lives at its natural home in Adjunction/Continuity.v.

--------
nLab：https://ncatlab.org/nlab/show/created+limit
nLab：https://ncatlab.org/nlab/show/adjoint+functor#preservation

[equivalence_creates_limits]（Theory/Equivalence/Limit.v）传递一个极限；它本身既不关联顶点也不关联腿，并且它的名称早于其声明。该文件在强方向上弥补了这一空白，同时保留名称：[equivalence_CreatesLimit] 以现有常量展示一个真正的 [CreatesLimit] 实例的存在资料（Structure/Limit/Creation.v），比较由极限在锥同构下的唯一性提供，反射条款由 [ff_reflect_ump] 提供——每个等价都是完全且忠实的，而腿假设通过 [reflexivity] 释放，因为 [FCone] 的腿就是像腿。没有常量被重命名，因此 [equivalence_creates_colimits]（Theory/Equivalence/Limit.v）及所有下游使用者均未受影响。

上面的构造并没有给出严格的提升：顶点 [equivalence_creates_limits] 所产生的是给定顶点的拟逆，仅通过同构与之相关。这正是 Riehl 在《范畴论在上下文中》（第2版，第105页）中对定义 3.4.7 的评论所指——严格生成在等价下并不不变，因此对于一般的 [F] 没有严格的证据。这并不是对每个等价的声明：[Id[C] 是一个，并且它严格生成每一个极限，这两个条款都是通过 [reflexivity]。下面的 [Id_CreatesAllLimits] 因此仅作为 [CreatesLimit] 的证据提供；严格类在一般性上由 [EM_Forget] 进行证明（Monad/Eilenberg/Moore/Limit.v）。

RAPL、[right_adjoint_PreservesLimitCone] 的锥体层级读数，位于其在 Adjunction/Continuity.v 中的自然位置。
*)

(** ** Right adjoints preserve limiting cones, not merely limit apexes / ** 右伴随保留极限锥，而不仅仅是极限顶点 *)

Section EquivCreates.

Context {C D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).

(*
An equivalence is (the left half of) an adjoint equivalence, hence a
   right adjoint, hence cone-level continuous.

--------
一个等价是（伴随等价的左半部分），因此是一个右伴随，因此是锥级连续的。
*)

Definition equivalence_PreservesLimitCone {J : Category} (K : J ⟶ C) :
  PreservesLimitCone K F :=
  right_adjoint_PreservesLimitCone
    (AdjointEquivalence_swap_adjunction (Equivalence_to_AdjointEquivalence E)) K.

(*
Reflection, from full faithfulness.  The leg side condition of
   [ff_reflect_ump] (Theory/Equivalence/Limit.v) is [reflexivity] here
   exactly because [FCone]'s legs are the image legs.

   CORRECTION (#481): the body wrote that term out, [@ff_reflect_ump C D
   F (Equivalence_Full E) (Equivalence_Faithful E) J K M (limitcone_isalimit
   H) (fun x => reflexivity _)], which is Theory/Equivalence/Limit.v's
   [ff_ReflectsLimitCone] at this functor's fullness and faithfulness:
   the two read back as one at [eq_refl] (measured).  The body now calls
   that constant, eta-expanded, and the [About] blocks of this file's five
   constants are unchanged (compared by script against the earlier
   body).

--------
反射，来自完全忠实。[ff_reflect_ump]（Theory/Equivalence/Limit.v）的腿侧条件在这里是[reflexivity]，正是因为[FCone]的腿是像腿。

更正（#481）：正文写出了该项，[@ff_reflect_ump C D F (Equivalence_Full E) (Equivalence_Faithful E) J K M (limitcone_isalimit H) (fun x => reflexivity _)]，这是该函子完全性和忠实性在Theory/Equivalence/Limit.v中的[ff_ReflectsLimitCone]：两者在[eq_refl]（测量）处读回作为一项。正文现在调用那常量，进行eta展开，该文件五个常量的[About]块保持不变（通过脚本与之前正文比较）。
*)

Definition equivalence_ReflectsLimitCone {J : Category} (K : J ⟶ C) :
  ReflectsLimitCone K F :=
  fun M H =>
    @ff_ReflectsLimitCone C D F (Equivalence_Full E) (Equivalence_Faithful E)
      J K M H.

(*
The naming defect of [equivalence_creates_limits], resolved by proof:
   that constant supplies the lift, and the two remaining clauses are the
   two lemmas above.

--------
[equivalence_creates_limits] 的命名缺陷，通过证明得到解决：该常数提供升力，剩下的两个条款是上面的两个引理。
*)

Definition equivalence_CreatesLimit {J : Category} (K : J ⟶ C) :
  CreatesLimit K F.
Proof using E.
  unshelve refine
    {| creates_lift := fun N HN =>
         @limit_cone _ _ _
           (equivalence_creates_limits E K (@Build_Limit J D (F ◯ K) N HN)) |}.
  - intros N HN.
    exact (limitcone_iso
             (equivalence_PreservesLimitCone K _ (limit_limitcone _)) HN).
  - exact (equivalence_ReflectsLimitCone K).
Defined.

Definition equivalence_CreatesAllLimits : CreatesAllLimits F :=
  fun J K => equivalence_CreatesLimit K.

End EquivCreates.

(** ** The identity functor creates every limit / ** 恒等函子创建每一个极限 *)

Definition Id_CreatesAllLimits {C : Category} : CreatesAllLimits Id[C] :=
  equivalence_CreatesAllLimits (@EquivalenceOfCategories_Id C).
