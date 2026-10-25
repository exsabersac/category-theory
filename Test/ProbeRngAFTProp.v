Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Limit.
Require Import Category.Instance.Rng.Free.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.AFT.

Generalizable All Variables.

(**
* Probe: the ring adjoint-functor-theorem applications are
      non-circular, and here they are at a named set and a named group

    The import list above is Instance/Rng/AFT.v's own, verbatim, plus that
    file itself; a shorter prefix is what makes a probe pass for no reason.

    WHAT THIS FILE GUARDS.  Until the PR "algebraic carriers are sets"
    (2026-09-17), [free_rng_ab_via_GAFT] and [free_ring_via_GAFT] consumed
    [solution_set_of_adjunction] applied to the very adjunctions they were
    meant to produce, and Instance/Rng/AFT.v's header said so at length.
    They now consume solution sets built from the free-ring TERM MODEL by
    [Prop]-valued congruences.  That change is invisible to the type -- the
    two readings inhabit the same statement -- so nothing in the build
    would notice it being reverted.  This file notices: the [eq_refl]
    readbacks below name the congruence index, and the [Fail] pins that the
    new solution set is not the old singleton.

    DISCIPLINE.  Every negative is paired with a positive control naming
    the same library constants; the instrument was checked; each negative
    was re-run with its guard stripped in a copy of this whole file so the
    refusal kind could be read rather than guessed.  The kinds recorded are
    CONVERSION (two) beside the instrument check, whose refusal is a
    missing NAME.

--------
* 探针：环伴随定理的应用是非循环的，它们在一个命名集合和一个命名群上如下

上面的导入列表是 Instance/Rng/AFT.v 自身的，逐字，包括该文件本身；更短的前缀会让探针无缘无故地通过。

本文件的保护内容。在 PR "代数承载者是集合"（2026-09-17）之前，[free_rng_ab_via_GAFT] 和 [free_ring_via_GAFT] 使用 [solution_set_of_adjunction] 应用于它们本应生成的伴随结构，Instance/Rng/AFT.v 的头部也长篇幅说明了这一点。现在，它们消耗由自由环 TERM MODEL 构建的解集，通过 [Prop] 值的合同。这个变化对类型不可见——两种解读占据同一条语句——所以构建中的任何部分都不会注意到它被恢复。但本文件会注意到：下面的 [eq_refl] 回读标明了合同索引，而 [Fail] 则固定了新的解集不是旧的单元素集。

纪律。每个阴性对照都配有一个命名相同库常量的阳性对照；仪器已检查；每个阴性对照都在本文件的副本中去掉保护后重新运行，以便能读出拒绝类型而不是猜测。记录的类型是转换（两个），位于仪器检查旁，其拒绝是缺少的名称。
*)

(** ** Instrument check / ** 仪表检查 *)

Fail Check zzz_no_such_constant_rng_aft.

(** ** Positive controls / ** 阳性对照 *)

Check @RngCongIdx.
Check @IsRngCongruence.
Check @QRng.
Check @QRng_insert.
Check @rng_ker.
Check @rng_ker_med.
Check @Rng_Forget_Ab_solution_set_prop.
Check @Rng_Forget_solution_set_prop.
Check @free_rng_ab_via_GAFT.
Check @free_ring_via_GAFT.

(*
The circular readings are KEPT and are still checkable; they are the
   comparison, not the delivery.

--------
循环读数被保留并且仍然可以检查；它们是比较，而不是交付。
*)
Check @Rng_Forget_Ab_solution_set_from_adjunction.
Check @Rng_Forget_solution_set_from_adjunction.
Check @free_rng_ab_via_GAFT_from_adjunction.
Check @free_ring_via_GAFT_from_adjunction.

(** ** The index readbacks: WHICH solution set each application consumes / ** 索引回读：每个应用程序使用哪个解决方案集 *)

Section IndexReadbacks.

Context (A : Ab).
Context (X : Sets).

(*
The [Ab] half: the index is the congruence type on the free-ring terms
   over [A], and the objects are the quotients.

--------
[Ab] 一半：指标是在 [A] 上自由环项的合同类型，对象是商。
*)
Example prng_ab_index :
  sol_index (Rng_Forget_Ab_solution_set_prop A) = RngCongIdx A := eq_refl.

Example prng_ab_obj (i : RngCongIdx A) :
  sol_obj (Rng_Forget_Ab_solution_set_prop A) i = QRng (`1 i) (`2 i)
  := eq_refl.

(*
The [Sets] half takes the SAME index, over the free abelian group on
   [X] -- the direct route, not a composite of two adjunctions.

--------
[Sets] 半群取相同的指标，在 [X] 上的自由阿贝尔群上 —— 直接路径，而不是两个伴随的复合。
*)
Example prng_sets_index :
  sol_index (Rng_Forget_solution_set_prop X)
    = RngCongIdx (FreeAbObject X) := eq_refl.

Example prng_sets_obj (i : RngCongIdx (FreeAbObject X)) :
  sol_obj (Rng_Forget_solution_set_prop X) i = QRng (`1 i) (`2 i)
  := eq_refl.

(* And the circular ones are still the singleton, which is the contrast. / 而圆形的仍然是单例，这是对比。 *)
Example prng_circular_index :
  sol_index (Rng_Forget_Ab_solution_set_from_adjunction A) = poly_unit
  := eq_refl.

End IndexReadbacks.

(**
** NEGATIVE 1 (CONVERSION): the new solution set is not the old one

    If a later edit points [Rng_Forget_Ab_solution_set_prop] back at
    [solution_set_of_adjunction], this line stops refusing.  The control is
    [prng_circular_index] above, which IS [eq_refl] for the old one.

--------
** 负面 1（转换）：新的解集不是旧的解集

如果稍后的编辑将 [Rng_Forget_Ab_solution_set_prop] 指回 [solution_set_of_adjunction]，这一行将停止拒绝。 控制在上方的 [prng_circular_index]，对于旧的解集，它就是 [eq_refl]。
*)

Fail Example prng_n1_prop_index_is_not_singleton (A : Ab) :
  sol_index (Rng_Forget_Ab_solution_set_prop A) = poly_unit := eq_refl.

(**
** NEGATIVE 2 (CONVERSION): the two applications are different terms

    [free_rng_ab_via_GAFT] and [free_rng_ab_via_GAFT_from_adjunction]
    inhabit the same type and are NOT the same term.  [GAFT] is [Qed], so
    neither reduces; what this pins is that the two are not syntactically
    identified, which is what would happen if one were defined as the
    other.

--------
** 负面 2（转换）：这两个应用是不同的术语

    [free_rng_ab_via_GAFT] 和 [free_rng_ab_via_GAFT_from_adjunction]
    属于同一类型，但不是同一个术语。[GAFT] 等于 [Qed]，所以
    都不会被约简；这表明两者在语法上没有被识别为相同，如果一个被定义为另一个，就会发生这种情况。
*)

Fail Example prng_n2_applications_differ :
  free_rng_ab_via_GAFT = free_rng_ab_via_GAFT_from_adjunction := eq_refl.

(**
** THE PAYOFF: both applications at named objects

    [ring_ab Int_Ring] is the integers as an abelian group;
    [nat_setoid_object] and [bool_setoid_object] are named sets.  Before
    this PR these lines would have exhibited a free ring obtained from an
    adjunction that was assumed in order to obtain it.

--------
** 收益：两个应用于命名对象

[ring_ab Int_Ring] 是作为阿贝尔群的整数；
[nat_setoid_object] 和 [bool_setoid_object] 是命名集合。在这个 PR 之前，这些行本会展示一个通过假定附加以获得的自由环。
*)

Section ConcreteWitnesses.

Definition prng_ZAb : Ab := ring_ab Int_Ring.

(* The free ring on the integers as an abelian group. / 作为阿贝尔群的整数上的自由环。 *)
Check (`1 free_rng_ab_via_GAFT prng_ZAb).
Check (Rng_Forget_Ab_solution_set_prop prng_ZAb).
Check (free_rng_ab_via_GAFT_comparison prng_ZAb).
Check (free_rng_ab_via_GAFT_unit prng_ZAb).

(* The free ring on a named set, twice. / 命名集合上的自由环，两次。 *)
Check (`1 free_ring_via_GAFT nat_setoid_object).
Check (`1 free_ring_via_GAFT bool_setoid_object).
Check (Rng_Forget_solution_set_prop nat_setoid_object).
Check (free_ring_via_GAFT_comparison nat_setoid_object).
Check (free_ring_via_GAFT_unit nat_setoid_object).

(*
And the congruence index at a named object, which is the thing that
   made the whole construction fit.

--------
以及在一个具名对象上的一致性索引，这就是使整个结构契合的东西。
*)
Check (RngCongIdx prng_ZAb).
Check (RngCongIdx (FreeAbObject nat_setoid_object)).

End ConcreteWitnesses.
