Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Elements.Kan.

Generalizable All Variables.

(** * Probes guarding Construction/Elements/Kan.v / * 探针守护 Construction/Elements/Kan.v *)

(*
This file pins every strict attempt that Construction/Elements/Kan.v MADE
   AND LOST, and every universe boundary its header claims, so that a later
   change which quietly makes one of them succeed — or which renames the
   constants out from under the claim — breaks the build loudly instead of
   leaving the header's prose stale.  It follows the convention of
   Test/ProbePostcompose.v and Test/ProbeQuiverConstructions.v.

   The import list is the target file's, in the target file's order, with the
   target itself appended.  That matters: a probe compiled against a short
   PREFIX of the real imports can fail for a missing-coercion or
   missing-notation reason and thereby pass VACUOUSLY.  (Instance/Field/Frac.v
   records an episode of exactly that.)  The target is Required last, so its
   names win any contest.

   TWO KINDS, KEPT LEXICALLY APART.

     CONVERSION negatives are written [Fail Definition ... := eq_refl] and say
     that two well-typed terms are not definitionally equal.

     FORMABILITY negatives are written [Fail Check] and say that a term
     cannot be elaborated at all, here always because of a universe
     constraint.

   Each negative was stripped of its [Fail] and the resulting error read; the
   diagnosis is recorded beside it.  In batch [coqc] a SUCCEEDING [Fail]
   prints nothing, so the exit code is the only signal, which is why the
   stripped run is part of the procedure and not optional.  Positive controls
   accompany each group, and the sharpest ones differ from their negative in
   exactly the disputed spot.

   Inventory: 7 conversion negatives, 3 formability negatives, 12 positive
   controls.

--------
这个文件记录了 Construction/Elements/Kan.v 的每一次严格尝试及其失败情况，以及其头文件声明的每一个宇宙边界，以便后来进行的更改——无论是悄悄使其中某个尝试成功，还是重命名常量从而破坏声明——都会显著地导致构建失败，而不是让头文件的文字描述过时。它遵循了 Test/ProbePostcompose.v 和 Test/ProbeQuiverConstructions.v 的惯例。

导入列表是目标文件的列表，按目标文件的顺序排列，并附加上目标文件本身。这很重要：针对真实导入的短前缀编译的探针可能因为缺少强制转换或缺少符号的原因而失败，从而虚空地通过。（Instance/Field/Frac.v 记录了一个完全符合这种情况的实例。）目标文件必须最后列出，因此它的名称在任何竞争中都会获胜。

两种类型，词汇上分开。

CONVERSION 负例写作 [Fail Definition ... := eq_refl]，并表示两个类型良好的项在定义上不相等。

可形成性负面写作 [Fail Check]，并说明某个术语根本无法展开，这里总是由于宇宙约束。

每个阴性样本都去掉了其 [Fail] 并读取了由此产生的错误；诊断记录在其旁边。在批次 [coqc] 中，随后的 [Fail] 什么也不打印，因此退出代码是唯一信号，这就是为什么去掉处理的运行是程序的一部分而不是可选的原因。每组都有阳性对照，而且最明显的阳性样本与其阴性样本在正是争议的部位有所不同。

库存：7个转换负面，3个可成形性负面，12个正面控制。
*)

(** ** Group 1 (CONVERSION): the nat/cone round trips / ** 第1组（转换）：自然/圆锥往返 *)

Section RoundTripConversion.

Context {D : Category}.
Context (K : D ⟶ Sets).
Context {a : D}.
Context (tau : K ⟹ [Hom a,─]).
Context (psi : ACone a (Elements_proj K)).
Context (d : D) (x : K d).
Context (j : Elements K).

(*
POSITIVE CONTROL 1.  The instrument is not rejecting everything: an
   [eq_refl] between a term and itself, in exactly the shape the negatives
   below use, is accepted.

--------
阳性对照 1.  仪器并未拒绝所有内容：一个术语与其自身之间的 [eq_refl]，以与下面的阴性案例完全相同的形式，是被接受的。
*)
Definition control_instrument :
  kan_nat_of_cone K (kan_cone_of_nat K tau)
    = kan_nat_of_cone K (kan_cone_of_nat K tau) := eq_refl.

(*
POSITIVE CONTROL 2.  The DATA of round trip 1 does return on the nose:
   the component of the recovered transformation, applied to an element, is
   the original component applied to that element.

--------
阳性对照 2。往返第 1 轮的数据确实精确返回：恢复的变换的分量作用于一个元素时，就是原始分量作用于该元素。
*)
Definition control_rt1_applied :
  @transform D Sets K ([Hom a,─])
     (kan_nat_of_cone K (kan_cone_of_nat K tau)) d x
  = @transform D Sets K ([Hom a,─]) tau d x := eq_refl.

(*
NEGATIVE 1 (CONVERSION).  Round trip 1 at the WHOLE [Transform] record.
   Refuted.  [Transform] carries primitive projections with eta conversion,
   so record equality reduces to field equality, and the [naturality] and
   [naturality_sym] fields of the rebuilt transformation are the terms
   [kan_nat_naturality]/[kan_nat_naturality_sym] rather than tau's own; `≈`
   is [crelation]-valued, so there is no definitional proof irrelevance to
   close the gap.  Stripped error: "cannot unify
   kan_nat_of_cone K (kan_cone_of_nat K tau) and tau".

--------
否定 1（转换）。在完整的 [Transform] 记录上进行往返转换 1。已驳回。[Transform] 携带带有 eta 转换的原始投影，因此记录相等性归结为字段相等性，而重建转换的 [naturality] 和 [naturality_sym] 字段是 [kan_nat_naturality]/[kan_nat_naturality_sym] 术语，而不是 tau 本身；`≈` 的值是 [crelation]，因此没有定义性证明的无关性来弥补差距。剥离错误：“无法统一 kan_nat_of_cone K (kan_cone_of_nat K tau) 和 tau”。
*)
Fail Definition neg_rt1_record :
  kan_nat_of_cone K (kan_cone_of_nat K tau) = tau := eq_refl.

(*
NEGATIVE 2 (CONVERSION).  Not even the component FAMILY returns, because
   each component is a [SetoidMorphism] record whose [proper_morphism] field
   is rebuilt from [kan_leg_respects].  Together with control 2 this locates
   the obstruction exactly: the underlying functions agree, the packaged
   proofs do not.

--------
负数 2（转换）。甚至连组件 FAMILY 都没有返回，因为每个组件都是一个 [SetoidMorphism] 记录，其 [proper_morphism] 字段是从 [kan_leg_respects] 重建的。连同控件 2，这准确地定位了阻塞：底层函数一致，但打包的证明不一致。
*)
Fail Definition neg_rt1_family :
  @transform D Sets K ([Hom a,─])
     (kan_nat_of_cone K (kan_cone_of_nat K tau))
  = @transform D Sets K ([Hom a,─]) tau := eq_refl.

(*
NEGATIVE 3 (CONVERSION).  The same at a single component, so that the
   failure is not attributed to the family's outer lambda.

--------
负三（转换）。在单个组件上相同，因此故障不归因于家庭的外部 lambda。
*)
Fail Definition neg_rt1_component :
  @transform D Sets K ([Hom a,─])
     (kan_nat_of_cone K (kan_cone_of_nat K tau)) d
  = @transform D Sets K ([Hom a,─]) tau d := eq_refl.

(*
POSITIVE CONTROL 3.  Round trip 2's LEG returns on the nose once the
   sigma object is a literal pair.

--------
阳性对照 3。当 sigma 对象是字面对时，往返 2 的航段会准确返回。
*)
Definition control_rt2_pair :
  @vertex_map (Elements K) D a (Elements_proj K)
     (kan_cone_of_nat K (kan_nat_of_cone K psi)) ((d; x) : Elements K)
  = @vertex_map (Elements K) D a (Elements_proj K) psi
     ((d; x) : Elements K) := eq_refl.

(*
NEGATIVE 4 (CONVERSION).  The same leg at a VARIABLE object.  Refuted for
   a cause INDEPENDENT of negative 1's: the rebuilt leg family is
   [fun j => leg psi (`1 j; `2 j)], and stdlib [sigT] has no eta rule here —
   Lib/Foundation.v's [Set Primitive Projections] governs this library's own
   records, not [sigT].  This is why Kan.v's [kan_cone_nat_cone] destructs
   the pair before closing by [reflexivity], and control 3 is the same
   statement with the pair destructed.

--------
负 4（转换）。在可变对象上的同一条腿。由于与负 1 无关的原因被驳回：重建的腿族是 [fun j => leg psi (`1 j; `2 j)]，而标准库 [sigT] 在此没有 eta 规则——Lib/Foundation.v 的 [Set Primitive Projections] 管辖此库自身的记录，而不是 [sigT]。这就是为什么 Kan.v 的 [kan_cone_nat_cone] 在通过 [reflexivity] 关闭之前先析构该对，并且控制 3 是同一条语句，只是对已被析构。
*)
Fail Definition neg_rt2_leg :
  @vertex_map (Elements K) D a (Elements_proj K)
     (kan_cone_of_nat K (kan_nat_of_cone K psi)) j
  = @vertex_map (Elements K) D a (Elements_proj K) psi j := eq_refl.

(*
NEGATIVE 5 (CONVERSION).  Round trip 2 at the WHOLE [ACone] record.  Both
   causes above apply, and additionally the [cone_coherence] field is
   rebuilt from [kan_cone_coherence].

--------
负5（转换）。在整个 [ACone] 记录上进行往返 2。上述两种原因都适用，此外 [cone_coherence] 字段是从 [kan_cone_coherence] 重建的。
*)
Fail Definition neg_rt2_record :
  kan_cone_of_nat K (kan_nat_of_cone K psi) = psi := eq_refl.

End RoundTripConversion.

(** ** Group 2 (CONVERSION): the Δ bridge / ** 第2组（转换）：Δ桥 *)

Section DeltaConversion.

Context {D : Category}.
Context (K : D ⟶ Sets).
Context {a : D}.
Context (psi : ACone a (Elements_proj K)).
Context (theta : Δ[Elements K](a) ⟹ Elements_proj K).
Context (j : Elements K).

(*
POSITIVE CONTROLS 4 and 5.  BOTH leg families of the Δ bridge return on
   the nose at a VARIABLE object — no sigma is taken apart on this route, so
   negative 4's obstruction is absent here.  These two controls are what
   makes negatives 6 and 7 informative: the only thing left to fail is the
   law fields.

--------
阳性对照4和5。Δ桥的两个支腿族在可变物体的鼻部回归——这条路线没有拆解任何西格玛，因此这里没有负4的阻塞。这两个对照使负6和7具有信息性：唯一可能失败的是法律场。
*)
Definition control_delta_cone_leg :
  @vertex_map (Elements K) D a (Elements_proj K)
     (kan_cone_of_transform K (kan_transform_of_cone K psi)) j
  = @vertex_map (Elements K) D a (Elements_proj K) psi j := eq_refl.

Definition control_delta_transform_component :
  @transform (Elements K) D (Δ[Elements K](a)) (Elements_proj K)
     (kan_transform_of_cone K (kan_cone_of_transform K theta)) j
  = @transform (Elements K) D (Δ[Elements K](a)) (Elements_proj K) theta j
  := eq_refl.

(*
NEGATIVE 6 (CONVERSION).  Cone → Δ-transformation → cone at the WHOLE
   record.  Refuted: the [cone_coherence] field is rebuilt through
   [kan_cone_of_transform_coherence], which spends an [id_right] because
   [fmap[Δa] f] is [id] and the cone law has no such factor.

--------
负 6（转换）。锥 → Δ-变换 → 锥在整个记录。 驳回：[cone_coherence] 字段通过 [kan_cone_of_transform_coherence] 重建，因为 [kan_cone_of_transform_coherence] 消耗了一个 [id_right]，因为 [fmap[Δa] f] 是 [id]，而锥定律没有这样的因子。
*)
Fail Definition neg_delta_cone_record :
  kan_cone_of_transform K (kan_transform_of_cone K psi) = psi := eq_refl.

(*
NEGATIVE 7 (CONVERSION).  The other direction, at the whole [Transform]
   record; same cause on [naturality]/[naturality_sym].

--------
负7（转换）。另一个方向，在整个 [Transform] 记录上；[naturality]/[naturality_sym] 上的原因相同。
*)
Fail Definition neg_delta_transform_record :
  kan_transform_of_cone K (kan_cone_of_transform K theta) = theta := eq_refl.

End DeltaConversion.

(** ** Group 3 (FORMABILITY): objects strictly above homs / ** 第3组（可成形性）：严格高于homs的物体 *)

(*
Kan.v's header states that both sides of the isomorphism force D's OBJECT
   universe to sit at or below D's HOM universe, and that the restriction
   enters at the PACKAGING rather than at the passages.  Both halves of that
   claim are pinned here.

--------
Kan.v 的标题指出，同构的两边都迫使 D 的 OBJECT 宇宙位于 D 的 HOM 宇宙之上或之下，并且这个限制出现在 PACKAGING 而不是在通道处。该声明的两部分都在此固定。
*)

Section ObjectsAboveHoms.

Universes uo uh us.
Constraint uh < uo.
Constraint uh < us.

(*
NEGATIVE 8 (FORMABILITY).  The cone presheaf is not formable when D's
   objects sit strictly above its homs.  Stripped error: "universe
   inconsistency: Cannot enforce uh = _ because uh < uo <= _".

--------
否定 8（可形成性）。当 D 的对象严格位于其同态之上时，锥形预层不可形成。简化错误："宇宙不一致：无法强制 uh = _ 因为 uh < uo <= _"
*)
Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              KanCone K).

(*
NEGATIVE 9 (FORMABILITY).  The transformation presheaf independently
   refuses at the same setting — a set of natural transformations is a family
   indexed by D's objects and must be an object of [Sets] at the hom level.

--------
负 9（可形成性）。变换预层在相同的设置下独立拒绝——一组自然变换是按 D 的对象索引的族，且必须是在同态层面的 [Sets] 的对象。
*)
Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              KanNat K).

(* NEGATIVE 10 (FORMABILITY).  Hence the natural isomorphism itself. / 负10（可形成性）。因此，自然同构本身。 *)
Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              kan_coyoneda K).

(*
POSITIVE CONTROLS 6 and 7.  AT THE VERY SAME UNIVERSE SETTING the two raw
   passages ARE formable.  These are the sharp controls: they differ from
   negatives 8-10 in exactly which constant is named, so the refusal is
   attributable to the packaging (the presheaf and the setoid of
   transformations) and not to [Elements], to [Sets], or to the section's
   constraints being unsatisfiable.

--------
阳性对照6和7。在完全相同的宇宙设置下，这两段原始文本都是可形成的。这些是精确的对照：它们与阴性对照8-10的区别正好在于命名的是哪个常数，因此拒绝是归因于包装（预层和变换的集合）而不是 [Elements]、[Sets]，或者该节的约束无法满足。
*)
Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) (a : D)
           (tau : K ⟹ [Hom a,─]) => kan_cone_of_nat K tau).

Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) (a : D)
           (psi : ACone a (Elements_proj K)) => kan_nat_of_cone K psi).

End ObjectsAboveHoms.

Section ObjectsBelowHoms.

Universes vo vh vs.
Constraint vo <= vh.
Constraint vh < vs.

(*
POSITIVE CONTROLS 8, 9 and 10.  With the inequality the other way round
   all three constants elaborate, so negatives 8-10 are about the direction
   of that inequality and not about the [Category@{_ _ _}] annotation
   itself.

--------
阳性对照 8、9 和 10。 如果不等式方向相反，所有三个常数都会详细说明，因此负号 8-10 是关于该不等式的方向，而不是关于 [Category@{_ _ _}] 注释本身。
*)
Check (fun (D : Category@{vo vh vh}) (K : D ⟶ Sets@{vh vs}) => KanCone K).
Check (fun (D : Category@{vo vh vh}) (K : D ⟶ Sets@{vh vs}) => KanNat K).
Check (fun (D : Category@{vo vh vh}) (K : D ⟶ Sets@{vh vs}) =>
         kan_coyoneda K).

End ObjectsBelowHoms.

(** ** Group 4: the delivered strengths, guarded / ** 第4组：传递的力量，谨慎 *)

Section Delivered.

Context {D : Category}.
Context (K : D ⟶ Sets).

(*
POSITIVE CONTROLS 11 and 12.  The two claims Kan.v makes at [eq_refl]
   about the natural isomorphism being an UPGRADE of the pointwise one are
   restated here, so that a change to either definition which broke the
   identification would be caught in this file as well as in the target.

--------
阳性对照 11 和 12。Kan.v 在 [eq_refl] 中对自然同构是逐点同构的升级所做的两个声明在此重述，以便对任一定义的更改如果破坏了这种识别，既会在此文件中被发现，也会在目标文件中被发现。
*)
Definition control_to_component (a : D) :
  transform[to (kan_coyoneda K)] a = to (kan_iso_at K a) := eq_refl.

Definition control_from_component (a : D) :
  transform[from (kan_coyoneda K)] a = from (kan_iso_at K a) := eq_refl.

End Delivered.
