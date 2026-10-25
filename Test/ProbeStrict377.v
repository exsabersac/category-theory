Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Construction.Quotient.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Theory.Equivalence.Strict.

(**
* Boundary probe for Theory/Equivalence/Strict.v (Mac Lane IV.4.3)

    Every rejection the target's header records is pinned here, from
    OUTSIDE the target, so that a rename breaks the probe loudly instead
    of turning a guard vacuously green.  The import list is the target's
    own, plus the target.

    Twelve negatives in THREE kinds, told apart by the error TEXT rather
    than by label:

      TYPING       (3) -- a plain "has type ... while it is expected to
                          have type ...", with no "cannot unify" clause;
                          negatives 1, 2 and 5.
      CONVERSION   (5) -- "cannot unify" between two terms of ONE type,
                          or a tactic script that does not close;
                          negatives 3, 4, 6, 7 and 8.
      FORMABILITY  (4) -- "universe inconsistency: Cannot enforce ...";
                          negatives 9 to 12.

    Negative 5 was expected to be a conversion rejection and is NOT: the
    two adjunctions have different TYPES, because their left adjoints are
    two non-convertible functors, so the error carries no "cannot unify"
    clause at all.  It is counted as typing.

    plus a scope-free instrument check.  Each was stripped ONE AT A TIME,
    the others left in place, the file compiled alone, and the whole error
    message read.  Every constant a negative names also appears in a
    command outside any guarded position.

--------
* Theory/Equivalence/Strict.v 的边界探针（Mac Lane IV.4.3）

目标的标题记录的每一次拒绝都固定在这里，从目标的外部，这样重命名会大声地破坏探针，而不是使保护徒然变绿。导入列表是目标自己的，加上目标本身。

三种类型的十二个底片，通过错误文本而不是标签来区分：

打字       (3) -- 一个简单的“具有类型...，但预期具有类型...”，没有“无法合并”部分；负例 1、2 和 5。
转换       (5) -- “无法合并”两个相同类型的项，或者战术脚本未完成；负例 3、4、6、7 和 8。
可形成性   (4) -- “宇宙不一致：无法强制执行...”；负例 9 到 12。

负5本应是转换拒绝，但实际上不是：这两个伴随有不同的类型，因为它们的左伴随是两个不可转换的函子，所以错误根本不包含“无法统一”子句。它被算作类型错误。

加上一个无作用域的工具检查。 每次只移除一个，其余的保持原位，文件单独编译，并读取整个错误消息。 每个常量，一个负名称，也出现在任何受保护位置之外的命令中。
*)

Generalizable All Variables.

(** ** Instrument check / ** 仪表检查 *)

(*
If a guarded command could succeed for want of a name, this one would
   too.  It must be rejected.

--------
如果一个受守护的命令因为缺少名称而可能成功，那么这个命令也会如此。它必须被拒绝。
*)
Fail Check probe377_no_such_constant_anywhere.

(** ** Controls: every constant the negatives name, named outside a guard / ** 控件：每个负数常量的名称，在保护之外命名 *)

Check @unit.
Check @counit.
Check @id_cast.
Check @id_cast_iso.
Check @iso_id.
Check @eso_iso.
Check @LeftAdjointRightInverse.
Check @lari_left.
Check @lari_adj.
Check @lari_obj.
Check @lari_unit.
Check @surjective_ESO.
Check @SurjectiveOnObjects.
Check @SurjectiveOnObjects_Id.
Check @ff_surjective_left.
Check @ff_surj_eq.
Check @ff_surj_adj.
Check @ff_surj_eso.
Check @ff_surj_eso_adjoint_equivalence.
Check @ff_surjective_adjoint_equivalence.
Check @ff_surjective_counit_iso.
Check @ff_eso_inverse.
Check @adj_equivalence.
Check @Adjunction.
Check IndT.
Check indiscrete_LARI.
Check Indiscrete.
Check @Erase.
Check erase_pt.

(** ** TYPING negatives: the two identity readings that are not statable / ** 打字负面：无法表达的两个同一性读数 *)

Section UnitAndCounitTyping.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context (P : LeftAdjointRightInverse S).
Context (c : C).

(*
Control: the delivered form of "unit the identity", against the
   identity TRANSPORTED along the object equation.

--------
控制：传递形式的“单位身份”，针对沿着对象方程传输的身份。
*)
Check (@unit A C (lari_left P) S (lari_adj P) c
         ≈ id_cast (eq_sym (lari_obj P c))).

(* Control: both sides of the negative are individually well-formed. / 控制：否定的两边各自都是良构的。 *)
Check (@unit A C (lari_left P) S (lari_adj P) c).
Check (@id C c).

(*
NEGATIVE 1 (TYPING).  The unit runs [c ~> S (lari_left c)] and the
   identity runs [c ~> c]; the two lie in one hom-set only when the two
   objects coincide at Leibniz equality, which is exactly what
   [lari_obj] supplies and what [≈] cannot.

--------
负 1（打字）。该单位运行 [c ~> S (lari_left c)]，身份运行 [c ~> c]；仅当两个对象在莱布尼茨等式下重合时，它们才位于同一个同态集合中，而这正是 [lari_obj] 提供的，也是 [≈] 无法提供的。
*)
Fail Check (@unit A C (lari_left P) S (lari_adj P) c ≈ @id C c).

End UnitAndCounitTyping.

Section CounitTyping.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context `{@Category.Theory.Functor.Full A C S}.
Context `{@Faithful A C S}.
Context (surj : SurjectiveOnObjects S).
Context (a : A).

(*
Control: the counit is well-formed, and is an isomorphism -- which is
   the strength Mac Lane's epsilon actually has.

--------
控制：协单位是良构的，并且是一个同构——这实际上是麦克莱恩的ε所具有的强度。
*)
Check (@counit A C (ff_surjective_left surj) S (ff_surj_adj surj) a).
Check (ff_surjective_counit_iso surj a).
Check (@id A a).

(*
NEGATIVE 2 (TYPING).  The counit runs
   [ff_surjective_left (S a) ~> a], and the chosen preimage of [S a] need
   not be [a]: the exercise gives an isomorphism, not an identity.

--------
负数 2（输入）。余单位运行 [ff_surjective_left (S a) ~> a]，且 [S a] 的选择原像不必是 [a]：该练习给出的是同构，而不是恒等式。
*)
Fail Check (@counit A C (ff_surjective_left surj) S (ff_surj_adj surj) a
            ≈ @id A a).

End CounitTyping.

(*
Control: the counit of the delivered adjoint equivalence at the
   non-degenerate witness is well-formed, and is an isomorphism.

--------
控制：在非退化见证处所交付的伴随等价的余单位是良构的，并且是一个同构。
*)
Check (@counit (Indiscrete bool) _1 (lari_left indiscrete_LARI)
         (Erase (Indiscrete bool)) (lari_adj indiscrete_LARI) false).

Check (@adj_equiv_counit_iso _1 (Indiscrete bool) IndT
         (Erase (Indiscrete bool)) indiscrete_adjoint_equivalence false).

(*
A trap worth recording rather than hiding.  At the [Indiscrete bool]
   witness the comparison of that counit with the identity IS well-typed,
   and indeed holds: [Indiscrete]'s hom family ignores its endpoints, so
   [true ~> false] and [false ~> false] are one and the same type, whose
   sole inhabitant is [tt].  The endpoints still differ
   ([indiscrete_counit_endpoints_differ]).  So the typing obstruction is
   stated at an abstract [A] above, where nothing collapses the two
   hom-sets, and NOT at this witness.

--------
一个值得记录而不是隐藏的陷阱。在 [Indiscrete bool] 处，观察该 counit 与恒等 IS 的比较是类型良好的，确实成立：[Indiscrete] 的 hom 族忽略其端点，因此 [true ~> false] 和 [false ~> false] 是同一种类型，其唯一的元素是 [tt]。端点仍然不同（[indiscrete_counit_endpoints_differ]）。因此，类型阻碍在上方的抽象 [A] 处陈述，在那里没有将两个 hom 集合合并，而不是在这个见证处。
*)
Check (@counit (Indiscrete bool) _1 (lari_left indiscrete_LARI)
         (Erase (Indiscrete bool)) (lari_adj indiscrete_LARI) false
       ≈ @id (Indiscrete bool) false).

(* And it holds: both sides are the one inhabitant of [unit]. / 它成立：双方都是 [unit] 的唯一居民。 *)
Example p377_indiscrete_counit_is_id :
  @counit (Indiscrete bool) _1 (lari_left indiscrete_LARI)
    (Erase (Indiscrete bool)) (lari_adj indiscrete_LARI) false
  ≈ @id (Indiscrete bool) false.
Proof. cbn; reflexivity. Qed.

(** ** CONVERSION negatives / ** 转化否定 *)

Section StrictReadbacks.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context `{@Category.Theory.Functor.Full A C S}.
Context `{@Faithful A C S}.
Context (surj : SurjectiveOnObjects S).
Context (c : C).

(*
Control: the residue is exhibited at Leibniz equality -- the unit IS
   [fmap[S] id] composed with the transported identity.

--------
控制：剩余在莱布尼茨等式中显示——单位是 [fmap[S] id] 与传送的恒等式组合。
*)
Check (ff_surj_unit_residue surj c).

(* Control: the [≈] form does hold. / 控制：[≈] 表格确实有效。 *)
Check (ff_surj_unit_is surj c).

(*
NEGATIVE 3 (CONVERSION).  [unit] is [⌊id⌋], so it carries an
   [fmap[S] id] that conversion cannot remove at an abstract [S].

--------
负3（转换）。[unit] 是 [⌊id⌋]，因此它携带一个 [fmap[S] ID，该 ID 在抽象的 [S] 上转换无法移除。
*)
Fail Example p377_n3 :
  @unit A C (ff_surjective_left surj) S (ff_surj_adj surj) c
    = id_cast (eq_sym (ff_surj_eq surj c)) := eq_refl.

(* Controls: both actions of the two left adjoints agree on the nose. / Controls: both actions of the two left adjoints agree on the nose. / 控制：两个左伴随的两个动作在本质上完全一致。 *)
Check (ff_surj_eso_inverse_obj surj c).
Check (ff_surj_eso_inverse_strict surj).

(*
NEGATIVE 4 (CONVERSION).  The whole functor RECORDS are not
   Leibniz-equal: the three law fields are rebuilt.

--------
负4（转换）。整个函子 RECORDS 并不雷布尼茨相等：三个律域被重建。
*)
Fail Example p377_n4 :
  @ff_eso_inverse A C S _ _ (ff_surj_eso surj) = ff_surjective_left surj
  := eq_refl.

(*
Control: the adjunction extracted from the delivered adjoint
   equivalence IS the directly built one.

--------
控制：从已传递的伴随等价中提取的伴随关系就是直接构建的那一个。
*)
Check (ff_surj_equiv_adj surj).

(*
NEGATIVE 5 (TYPING).  The adjunction the alternative route produces is
   not the directly built one -- and the two do not even have the same
   type, the left adjoints being non-convertible functors.

--------
负 5（打字中）。 替代路径产生的伴随不是直接构建的那个——而且两者甚至类型不同，左伴随是不可转换的函子。
*)
Fail Example p377_n5 :
  @adj_equivalence C A _ S (ff_surj_eso_adjoint_equivalence surj)
    = ff_surj_adj surj := eq_refl.

(*
NEGATIVE 6 (CONVERSION).  The alternative route's unit is not the
   transported identity on the nose either.  Note that this error prints
   exactly like negative 3's, both sides displaying as [unit] with the
   implicit arguments hidden; what separates the two routes is negative 7
   below, not this one.

--------
负 6（转换）。替代路径的单元也不是传输的标识。请注意，这个错误的打印方式与负 3 完全相同，两边都显示为 [unit]，隐含参数被隐藏；区分这两条路径的是下面的负 7，而不是这一条。
*)
Fail Example p377_n6 :
  @unit A C (@ff_eso_inverse A C S _ _ (ff_surj_eso surj)) S
    (@adj_equivalence C A _ S (ff_surj_eso_adjoint_equivalence surj)) c
    = id_cast (eq_sym (ff_surj_eq surj c)) := eq_refl.

(*
Control: on the DIRECT route the [≈] form is reached by unfolding the
   unit and computing -- the residue is one [fmap_id].

--------
控制：在直接路径上，通过展开单元并计算到达 [≈] 表单——余数是一个 [fmap_id]。
*)
Definition p377_route_control :
  @unit A C (ff_surjective_left surj) S (ff_surj_adj surj) c
    ≈ id_cast (eq_sym (ff_surj_eq surj c))
  := ltac:(unfold unit; simpl; rewrite fmap_id, id_left; reflexivity).

(*
NEGATIVE 7 (CONVERSION).  The same script on the ALTERNATIVE route does
   not close, and the error names where it stops: the goal is
   [equiv_adj_to EquivalenceOfCategories_sym id], i.e. the [symmetry]
   taken on [Functor_Setoid], whose [Equivalence] obligation is closed
   opaquely at Theory/Functor.v.  This is the measurement that decides
   which route is shipped.

--------
负 7（转换）。在替代路径上的相同脚本无法关闭，并且错误显示它停止的地方：目标是 [equiv_adj_to EquivalenceOfCategories_sym id]，即在 [Functor_Setoid] 上采取的 [symmetry]，其 [Equivalence] 义务在 Theory/Functor.v 中以不透明方式关闭。这是决定哪条路径被采用的衡量标准。
*)
Fail Definition p377_n7 :
  @unit A C (@ff_eso_inverse A C S _ _ (ff_surj_eso surj)) S
    (@adj_equivalence C A _ S (ff_surj_eso_adjoint_equivalence surj)) c
    ≈ id_cast (eq_sym (ff_surj_eq surj c))
  := ltac:(unfold unit; simpl; reflexivity).

End StrictReadbacks.

(*
Controls: at an [eq_refl] witness both legs of the repackaged
   isomorphism are [id] on the nose.

--------
控制：在 [eq_refl] 见证者处，重新包装的同构的两条腿都 [id] 在鼻子上。
*)
Check @surjective_ESO_refl_to.
Check @surjective_ESO_refl_from.

(*
NEGATIVE 8 (CONVERSION).  The whole isomorphism RECORD is nevertheless
   not [iso_id]: the two inverse-law fields are different proofs.

--------
负 8（转换）。然而，整个同构记录并不是 [iso_id]：两个逆律字段是不同的证明。
*)
Fail Example p377_n8 {C : Category} (c : C) :
  @eso_iso C C Id[C] (surjective_ESO (@SurjectiveOnObjects_Id C)) c
    = @iso_id C c := eq_refl.

(** ** FORMABILITY negatives / ** 可成形性缺点 *)

(*
The two categories' hom universes are identified in every delivered
   constant.  The cause is measured rather than attributed: the mere
   presence of functors in BOTH directions already forces it, before any
   adjunction is formed.

--------
每个传递的常数中都识别了这两类的同类宇宙。原因是被测量而非被归因：仅仅在两个方向上存在函子就已经强制了原因，在形成任何伴随之前。
*)

Section HomLevelBoundary.

Universes uo uh vo vh.
Constraint uh < vh.

Context (Au : Category@{uo uh uh}).
Context (Xu : Category@{vo vh vh}).

(*
Controls: both categories are formable at these declared levels, and a
   functor in the DIRECTION the bound permits elaborates.

--------
控制：这两个类别都可以在这些声明的级别上形成，并且一个在绑定允许的方向上的函子会展开。
*)
Check Au.
Check Xu.
Check (Au ⟶ Xu).

(*
NEGATIVE 9 (FORMABILITY).  The other direction does not: [Functor]
   forces the source's hom level below the target's.

--------
负 9（可成形性）。另一个方向则不行：[Functor] 强迫源的同质水平低于目标的同质水平。
*)
Fail Check (Xu ⟶ Au).

(*
NEGATIVE 10 (FORMABILITY).  Hence neither does the record, whose
   [lari_left] field is a functor the other way.

--------
负 10（可成型性）。因此，记录也不行，其 [lari_left] 字段是相反方向的函子。
*)
Fail Check (∀ S : Au ⟶ Xu, LeftAdjointRightInverse S).

End HomLevelBoundary.

(*
Hom is identified with proof as well, and that is a second, separate
   donor: it is already forced by [Adjunction], whose hom-set isomorphism
   lives in [Sets], where a setoid's carrier and relation universes
   coincide.

--------
同态也可以通过证明来识别，这是第二个独立的捐赠者：它已经被 [Adjunction] 强制，其中同态集合的同构存在于 [Sets]，在那里一个集合点的载体和关系宇宙相一致。
*)

Section HomProofBoundary.

Universes wo wh wp.
Constraint wh < wp.

Context (Bu : Category@{wo wh wp}).

(*
Controls: the category, its homs, and functors on it are all formable
   with hom declared strictly below proof.

--------
控制：该范畴、其同态以及其上的函子都可以构造，且同态严格声明在证明之下。
*)
Check Bu.
Check (∀ x y : Bu, x ~{Bu}~> y).
Check (Bu ⟶ Bu).

(* NEGATIVE 11 (FORMABILITY).  The adjunction is not. / 负11（可成形性）。附加部分不是。 *)
Fail Check (∀ F G : Bu ⟶ Bu, F ⊣ G).

(* NEGATIVE 12 (FORMABILITY).  Nor, therefore, is the record. / 负12（可成型性）。因此，记录也不是。 *)
Fail Check (∀ S : Bu ⟶ Bu, LeftAdjointRightInverse S).

End HomProofBoundary.
