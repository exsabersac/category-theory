(**
* Probe for the Freyd characterization (issue #436)

    Pins the measured boundaries of Adjunction/GAFT.v's necessity direction
    and of the biconditional, with negatives of three kinds kept lexically
    apart.  NAME-ABSENCE: n7, there is no field called [sol_unique] — the
    same KIND of refusal as the instrument, and it carries only half the
    argument, the other half being the four accepted [Check]s beside it that
    enumerate the record's fields; together they say that "solution set"
    here is weak factorization with no uniqueness clause.  CONVERSION: n1, the direct singleton
    family and Mac Lane's route through the comma-initial object agree on
    every data field but are not the same term; n8, the member is [F d] and
    not [F (U (F d))]; n3, a general solution set is not a singleton, which
    is what makes the necessity direction's singleton a real choice; n9, the
    manufactured family at [Id : Sets ⟶ Sets] agrees with the hand-built
    [Sets_Id_SolutionSet] in index, member and arrow but is not the same
    record, the two covering witnesses differing.  TYPING: n4, the
    sufficient direction keeps all three premises — dropping continuity does
    not ascribe.

    RECORDED CORRECTION: an earlier revision counted a fourth kind,
    UNIVERSE, for n6, "the biconditional inherits [GAFT]'s pin of both hom
    universes to [Set] — which the necessity direction does NOT".  [GAFT]'s
    [Set] came from Instance/Discrete.v's unannotated
    [DiscreteCat_Functor] through GAFT.v; the donor was annotated in
    the PR "algebraic carriers are sets" (2026-09-17) and n6 is now an
    accepted positive control beside its former control.  No UNIVERSE
    refusal remains in this file.

    The [eq_refl] readbacks are positive controls: the three data fields of
    the manufactured family, the collapse of the comma route's arrow to the
    unit, the identity of the biconditional's reverse half with [GAFT], and
    the [Sets] cross-check that reverse half IS the application the tree
    already had.  Each refutation was stripped one at a time in a copy of
    the whole file; the import list mirrors the two targets'.

--------
* 探测 Freyd 特征化（问题 #436）

固定了Adjunction/GAFT.v的必要性方向和双条件的测量边界，同时三种类型的否定在词汇上保持分离。名称缺失：n7，没有名为[sol_unique]的字段——这与该工具的拒绝类型相同，并且它只带有一半的论证，另一半由旁边列出记录字段的四个已接受[Check]构成；它们共同说明这里的“解集”是没有唯一性条款的弱因式分解。转换：n1，直接单例族和 Mac Lane 通过逗号开头的对象的路径在每个数据字段上都一致，但不是同一个项；n8，该成员是 [F d]，而不是 [F (U (F d))]；n3，一般解集不是单例，这也是使必要方向的单例成为真实选择的原因；n9，[Id : Sets ⟶ Sets] 的制造族在索引、成员和箭头上与手工构建的 [Sets_Id_SolutionSet] 一致，但不是同一记录，两者的覆盖见证者不同。类型：n4，充分方向保留所有三个前提——放弃连续性不会归属。

记录修正：早期的一个修订将第四种类型计为 n6 的 UNIVERSE，“该双条件继承了 [GAFT] 的两个同质宇宙引脚到 [Set] —— 而必要方向则没有”。[GAFT] 的 [Set] 来自 Instance/Discrete.v 中未经注释的 [DiscreteCat_Functor]，通过 GAFT.v；捐赠者在 PR“代数承载是集合”（2026-09-17）中有注释，n6 现在被接受为一个正向对照，除了其之前的对照。此文件中不再存在 UNIVERSE 拒绝。

[eq_refl] 的回读是阳性对照：制造的系列的三个数据字段，逗号线路箭头折叠到单元上，双条件反向半部与 [GAFT] 的一致性，以及 [Sets] 交叉检查该反向半部确实是树之前已有的应用程序。每个反驳在整个文件的副本中一次移除一个；导入列表与两个目标的列表相对应。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe436_absent_name.

(** ** A: FORMABILITY — no uniqueness is asked of a solution set / ** A: 可成形性——对解集不要求唯一性 *)

Check @sol_index.
Check @sol_obj.
Check @sol_arr.
Check @sol_covers.

(*
n7 NAME-ABSENCE: and there is no field called [sol_unique] — a
   reference-not-found, the instrument's own kind, which is why the four
   [Check]s above carry the rest of the claim

--------
n7 NAME-ABSENCE：并且没有名为 [sol_unique] 的字段——一种未找到引用的情况，是仪器自身的类型，这就是为什么上面的四个 [Check] 承载了其余的声明
*)
Fail Check @sol_unique.

(** ** B: CONVERSION — how far the unit family reads back / ** B：转换 — 单位系列回读的程度 *)

Section Conversion.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (d : D).

Example p436_index : sol_index (solution_set_of_adjunction A d) = poly_unit
  := eq_refl.

Example p436_obj (u : poly_unit) :
  sol_obj (solution_set_of_adjunction A d) u = F d := eq_refl.

Example p436_arr (u : poly_unit) :
  sol_arr (solution_set_of_adjunction A d) u = @unit _ _ _ _ A d := eq_refl.

(*
controls: Mac Lane's route agrees with the direct one on all three
   data fields, not only the arrow

--------
控制：Mac Lane 的路径在所有三个数据字段上都与直接路径一致，而不仅仅是箭头
*)
Example p436_via_index :
  sol_index (solution_set_of_adjunction_via_comma A d)
    = sol_index (solution_set_of_adjunction A d) := eq_refl.

Example p436_via_obj (u : poly_unit) :
  sol_obj (solution_set_of_adjunction_via_comma A d) u = F d := eq_refl.

Example p436_via_arr (u : poly_unit) :
  sol_arr (solution_set_of_adjunction_via_comma A d) u = @unit _ _ _ _ A d
  := eq_refl.

(* n1 CONVERSION: the two routes are nevertheless not the same term / n1 转换：尽管如此，这两条路线不是同一个术语 *)
Fail Example p436_routes_agree :
  solution_set_of_adjunction A d = solution_set_of_adjunction_via_comma A d
  := eq_refl.

(* n8 CONVERSION: the member is [F d], not [F (U (F d))] / n8 转换：成员是 [F d]，而不是 [F (U (F d))] *)
Fail Example p436_member_is_FUF (u : poly_unit) :
  sol_obj (solution_set_of_adjunction A d) u = F (U (F d)) := eq_refl.

(*
control: a solution set built from a weakly initial family keeps that
   family's index

--------
控制：由弱初始族构建的解集保持该族的指标
*)
Example p436_wif_index (W : WeaklyInitialFamily (=(d) ↓ U)) :
  sol_index (sols_of_wif U d W) = wif_index W := eq_refl.

(* n3 CONVERSION: so a general solution set is not a singleton / n3 转换：所以一般解集不是单元素集 *)
Fail Example p436_general_is_singleton (W : WeaklyInitialFamily (=(d) ↓ U)) :
  sol_index (sols_of_wif U d W) = poly_unit := eq_refl.

End Conversion.

(** ** C: TYPING — the sufficient direction keeps all three premises / ** C: 打字 — 足够的方向保持所有三个前提 *)

Check (fun (C D : Category) (U : C ⟶ D) (comp : @Complete C)
           (cont : @PreservesImageLimit C D U)
           (sols : ∀ d : D, SolutionSet U d) => GAFT U comp cont sols).

(* n4 TYPING: completeness and a solution set alone do not ascribe / n4 输入：完整性和仅有解集本身并不能赋予 *)
Fail Check (fun (C D : Category) (U : C ⟶ D) (comp : @Complete C)
                (sols : ∀ d : D, SolutionSet U d) => GAFT U comp sols).

(**
** D: the biconditional no longer inherits a [Set] pin

    RECORDED CORRECTION.  An earlier revision headed this section
    "UNIVERSE — the biconditional inherits GAFT's pin, the converse
    direction does not", and n6 below was a refusal: [GAFT_iff] was not
    formable over a category whose hom level is declared strictly above
    [Set], while [solution_set_of_adjunction] was.  [GAFT]'s [Set] came
    from Instance/Discrete.v's unannotated [DiscreteCat_Functor] through
    Adjunction/GAFT.v and [initial_from_weakly_initial]; annotating
    that donor in the PR "algebraic carriers are sets" (2026-09-17)
    removes it, and [GAFT_iff] is now ACCEPTED at those levels.  Both
    lines are kept as positive controls, so dropping the annotation
    refuses the second again and breaks this file.

--------
** D：双条件不再继承 [Set] 引脚

记录的更正。一版早期修订将本节标题定为“UNIVERSE — 双条件继承 GAFT 的引脚，而逆向不继承”，下面的 n6 是一次拒绝：[GAFT_iff] 无法在同类层级被声明严格高于 [Set] 的类别上形成，而 [solution_set_of_adjunction] 可以。[GAFT] 的 [Set] 来自 Instance/Discrete.v 中未标注的 [DiscreteCat_Functor]，通过 Adjunction/GAFT.v 和 [initial_from_weakly_initial]；在 PR“代数载体是集合”（2026-09-17）中标注该捐赠源会移除它，[GAFT_iff] 现在在那些层级上被接受。两行都保留作为阳性对照，因此去掉标注会再次拒绝第二行，并破坏该文件。
*)

Monomorphic Universes p436o p436h p436p.
Monomorphic Constraint Set < p436h.

(*
Coq identifies [p436h] with [p436p] here, so what this pair measures is
   freedom from [Set] and not freedom of three separate universes: the
   necessity direction is stated at [Category@{uo uh uh}].

--------
Coq 在这里将 [p436h] 与 [p436p] 识别为相同，因此这一对测量的是对 [Set] 的自由，而不是三个独立宇宙的自由：必要性方向在 [Category@{uo uh uh}] 中说明。
*)

(* control: necessity is free of the pin / 控制：必要性不受销钉约束 *)
Check (fun (Cu : Category@{p436o p436h p436p}) (Du : Category@{p436o p436h p436p})
           (F : Du ⟶ Cu) (U : Cu ⟶ Du) => @solution_set_of_adjunction Cu Du F U).

(* former n6: the biconditional is accepted there too / 前n6：那里也接受双条件 *)
Check (fun (Cu : Category@{p436o p436h p436p})
                (Du : Category@{p436o p436h p436p})
                (U : Cu ⟶ Du) => @GAFT_iff Cu Du U).

(** ** E: readbacks, and the [Sets] cross-check / ** E：回读，以及 [Sets] 交叉检查 *)

Example p436_rev_is_GAFT {C D : Category} (U : C ⟶ D) (comp : @Complete C)
  (cont : @PreservesImageLimit C D U) (sols : ∀ d : D, SolutionSet U d) :
  GAFT_iff_rev U comp (cont, sols) = GAFT U comp cont sols := eq_refl.

Example p436_sets_rev :
  Sets_Id_has_left = GAFT_at_Sets_Id := eq_refl.

Example p436_sets_index (d : Sets) :
  sol_index (solution_set_of_adjunction (@adj_id Sets) d)
    = sol_index (Sets_Id_SolutionSet d) := eq_refl.

Example p436_sets_obj (d : Sets) (u : poly_unit) :
  sol_obj (solution_set_of_adjunction (@adj_id Sets) d) u
    = sol_obj (Sets_Id_SolutionSet d) u := eq_refl.

Example p436_sets_arr (d : Sets) (u : poly_unit) :
  sol_arr (solution_set_of_adjunction (@adj_id Sets) d) u
    = sol_arr (Sets_Id_SolutionSet d) u := eq_refl.

(*
n9 CONVERSION: the two families are not the same record — the covering
   witnesses differ

--------
n9 转换：这两个家族不是同一记录——覆盖的证人不同
*)
Fail Example p436_sets_same_record (d : Sets) :
  solution_set_of_adjunction (@adj_id Sets) d = Sets_Id_SolutionSet d
  := eq_refl.

(** ** F: guard block / ** F：防守挡拆 *)

Check @solution_set_of_adjunction.
Check @solution_set_of_adjunction_index.
Check @solution_set_of_adjunction_obj.
Check @solution_set_of_adjunction_arr.
Check @universal_arrow_of_adjunction.
Check @comma_initial_of_adjunction.
Check @solution_set_of_adjunction_via_comma.
Check @solution_set_via_comma_index.
Check @solution_set_via_comma_obj.
Check @solution_set_via_comma_arr.
Check @comma_Complete_via_creation.
Check @GAFT_iff.
Check @GAFT_iff_fwd.
Check @GAFT_iff_rev.
Check @GAFT_iff_rev_is_GAFT.
Check @GAFT_iff_at_Sets_Id.
Check @Sets_Id_has_left.
Check @Sets_Id_has_left_is_GAFT_at_Sets_Id.
Check @Sets_Id_SolutionSet_of_adjunction.
Check @Sets_Id_sols_index.
Check @Sets_Id_sols_obj.
Check @Sets_Id_sols_arr.
Check @GAFT.
Check @GAFT_from_initials.
Check @GAFT_via_comma_initial.
Check @comma_initial_of_sols.
Check @sols_of_wif.
Check @SolutionSet.
Check @right_adjoint_PreservesImageLimit.
Check @Sets_Id_SolutionSet.
Check @Sets_Id_PreservesImageLimit.
Check @GAFT_at_Sets_Id.
