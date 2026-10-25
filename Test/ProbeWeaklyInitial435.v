(**
* Probe for Theory/WeaklyInitial.v's characterization (issue #435)

    Pins the measured boundaries of the initial-object theorem's two
    directions with negatives of two kinds, kept lexically apart: TYPING
    (N1: a weakly initial OBJECT is not a weakly initial FAMILY — the two
    notions are related by [wif_of_weakly_initial], not by conversion; N4:
    Freyd's direction does not run without the SECOND product — the
    equalizer supply is not accepted in its place; N5: a family does not
    yield a weakly initial object at a chosen index — [wif_cover] picks its
    own member per target, Riehl's distinction between weakly initial and
    jointly weakly initial) and CONVERSION (N2: the singleton family's index
    is [poly_unit] and nothing else; N3: a [Terminal] is not an [Initial],
    the [C^op] pivot made visible).  The [eq_refl] readbacks are positive
    controls: the family built from an initial object is that object, both
    biconditionals' forward halves ARE [weakly_initial_of_initial], and at
    Sets the DERIVED singleton family's index and member compute.  Every command
    binds its own category, because the pinned [Limit] hypotheses need the
    category's hom level at [Set] and a [Section] variable would fix it
    elsewhere.  Each refutation was stripped one at a time in a copy of the
    whole file; the import list mirrors the target's, plus the Sets
    satellite and Adjunction/GAFT.v for their controls.  A universe
    refutation at [Cat] was tried and does NOT refuse ([Cat]'s hom universe
    instantiates at [Set]); it is not here.

--------
* 探查 Theory/WeaklyInitial.v 的特性（问题 #435）

用两种不同的负号固定初始对象定理的两个方向的测量边界，并在词汇上区分开来：TYPING（N1：弱初始对象不是弱初始族——这两个概念通过 [wif_of_weakly_initial] 关联，而不是通过转换；N4：Freyd 的方向在没有第二个积时无法进行——等化器供给不能替代；N5：一个族在选定的指标下不能产生弱初始对象——[wif_cover] 为每个目标选择其自身成员，Riehl 区分弱初始与联合弱初始）和 CONVERSION（N2：单元素族的指标是 [poly_unit]，别无他物；N3：一个 [Terminal] 不是 [Initial]，[C^op] 枢轴已可见）。
[eq_refl] 回读是阳性控制：从初始对象构建的族就是该对象，两者双条件的前半部分是 [weakly_initial_of_initial]，并且在集合中设置派生单例族的索引和成员计算。每个命令都绑定其自己的类别，因为固定的 [Limit] 假设需要类别在 [Set] 的 hom 级别，并且一个 [Section] 变量会在其他地方固定它。每个反驳在整个文件的副本中一次被剥离；导入列表镜像目标的列表，加上集合卫星和 Adjunction/GAFT.v 用于其控制。在 [Cat] 尝试了一个宇宙反驳，并且没有被拒绝（[Cat] 的 hom 宇宙在 [Set] 实例化）；它不在这里。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Parallel.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.GAFT.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Theory.WeaklyInitial.Sets.

Generalizable All Variables.

(* instrument: the refutation keyword is live / instrument：反驳关键词是 live *)
Fail Check probe435_absent_name.

(** ** A: TYPING — object versus family / ** A：打字——对象与家庭 *)

(* control: a weakly initial object is a type, and a family is built from it / control: a weakly initial object is a type, and a family is built from it / 控制：弱初对象是一种类型，并且一个族是由它构建的 *)
Check (fun (C : Category) (c : C) (w : WeaklyInitial c) =>
         wif_of_weakly_initial w).

(* N1 TYPING: an object is not a family / N1 打字：对象不是一个家族 *)
Fail Check (fun (C : Category) (c : C) (w : WeaklyInitial c) =>
              (w : WeaklyInitialFamily C)).

(** ** B: CONVERSION — the singleton index, and the [C^op] pivot / ** B: 转换 — 单例索引，以及 [C^op] 枢轴 *)

(* control: the index is the polymorphic unit / 控制：指数是多态单元 *)
Example p435_index {C : Category} (I : @Initial C) :
  wif_index (weakly_initial_of_initial I) = poly_unit := eq_refl.

(* N2 CONVERSION: it is not [bool] / N2 转换：它不是 [bool] *)
Fail Example p435_index_bool {C : Category} (I : @Initial C) :
  wif_index (weakly_initial_of_initial I) = bool := eq_refl.

(* control: the direction consumes an [Initial] / 控制：该方向消耗了一个 [Initial] *)
Check (fun (C : Category) (I : @Initial C) => weakly_initial_of_initial I).

(* N3 CONVERSION: a [Terminal] is refused where an [Initial] is expected / N3 转换：在期望 [Initial] 的情况下，[Terminal] 被拒绝 *)
Fail Check (fun (C : Category) (T : @Terminal C) =>
              weakly_initial_of_initial T).

(** ** C: TYPING — the two products, and the index choice / ** C：打字——两个产品，以及指数选择 *)

(* control: with both products and the equalizers, Freyd's direction runs / control: with both products and the equalizers, Freyd's direction runs / 控制：通过产品和均衡器，弗雷德的方向得以运行 *)
Check (fun (C : Category) (W : WeaklyInitialFamily C)
           (P : Limit (DiscreteCat_Functor (wif_obj W)))
           (Pe : Limit (DiscreteCat_Functor
                          (fun _ : iprod (wif_obj W) P ~> iprod (wif_obj W) P
                           => iprod (wif_obj W) P)))
           (E : HasEqualizers C) => initial_from_weakly_initial W P Pe E).

(*
N4 TYPING: the equalizer supply is not accepted in place of the second
   product

--------
N4 打字：均衡器电源不能替代第二个产品
*)
Fail Check (fun (C : Category) (W : WeaklyInitialFamily C)
                (P : Limit (DiscreteCat_Functor (wif_obj W)))
                (E : HasEqualizers C) => initial_from_weakly_initial W P E).

(* control: the family's product is a weakly initial object / 控制：该家族的积是一个弱初对象 *)
Check (fun (C : Category) (W : WeaklyInitialFamily C)
           (P : Limit (DiscreteCat_Functor (wif_obj W))) =>
         weakly_initial_iprod W P).

(*
N5 TYPING: a member at a chosen index is not weakly initial by the cover
   alone — [wif_cover] chooses its own index per target

--------
N5 打字：仅凭覆盖，所选索引处的成员并不是弱初始——[wif_cover] 为每个目标选择自己的索引
*)
Fail Definition p435_member_weakly_initial (C : Category)
  (W : WeaklyInitialFamily C) (i : wif_index W) : WeaklyInitial (wif_obj W i) :=
  fun x => projT2 (wif_cover W x).

(** ** D: readbacks / ** D：复读 *)

Example p435_obj {C : Category} (I : @Initial C) (u : poly_unit) :
  wif_obj (weakly_initial_of_initial I) u = @initial_obj C I := eq_refl.

Example p435_cover {C : Category} (I : @Initial C) (x : C) :
  projT2 (wif_cover (weakly_initial_of_initial I) x) = @zero C I x := eq_refl.

Example p435_iff_fst {C : Category} (Ps : FreydProducts C) (E : HasEqualizers C)
  (I : @Initial C) :
  fst (initial_iff_weakly_initial_family Ps E) I = weakly_initial_of_initial I
  := eq_refl.

Example p435_iff_complete_fst {C : Category} (HC : @Complete C)
  (E : HasEqualizers C) (I : @Initial C) :
  fst (initial_iff_weakly_initial_family_complete HC E) I
    = weakly_initial_of_initial I := eq_refl.

Check (fun (C : Category) (Ps : FreydProducts C) (E : HasEqualizers C) =>
         snd (initial_iff_weakly_initial_family Ps E)
         : WeaklyInitialFamily C → @Initial C).

(* the Sets round trip computes its family / 集合往返计算其族 *)
Example p435_sets_index : wif_index Sets_wif = poly_unit := eq_refl.

Example p435_sets_obj (u : poly_unit) :
  wif_obj Sets_wif u = @initial_obj Sets Sets_Initial := eq_refl.

Check (Sets_roundtrip_iso
         : @initial_obj Sets Sets_initial_recovered
             ≅ @initial_obj Sets Sets_Initial).

(* the separator and the solution-set converse are present / 分隔符和解集的对偶都存在 *)
Check (Parallel_ParX_not_initial : @IsInitialObj Parallel ParX → False).
Check (Parallel_ParY_not_weakly_initial : @WeaklyInitial Parallel ParY → False).
Check (@sols_of_wif).
Check (@sols_of_comma_initial).

(*
the converse's own index readback lives in Adjunction/GAFT.v, whose
   comma notation this file does not import

--------
反函自身的索引回读存在于 Adjunction/GAFT.v 中，而本文件未导入其逗号符号
*)
Check (@sols_of_wif_index).

(** ** Guard block / ** 防守格挡 *)

Check @WeaklyInitial.
Check @WeaklyInitialFamily.
Check @wif_of_weakly_initial.
Check @weakly_initial_of_initial.
Check @weakly_initial_obj_of_initial.
Check @weakly_initial_iprod.
Check @FreydProducts.
Check @initial_iff_weakly_initial_family.
Check @initial_iff_weakly_initial_family_complete.
Check @initial_from_weakly_initial_complete.
Check @initial_from_weakly_initial.
Check @wif_index.
Check @wif_obj.
Check @wif_cover.
Check @IsInitialObj.
Check @Terminal.
Check @initial_obj.
Check @zero.
Check @Limit.
Check @DiscreteCat_Functor.
Check @iprod.
Check @HasEqualizers.
Check @Complete.
Check @Sets_wif.
Check @Sets_initial_characterization.
Check @Sets_initial_recovered.
Check @Sets_roundtrip_iso.
Check @Parallel_ParX_WeaklyInitial.
Check @sols_of_wif.
Check @sols_of_wif_index.
Check @sols_of_comma_initial.
Check @SolutionSet.
Check @sol_index.
Check @poly_unit.
Check bool.
Check @projT2.
