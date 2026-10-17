Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.WeaklyInitial.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Discrete.

Set Universe Polymorphism.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(* nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   一般伴随函子定理 (GAFT, Freyd; Mac Lane CWM V.6) 给出函子 [U : C ⟶ D] 有左伴随的
   充分条件。它有两成分，一呈普遍箭头形，一呈解集形：

     - 若每个对象 [d : D] 都有进入 [U] 的*普遍箭头*——此处打包为逗号范畴 [=(d) ↓ U]
       的初始对象——则这些箭头组装成左伴随。这是 [GAFT_from_initials]，直接来自
       [Theory/Universal/Arrow.v]（[AdjunctionFromUniversalArrows]）。

     - Freyd 定理随后从 [C] 的完备性假设、[U] 的极限保持假设，以及每个 [d] 处的*解集*
       *制造*那些初始对象。解集是小族箭头 [d ~> U (sol_obj i)]，每个 [d ~> U c] 经其分解；
       恰是 [=(d) ↓ U] 中的*弱*初始族。逗号完备性（[Construction/Comma/Limit.v]）加上
       从弱初始族到真正初始对象的通路（[Theory/WeaklyInitial.v]）把该弱初始族提升为
       初始对象，喂给 [GAFT_from_initials]。

   变差。[Theory/Universal/Arrow.v] 对其函子 [U0 : D0 ⟶ C0] 陈述普遍箭头伴随并产出
   左伴随 [C0 ⟶ D0]。我们以 [C0 := D]、[D0 := C]、[U0 := U] 实例化，使 [=(c) ↓ U0]
   （[c : C0 = D]）即我们的 [=(d) ↓ U]，诱导左伴随为 [D ⟶ C]，恰如打包
   [{ F : D ⟶ C & F ⊣ U }] 所需。

   假设形式（donor-signature 偏差，诚实记录）。[GAFT] 的操作性保持假设是
   [Construction/Comma/Limit.v] 的 [PreservesImageLimit U]，锥层陈述：[U] 把任意图的
   极限锥带到极限锥（像锥 [(U L, fmap[U] π_•)] 普遍）。这是「U 保持极限」的数学正确读法，
   恰是 [Comma_Complete] 所消耗的。[Structure/Limit/Preservation.v] 的仅顶点类
   [PreservesAllLimits] 只记录顶点对象 [U L] 携带*某个*极限结构，腿不必是像腿；如
   [Construction/Comma/Limit.v] 详述，同顶点上两锥结构可差非可逆自同态，故仅顶点保持
   本身不使像锥普遍。取锥层 [PreservesImageLimit] 因此是加强到正确保持概念——更瘦、诚实的
   假设——从不削弱结论，结论仍是完整左伴随 [F ⊣ U]。这镜像 [Comma_Complete] 自身的
   相同、已文档化选择。 *)

(*
   nLab:  https://ncatlab.org/nlab/show/adjoint+functor+theorem
   Book:  Freyd, "Abelian Categories: An Introduction to the Theory of
   Paper: Kan, "Adjoint Functors", Trans. AMS 87(2), 1958
   Paper: Porst, "The history of the General Adjoint Functor Theorem",

   本节说明伴随、函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Solution sets *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record SolutionSet@{i dobj cobj h}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D) := {
  sol_index : Type@{i};
  sol_obj : sol_index -> C;
  sol_arr : forall i, d ~> U (sol_obj i);
  sol_covers {c} (h : d ~> U c) :
    { i : sol_index & { t : sol_obj i ~> c & fmap[U] t ∘ sol_arr i ≈ h } }
}.

Arguments sol_index {C D U d} _.
Arguments sol_obj {C D U d} _ _.
Arguments sol_arr {C D U d} _ _.
Arguments sol_covers {C D U d} _ {c} _.

(* * ** The universal-arrow half: initial 对象 give 左伴随 （已译） *)

(*
   本节说明伴随、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem GAFT_from_initials {C D : Category} (U : C ⟶ D)
  (H : forall d : D, @Initial (=(d) ↓ U)) : { F : D ⟶ C & F ⊣ U }.
Proof.
  pose (Hu := fun d : D => {| arrow_initial := H d |} : @UniversalArrow D C d U).
  exists (@LeftAdjointFunctorFromUniversalArrows D C U Hu).
  exact (@AdjunctionFromUniversalArrows D C U Hu).
Qed.

(* 相关说明。 （已译） *)

(* Every complete category has all binary equalizers: take the limit of the
   walking parallel pair [APair f g] and read it, at its apex, as an elementary
   equalizer via [equalizer_is_equalizer] of [Structure/Equalizer/Fork.v]. *)
Definition Complete_HasEqualizers {A : Category} (HA : @Complete A) :
  HasEqualizers A.
Proof.
  constructor.
  intros x y f g.
  pose (L := HA Parallel (APair f g)).
  eexists.
  eexists.
  exact (equalizer_is_equalizer f g L).
Defined.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition wif_of_sols@{i cobj dobj h comma +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (S : SolutionSet@{i dobj cobj h} U d)
  : WeaklyInitialFamily@{i comma h} (=(d) ↓ U).
Proof.
  destruct S as [idx obj arr cov].
  unshelve refine (@Build_WeaklyInitialFamily (=(d) ↓ U) idx
                     (fun i => ((ttt, obj i); arr i)) _).
  intro Y.
  destruct Y as [[oY cY] hY].
  destruct (cov cY hY) as [i [t e]].
  exists i.
  unshelve refine ((ttt, t); _).
  change (hY ∘ id[d] ≈ fmap[U] t ∘ arr i).
  rewrite id_right.
  symmetry; exact e.
Defined.

(* 相关说明。 （已译） *)

(*
   本节说明伴随、（余）极限、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem GAFT@{cobj dobj h +} {C : Category@{cobj h h}} {D : Category@{dobj h h}}
  (U : C ⟶ D)
  (comp : @Complete@{h h h cobj} C) (cont : @PreservesImageLimit C D U)
  (sols : forall d : D, SolutionSet@{h dobj cobj h} U d)
  : { F : D ⟶ C & F ⊣ U }.
Proof.
  apply GAFT_from_initials.
  intro d.
  pose (HCat := @Comma_Complete C D U d cont comp).
  pose (W := wif_of_sols U d (sols d)).
  pose (P := HCat _ (DiscreteCat_Functor (wif_obj W))).
  refine (@initial_from_weakly_initial (=(d) ↓ U) W P
            (HCat _ (DiscreteCat_Functor
                       (fun _ : (iprod (wif_obj W) P ~> iprod (wif_obj W) P)
                        => iprod (wif_obj W) P)))
            (Complete_HasEqualizers HCat)).
Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 GAFT 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sols_of_wif@{i cobj dobj h comma +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (W : WeaklyInitialFamily@{i comma h} (=(d) ↓ U))
  : SolutionSet@{i dobj cobj h} U d.
Proof.
  unshelve refine
    {| sol_index := wif_index W
     ; sol_obj := fun i => snd (`1 (wif_obj W i))
     ; sol_arr := fun i => `2 (wif_obj W i) |}.
  intros c h.
  destruct (wif_cover W (((ttt, c); h) : (=(d) ↓ U))) as [i m].
  exists i.
  destruct m as [[u t] sq].
  exists t.
  simpl in sq |- *.
  now rewrite <- sq, id_right.
Defined.

(* 相关说明。 （已译） *)
Example sols_of_wif_index {C D : Category} (U : C ⟶ D) (d : D)
  (W : WeaklyInitialFamily (=(d) ↓ U)) :
  sol_index (sols_of_wif U d W) = wif_index W := eq_refl.

Definition sols_of_comma_initial {C D : Category} (U : C ⟶ D) (d : D)
  (I : @Initial (=(d) ↓ U)) : SolutionSet U d :=
  sols_of_wif U d (weakly_initial_of_initial I).

(* The one member initial comma 对象, nose. （已译） *)
Example sols_of_comma_initial_index {C D : Category} (U : C ⟶ D) (d : D)
  (I : @Initial (=(d) ↓ U)) :
  sol_index (sols_of_comma_initial U d I) = poly_unit := eq_refl.

Example sols_of_comma_initial_obj {C D : Category} (U : C ⟶ D) (d : D)
  (I : @Initial (=(d) ↓ U)) (u : poly_unit) :
  sol_obj (sols_of_comma_initial U d I) u
    = snd (`1 (@initial_obj (=(d) ↓ U) I)) := eq_refl.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition comma_initial_of_sols@{cobj dobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D) (d : D)
  (comp : @Complete@{h h h cobj} C) (cont : @PreservesImageLimit C D U)
  (S : SolutionSet@{h dobj cobj h} U d) : @Initial (=(d) ↓ U).
Proof.
  pose (HCat := @Comma_Complete C D U d cont comp).
  pose (W := wif_of_sols U d S).
  pose (P := HCat _ (DiscreteCat_Functor (wif_obj W))).
  refine (@initial_from_weakly_initial (=(d) ↓ U) W P
            (HCat _ (DiscreteCat_Functor
                       (fun _ : (iprod (wif_obj W) P ~> iprod (wif_obj W) P)
                        => iprod (wif_obj W) P)))
            (Complete_HasEqualizers HCat)).
Defined.

(* GAFT itself, re-derived exported step, agrees 定理
 above statement — two interchangeable at type. （已译） *)
(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition GAFT_via_comma_initial@{cobj dobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} (U : C ⟶ D)
  (comp : @Complete@{h h h cobj} C) (cont : @PreservesImageLimit C D U)
  (sols : ∀ d : D, SolutionSet@{h dobj cobj h} U d) : { F : D ⟶ C & F ⊣ U } :=
  GAFT_from_initials U (fun d => comma_initial_of_sols U d comp cont (sols d)).

(* * ** The converse: 伴随 supplies own solution sets （已译） *)

(*
   本节说明伴随、（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition solution_set_of_adjunction {C D : Category} {F : D ⟶ C} {U : C ⟶ D}
  (A : F ⊣ U) (d : D) : SolutionSet U d.
Proof.
  unshelve refine
    {| sol_index := poly_unit
     ; sol_obj := fun _ => F d
     ; sol_arr := fun _ => @unit _ _ _ _ A d |}.
  intros c h.
  exists ttt.
  exists (@counit _ _ _ _ A c ∘ fmap[F] h).
  rewrite fmap_comp, <- comp_assoc.
  rewrite unit_comp, comp_assoc.
  rewrite fmap_counit_unit.
  apply id_left.
Defined.

(* 相关说明。 （已译） *)

Definition solution_set_of_adjunction_index {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) :
  sol_index (solution_set_of_adjunction A d) = poly_unit := eq_refl.

Definition solution_set_of_adjunction_obj {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) (i : poly_unit) :
  sol_obj (solution_set_of_adjunction A d) i = F d := eq_refl.

Definition solution_set_of_adjunction_arr {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) (i : poly_unit) :
  sol_arr (solution_set_of_adjunction A d) i = @unit _ _ _ _ A d := eq_refl.

(* * ** Mac Lane's own route, through comma-始对象 （已译） *)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition universal_arrow_of_adjunction {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) : UniversalArrow d U.
Proof.
  unshelve refine (universal_arrow_from_UMP d U (F d) (@unit _ _ _ _ A d) _).
  intros c h.
  exists (@counit _ _ _ _ A c ∘ fmap[F] h).
  - rewrite fmap_comp, <- comp_assoc.
    rewrite unit_comp, comp_assoc.
    rewrite fmap_counit_unit.
    symmetry; apply id_left.
  - intros g Hg.
    rewrite Hg, fmap_comp, comp_assoc.
    rewrite counit_comp, <- comp_assoc.
    rewrite counit_fmap_unit.
    apply id_right.
Defined.

Definition comma_initial_of_adjunction {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) : @Initial (=(d) ↓ U) :=
  @arrow_initial _ _ d U (universal_arrow_of_adjunction A d).

Definition solution_set_of_adjunction_via_comma {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) : SolutionSet U d :=
  sols_of_comma_initial U d (comma_initial_of_adjunction A d).

(* The 复合 [universal_arrow_from_UMP → arrow_initial →
 weakly_initial_of_initial → sols_of_wif] reduces all way the
 unit. （已译） *)

Definition solution_set_via_comma_index {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D) :
  sol_index (solution_set_of_adjunction_via_comma A d)
    = sol_index (solution_set_of_adjunction A d) := eq_refl.

Definition solution_set_via_comma_obj {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D)
  (i : sol_index (solution_set_of_adjunction_via_comma A d)) :
  sol_obj (solution_set_of_adjunction_via_comma A d) i = F d := eq_refl.

Definition solution_set_via_comma_arr {C D : Category} {F : D ⟶ C}
  {U : C ⟶ D} (A : F ⊣ U) (d : D)
  (i : sol_index (solution_set_of_adjunction_via_comma A d)) :
  sol_arr (solution_set_of_adjunction_via_comma A d) i
    = @unit _ _ _ _ A d := eq_refl.

(** ** The characterization *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem GAFT_iff {C D : Category} (U : C ⟶ D) (comp : @Complete C) :
  { F : D ⟶ C & F ⊣ U }
    ↔ (@PreservesImageLimit C D U * (∀ d : D, SolutionSet U d)).
Proof.
  split.
  - intros [F A].
    split.
    + exact (right_adjoint_PreservesImageLimit A).
    + exact (solution_set_of_adjunction A).
  - intros [cont sols].
    exact (GAFT U comp cont sols).
Defined.

Definition GAFT_iff_fwd {C D : Category} (U : C ⟶ D) (comp : @Complete C)
  (H : { F : D ⟶ C & F ⊣ U }) :
  @PreservesImageLimit C D U * (∀ d : D, SolutionSet U d) :=
  fst (GAFT_iff U comp) H.

Definition GAFT_iff_rev {C D : Category} (U : C ⟶ D) (comp : @Complete C)
  (H : @PreservesImageLimit C D U * (∀ d : D, SolutionSet U d)) :
  { F : D ⟶ C & F ⊣ U } :=
  snd (GAFT_iff U comp) H.

(* 相关说明。 （已译） *)

Definition GAFT_iff_rev_is_GAFT {C D : Category} (U : C ⟶ D)
  (comp : @Complete C) (cont : @PreservesImageLimit C D U)
  (sols : ∀ d : D, SolutionSet U d) :
  GAFT_iff_rev U comp (cont, sols) = GAFT U comp cont sols := eq_refl.
