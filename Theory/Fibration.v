Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Displayed.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Instance.StrictCat.ToCat.

Generalizable All Variables.

(** * Fibrations *)

(* nLab:      https://ncatlab.org/nlab/show/Grothendieck+fibration
   nLab:      https://ncatlab.org/nlab/show/cartesian+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Fibred_category
   Reference: Benedikt Ahrens and Peter LeFanu Lumsdaine, "Displayed
              Categories", Logical Methods in Computer Science 15(1), 2019.
              https://arxiv.org/abs/1705.04296

   两种呈现下的纤维化，以及其间的桥。

   展示呈现（基于 Theory/Displayed.v 的原语）：展示态射 [ff : dhom dx dy f] 是笛卡尔的
   （[DCartesian]），当每个在复合 [f ∘ g] 上的展示态射都经 [ff] 由在 [g] 上的展示态射
   唯一分解。劈开 (cleaving)（[Cleaving]）对每个基态射 [f : x ~> y] 及其陪域上的展示
   对象 [dy]，选定 [x] 上的对象 [dx] 与在 [f] 上的笛卡尔态射 [dx ~> dy]。此处从不比较
   对象相等：提升的纤维位置由指标 [x] 本身携带。

   函子呈现（经典）：对 [P : E ⟶ C]，[E] 的态射 [φ : e ~> e'] 是笛卡尔的
   （[CartesianMorphism]），当对每个 [ψ : e'' ~> e']、每个显式基态射见证
   [g : P e'' ~> P e]、以及每个方程 [fmap[P] ψ ≈ fmap[P] φ ∘ g]（展示 [fmap[P] ψ]
   经 [fmap[P] φ] 分解），存在唯一 [χ : e'' ~> e] 落在 [g] 上——即 [fmap[P] χ ≈ g]——
   且 [φ ∘ χ ≈ ψ]。因本库 hom 是 setoid，经典方程 [P ψ = P φ ∘ g] 与 [P χ = g] 用 [≈]
   陈述；显式携带见证 [g] 与分解方程是普遍性质的 ≈-诚实读法（展示侧用 [dtransport]
   做携带，实现同一读法）。

   劈开纤维化 ([ClovenFibration]) 给 [P] 配备每个 [f : x ~> P e'] 的选定笛卡尔提升
   （[CartesianLift]）。此处——且仅此处——纤维位置是严格的：选定的 [lift_obj] 满足
   命题对象相等 [P lift_obj = x]，经 Instance/StrictCat/ToCat.v 的诱导同构 [iso_of_eq]
   消耗。对象上的普通 [=] 是刻意的，并在此单一接口获准：它把每个选定提升锚定在 [x]
   上的诚实纤维，供下文分裂理论与指标范畴往返（Construction/Grothendieck/RoundTrip.v）
   消耗。劈开是分裂的（[SplitCleaving]）当选定提升在表面上函子性：恒等的提升是恒等，
   复合的提升是提升的复合，均跨严格锚定的 transport 陈述。

   桥：展示范畴 [D] 上的 [Cleaving] 使投影 [Total_Proj D : Total D ⟶ C] 成为劈开纤维化
   （[cleaving_total_cloven]）；锚定是 [eq_refl]，因提升对象字面上是第一分量为 [x]
   的对 [(x; dx)]。

   余纤维化由对偶产生：[Displayed_op] 把 [C] 上的展示范畴重读为 [C^op] 上的——
   在 [f : x ~{C^op}~> y] 上从 [dx] 到 [dy] 的展示态射是在 [C] 底层箭头上从 [dy] 到 [dx]
   的展示态射——[D] 的余劈开是 op-展示范畴的劈开（[OpCleaving]）。 *)

(* * ** Cartesian 态射 cleavings, displayed presentation （已译） *)

(* [ff] is cartesian over its base morphism [f] when every displayed
   morphism over a composite [f ∘ g] factors through [ff] by a unique
   displayed morphism over [g]. *)
Class DCartesian {C : Category} {D : Displayed C} {x y : C} {f : x ~> y}
      {dx : dobj x} {dy : dobj y} (ff : dhom dx dy f) := {
  dcart_factor {z : C} {g : z ~> x} {dz : dobj z}
    (hh : dhom dz dy (f ∘ g)) :
    ∃! gg : dhom dz dx g, dcomp ff gg ≈ hh
}.

(* A cleaving: chosen cartesian lifts. Given [f : x ~> y] [dy] over
 codomain, it selects 对象 over [x] together cartesian
 态射 over [f] [dy]. （已译） *)
Class Cleaving {C : Category} (D : Displayed C) := {
  clift {x y : C} (f : x ~> y) (dy : dobj y) :
    { dx : dobj x & { ff : dhom dx dy f & DCartesian ff } }
}.

(* * ** Cartesian 态射 cloven fibrations, 函子 presentation （已译） *)

(*
   本节说明 Fibration 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class CartesianMorphism {C E : Category} (P : E ⟶ C)
      {e e' : E} (φ : e ~> e') := {
  cart_factor {e'' : E} (ψ : e'' ~> e') (g : P e'' ~> P e)
    (factors : fmap[P] ψ ≈ fmap[P] φ ∘ g) :
    ∃! χ : e'' ~> e, (φ ∘ χ ≈ ψ) ∧ (fmap[P] χ ≈ g)
}.

(*
   本节说明同构、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record CartesianLift {C E : Category} (P : E ⟶ C) {x : C} {e' : E}
       (f : x ~> P e') := {
  lift_obj : E;
  lift_anchor : P lift_obj = x;         (* strict fibre anchoring *)
  lift_mor : lift_obj ~> e';
  lift_cartesian : CartesianMorphism P lift_mor;
  lift_over : fmap[P] lift_mor ≈ f ∘ to (iso_of_eq lift_anchor)
}.

Arguments lift_obj {C E P x e' f} _.
Arguments lift_anchor {C E P x e' f} _.
Arguments lift_mor {C E P x e' f} _.
Arguments lift_cartesian {C E P x e' f} _.
Arguments lift_over {C E P x e' f} _.

(* A cloven fibration: a chosen cartesian lift for every [f : x ~> P e']. *)
Class ClovenFibration {C E : Category} (P : E ⟶ C) := {
  cloven_lift {x : C} {e' : E} (f : x ~> P e') : CartesianLift P f
}.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class SplitCleaving {C E : Category} (P : E ⟶ C)
      `{H : @ClovenFibration C E P} := {
  split_lift_id {e' : E} :
    { q : lift_obj (cloven_lift (id[P e'])) = e'
    & lift_mor (cloven_lift (id[P e'])) ≈ to (iso_of_eq q) };

  split_lift_comp {x y : C} {e' : E} (f : x ~> P e') (g : y ~> x) :
    { q : lift_obj (cloven_lift (f ∘ g))
        = lift_obj (cloven_lift
            (from (iso_of_eq (lift_anchor (cloven_lift f))) ∘ g))
    & lift_mor (cloven_lift (f ∘ g))
        ≈ lift_mor (cloven_lift f)
            ∘ lift_mor (cloven_lift
                (from (iso_of_eq (lift_anchor (cloven_lift f))) ∘ g))
            ∘ to (iso_of_eq q) }
}.

(* 相关说明。 （已译） *)

(*
   本节说明函子、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma total_cartesian {C : Category} {D : Displayed C}
  {t t' : Total D} (φ : t ~> t') (Hφ : DCartesian (`2 φ)) :
  CartesianMorphism (Total_Proj D) φ.
Proof.
  constructor; intros e'' ψ g Hbase; simpl in *.
  destruct (@dcart_factor _ _ _ _ _ _ _ _ Hφ _ g _
              (dtransport Hbase (`2 ψ))) as [gg Hcomm Huniq].
  unshelve refine {| unique_obj := ((g; gg) : e'' ~{ Total D }~> t) |}.
  - split.
    + (* the mediating lift commutes: φ ∘ (g; gg) ≈ ψ *)
      exists (symmetry Hbase); simpl.
      rewrite Hcomm.
      apply dtransport_symm_l.
    + (* and it lies over g *)
      simpl.
      reflexivity.
  - (* uniqueness among lifts over g *)
    intros [v vv] [[e1 He1] Hv2]; simpl in *.
    exists (symmetry Hv2).
    assert (Hu : gg ≈ dtransport Hv2 vv).
    { apply Huniq.
      rewrite (dtransport_comp_r Hv2
                 (compose_respects _ _ (Equivalence_Reflexive _) _ _ Hv2)
                 (`2 φ) vv).
      apply (fst (dtransport_flip _ _ _)) in He1.
      rewrite He1.
      apply dtransport_trans_any. }
    rewrite Hu.
    apply dtransport_symm_l.
Defined.

#[local] Obligation Tactic := program_simpl.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition cleaving_total_cloven {C : Category} {D : Displayed C}
        `{H : @Cleaving C D} : ClovenFibration (Total_Proj D) := {|
  cloven_lift := fun x e' f =>
    {| lift_obj := (x; `1 (clift f (`2 e')));
       lift_anchor := eq_refl;
       lift_mor := (f; `1 (`2 (clift f (`2 e'))));
       lift_cartesian := @total_cartesian C D (x; `1 (clift f (`2 e'))) e'
                           (f; `1 (`2 (clift f (`2 e'))))
                           (`2 (`2 (clift f (`2 e')))) |}
|}.
Next Obligation.
  (* the chosen lift lies over f: anchoring [eq_refl], whose
 induced 同构 恒等 （已译） *)
  now rewrite id_right.
Qed.

(** ** Opfibrations, by duality *)

#[local] Obligation Tactic := idtac.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Displayed_op {C : Category} (D : Displayed C) :
  Displayed (C^op) := {|
  dobj := @dobj C D;
  dhom := fun x y dx dy f => @dhom C D y x dy dx f;
  dhomset := fun x y dx dy f => @dhomset C D y x dy dx f;
  dtransport := fun x y dx dy f g e => @dtransport C D y x dy dx f g e;
  did := fun x dx => @did C D x dx;
  dcomp := fun x y z dx dy dz f g ff gg => @dcomp C D z y x dz dy dx g f gg ff
|}.
(* [dtransport_respects] is resolved during elaboration registered
 实例 underlying displayed 范畴, so it generates no
 obligation; remaining laws follow field order.（已译） *)
Next Obligation. (* dtransport_id *)
  intros C D x y dx dy f e ff.
  exact (@dtransport_id C D y x dy dx f e ff).
Qed.
Next Obligation. (* dtransport_trans: any 证明 endpoints works （已译） *)
  intros C D x y dx dy f g h e1 e2 ff; simpl.
  apply dtransport_trans_any.
Qed.
Next Obligation. (* dcomp_respects: the underlying respectfulness, flipped *)
  intros C D x y z dx dy dz f g ff ff' Hff gg gg' Hgg.
  exact (@dcomp_respects C D z y x dz dy dx g f gg gg' Hgg ff ff' Hff).
Qed.
Next Obligation. (* dtransport_comp_l is the underlying dtransport_comp_r *)
  intros C D x y z dx dy dz f f' g e e' ff gg.
  exact (@dtransport_comp_r C D z y x dz dy dx g f f' e e' gg ff).
Qed.
Next Obligation. (* dtransport_comp_r is the underlying dtransport_comp_l *)
  intros C D x y z dx dy dz f g g' e e' ff gg.
  exact (@dtransport_comp_l C D z y x dz dy dx g g' f e e' gg ff).
Qed.
Next Obligation. (* did_left is the underlying did_right *)
  intros C D x y dx dy f ff.
  exact (@did_right C D y x dy dx f ff).
Qed.
Next Obligation. (* did_right is the underlying did_left *)
  intros C D x y dx dy f ff.
  exact (@did_left C D y x dy dx f ff).
Qed.
Next Obligation. (* dcomp_assoc: the underlying associator, reoriented *)
  intros C D w x y z dw dx dy dz f g h ff gg hh; simpl.
  symmetry.
  apply dtransport_dcomp_assoc.
Qed.

(* An opcleaving of [D] — chosen opcartesian lifts, pushing displayed
   objects forward along base morphisms — is a cleaving of the
   op-displayed category. *)
Definition OpCleaving {C : Category} (D : Displayed C) : Type :=
  Cleaving (Displayed_op D).
