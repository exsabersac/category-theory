Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Displayed.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Instance.StrictCat.ToCat.

Generalizable All Variables.

(** * Fibrations / * 纤维化 *)

(*
nLab:      https://ncatlab.org/nlab/show/Grothendieck+fibration
   nLab:      https://ncatlab.org/nlab/show/cartesian+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Fibred_category
   Reference: Benedikt Ahrens and Peter LeFanu Lumsdaine, “Displayed
              Categories”, Logical Methods in Computer Science 15(1), 2019.
              https://arxiv.org/abs/1705.04296

   Fibrations in both presentations, with the bridge between them.

   Displayed presentation (over the primitive of Theory/Displayed.v): a
   displayed morphism [ff : dhom dx dy f] is cartesian ([DCartesian]) when
   every displayed morphism over a composite [f ∘ g] factors uniquely
   through [ff] by a displayed morphism over [g].  A cleaving ([Cleaving])
   chooses, for every base morphism [f : x ~> y] and displayed object [dy]
   over its codomain, an object [dx] over [x] and a cartesian morphism
   [dx ~> dy] over [f].  No object is ever compared for equality here: the
   fibre placement of the lift is carried by the index [x] itself.

   Functor presentation (the classical one): for [P : E ⟶ C], a morphism
   [φ : e ~> e'] of [E] is cartesian ([CartesianMorphism]) when for every
   [ψ : e'' ~> e'], every explicit base-morphism witness [g : P e'' ~> P e],
   and every equation [fmap[P] ψ ≈ fmap[P] φ ∘ g] exhibiting [fmap[P] ψ] as
   factoring through [fmap[P] φ], there is a unique [χ : e'' ~> e] lying
   over [g] — meaning [fmap[P] χ ≈ g] — with [φ ∘ χ ≈ ψ].  Because homs in
   this library are setoids, the classical equations [P ψ = P φ ∘ g] and
   [P χ = g] are stated with [≈]; carrying the witness [g] and the
   factorization equation explicitly is the ≈-honest reading of the
   universal property (the displayed side realises the same reading with
   [dtransport] doing the carrying).

   A cloven fibration ([ClovenFibration]) equips [P] with a chosen
   cartesian lift ([CartesianLift]) of every [f : x ~> P e'].  Here — and
   only here — the fibre placement is strict: the chosen [lift_obj]
   satisfies a propositional object equality [P lift_obj = x], consumed
   through the induced isomorphism [iso_of_eq] of
   Instance/StrictCat/ToCat.v.  Plain [=] on objects is deliberate and
   sanctioned at this single interface: it anchors each chosen lift in an
   honest fibre over [x], which is what the split theory below and the
   round trip with indexed categories
   (Construction/Grothendieck/RoundTrip.v) consume.  A cleavage is split
   ([SplitCleaving]) when the chosen lifts are functorial on the nose: the
   lift of an identity is an identity and the lift of a composite is the
   composite of the lifts, both stated across the strict anchoring's
   transports.

   Bridge: a [Cleaving] on a displayed category [D] makes the projection
   [Total_Proj D : Total D ⟶ C] a cloven fibration
   ([cleaving_total_cloven]); the anchoring is [eq_refl], because the lift
   object is literally the pair [(x; dx)] whose first component is [x].

   Opfibrations arise by duality: [Displayed_op] re-reads a displayed
   category over [C] as one over [C^op] — a displayed morphism from [dx]
   to [dy] over [f : x ~{C^op}~> y] is a displayed morphism from [dy] to
   [dx] over the underlying arrow of [C] — and an opcleaving of [D] is a
   cleaving of the op-displayed category ([OpCleaving]).

--------
nLab:      https://ncatlab.org/nlab/show/Grothendieck+fibration
   nLab:      https://ncatlab.org/nlab/show/cartesian+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Fibred_category
   Reference: Benedikt Ahrens and Peter LeFanu Lumsdaine, “Displayed
              Categories”, Logical Methods in Computer Science 15(1), 2019.
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
   的展示态射——[D] 的余劈开是 op-展示范畴的劈开（[OpCleaving]）。
*)

(** ** Cartesian morphisms and cleavings, displayed presentation / ** 笛卡尔态射与剖分，显示表示 *)

(*
[ff] is cartesian over its base morphism [f] when every displayed
   morphism over a composite [f ∘ g] factors through [ff] by a unique
   displayed morphism over [g].

--------
当每个复合 [f ∘ g] 上的显示态态射通过 [g] 上的唯一显示态射分解为 [ff] 上的态射时，[ff] 在其基态射 [f] 上是笛卡尔的。
*)
Class DCartesian {C : Category} {D : Displayed C} {x y : C} {f : x ~> y}
      {dx : dobj x} {dy : dobj y} (ff : dhom dx dy f) := {
  dcart_factor {z : C} {g : z ~> x} {dz : dobj z}
    (hh : dhom dz dy (f ∘ g)) :
    ∃! gg : dhom dz dx g, dcomp ff gg ≈ hh
}.

(*
A cleaving: chosen cartesian lifts.  Given [f : x ~> y] and [dy] over
   the codomain, it selects an object over [x] together with a cartesian
   morphism over [f] into [dy].

--------
切分：选定的笛卡尔提升。给定位于陪域上的 [f : x ~> y] 和 [dy]，它会选择一个位于 [x] 上的对象，以及一个位于 [f] 上指向 [dy] 的笛卡尔态射。
*)
Class Cleaving {C : Category} (D : Displayed C) := {
  clift {x y : C} (f : x ~> y) (dy : dobj y) :
    { dx : dobj x & { ff : dhom dx dy f & DCartesian ff } }
}.

(** ** Cartesian morphisms and cloven fibrations, functor presentation / ** 笛卡尔态射与分裂纤维化，函子表示 *)

(*
The ≈-honest universal property: the factorization of [fmap[P] ψ]
   through [fmap[P] φ] is carried by an explicit base-morphism witness [g]
   and an explicit equation, and the mediating lift is unique among
   morphisms lying over [g] up to [≈].

--------
≈-诚实的普适性质：[fmap[P] ψ] 通过 [fmap[P] φ] 的分解由一个显式的基态态射见证 [g] 和一个显式方程承载，并且中介提升在位于 [g] 上的态射中是唯一的，直至 [≈]。
*)
Class CartesianMorphism {C E : Category} (P : E ⟶ C)
      {e e' : E} (φ : e ~> e') := {
  cart_factor {e'' : E} (ψ : e'' ~> e') (g : P e'' ~> P e)
    (factors : fmap[P] ψ ≈ fmap[P] φ ∘ g) :
    ∃! χ : e'' ~> e, (φ ∘ χ ≈ ψ) ∧ (fmap[P] χ ≈ g)
}.

(*
A chosen cartesian lift of [f : x ~> P e'].  The lift object is
   anchored in the fibre over [x] STRICTLY, by a propositional object
   equality [P lift_obj = x] (sanctioned here; see the header), and the
   lift lies over [f] up to the isomorphism induced by that equality.

--------
[f : x ~> P e'] 的一个选定笛卡尔提升。该提升对象严格地固定在 [x] 上的纤维中，通过一个命题对象等式 [P lift_obj = x]（此处批准；见标题），并且该提升位于 [f] 之上，直至由该等式引起的同构。
*)
Record CartesianLift {C E : Category} (P : E ⟶ C) {x : C} {e' : E}
       (f : x ~> P e') := {
  lift_obj : E;
  lift_anchor : P lift_obj = x;         (* strict fibre anchoring / 严格的纤维锚固 *)
  lift_mor : lift_obj ~> e';
  lift_cartesian : CartesianMorphism P lift_mor;
  lift_over : fmap[P] lift_mor ≈ f ∘ to (iso_of_eq lift_anchor)
}.

Arguments lift_obj {C E P x e' f} _.
Arguments lift_anchor {C E P x e' f} _.
Arguments lift_mor {C E P x e' f} _.
Arguments lift_cartesian {C E P x e' f} _.
Arguments lift_over {C E P x e' f} _.

(* A cloven fibration: a chosen cartesian lift for every [f : x ~> P e']. / 一个分裂纤维化：为每个 [f : x ~> P e'] 选择的笛卡尔提升。 *)
Class ClovenFibration {C E : Category} (P : E ⟶ C) := {
  cloven_lift {x : C} {e' : E} (f : x ~> P e') : CartesianLift P f
}.

(*
A split cleavage: the chosen lifts are functorial on the nose.  Both
   laws live across the strict anchoring's transports, via [iso_of_eq]:

   - the lift of [id[P e']] has lift object equal to [e'] itself, and its
     lift morphism is the corresponding transport isomorphism (an identity
     seen across the object equality [q]);

   - the composite [f ∘ g] is lifted, up to the object equality [q] of the
     two chosen lift objects, by the composite of the lift of [f] with the
     lift of [g] — where [g : y ~> x] is first carried into the fibre over
     [x] along the anchoring of the lift of [f], so that it can be lifted
     with codomain [lift_obj (cloven_lift f)].

--------
一个分裂支解：所选择的提升在字面上是函子性的。两个定律跨越严格锚定的传输，通过 [iso_of_eq] 存在：

- [id[P e'] 的提升对象等于 [e'] 本身，它的提升态射是相应的传输同构（在对象等式 [q] 下看作恒等式）；

- 复合 [f ∘ g] 被提升，直到两个所选择提升对象的对象等式 [q]，通过 [f] 的提升与 [g] 的提升的复合——其中 [g : y ~> x] 首先沿着 [f] 的提升的锚定被带入 [x] 对应的纤维，从而可以被提升到余域 [lift_obj (cloven_lift f)]。
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

(** ** Bridge: a cleaving makes the total projection a cloven fibration / ** 桥：一次劈开使总投影成为分裂纤维丛 *)

(*
A displayed-cartesian morphism is cartesian for the projection functor:
   the base factorization is transported into a displayed morphism over
   the composite, which then factors uniquely through [ff].

--------
一个显示的笛卡尔态射对于投影函子是笛卡尔的：基分解被传送为复合上的显示态射，然后唯一地通过 [ff] 分解。
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
    + (* the mediating lift commutes: φ ∘ (g; gg) ≈ ψ / 中介提升可交换：φ ∘ (g; gg) ≈ ψ *)
      exists (symmetry Hbase); simpl.
      rewrite Hcomm.
      apply dtransport_symm_l.
    + (* and it lies over g / 它躺在 g 上 *)
      simpl.
      reflexivity.
  - (* uniqueness among lifts over g / 在 g 上方电梯中的独特性 *)
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
The bridge: chosen displayed lifts become chosen functor-level lifts of
   the projection.  The lift of [f : x ~> `1 e'] at [e'] is the pair
   [(x; dx)] over the cleaving's chosen [dx], so the strict anchoring is
   [eq_refl] and its transport isomorphism is an identity.

--------
桥：所选择显示的提升成为投影的所选择函子级提升。在 [e'] 处的 [f : x ~> `1 e'] 的提升是 [(x; dx)] 与分裂的所选择 [dx] 之上的对，因此严格锚定是 [eq_refl]，其传输同构是恒等的。
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
  (*
the chosen lift lies over f: the anchoring is [eq_refl], whose
     induced isomorphism is an identity

--------
所选择的提升位于 f 上：锚定是 [eq_refl]，其诱导的同构是恒等映射
*)
  now rewrite id_right.
Qed.

(** ** Opfibrations, by duality / ** 纤维上范畴，通过对偶性 *)

#[local] Obligation Tactic := idtac.

(*
The op-displayed category: same displayed objects; a displayed morphism
   from [dx] to [dy] over [f : x ~{C^op}~> y] is a displayed morphism from
   [dy] to [dx] over the underlying arrow [f : y ~{C}~> x].  Transport is
   unchanged (an op-hom setoid IS the underlying hom setoid), and displayed
   composition flips its arguments, mirroring [Construction/Opposite.v].

--------
对偶显示的范畴：相同的显示对象；从 [dx] 到 [dy] 在 [f : x ~{C^op}~> y] 上的显示态射是一个从 [dy] 到 [dx] 在基础箭头 [f : y ~{C}~> x] 上的显示态射。运输保持不变（一个对偶同态集合是基础同态集合），而显示复合会翻转其参数，反映 [Construction/Opposite.v]。
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
(*
[dtransport_respects] is resolved during elaboration by the registered
   instance of the underlying displayed category, so it generates no
   obligation; the remaining laws follow in field order.

--------
[dtransport_respects] 在展开过程中由底层显示范畴的注册实例解析，因此不会产生任何义务；其余的规则按照字段顺序执行。
*)
Next Obligation. (* dtransport_id / 运输编号 *)
  intros C D x y dx dy f e ff.
  exact (@dtransport_id C D y x dy dx f e ff).
Qed.
Next Obligation. (* dtransport_trans: any proof of the endpoints works / dtransport_trans：任何端点的证明都有效 *)
  intros C D x y dx dy f g h e1 e2 ff; simpl.
  apply dtransport_trans_any.
Qed.
Next Obligation. (* dcomp_respects: the underlying respectfulness, flipped / dcomp_respects：底层的尊重性，翻转 *)
  intros C D x y z dx dy dz f g ff ff' Hff gg gg' Hgg.
  exact (@dcomp_respects C D z y x dz dy dx g f gg gg' Hgg ff ff' Hff).
Qed.
Next Obligation. (* dtransport_comp_l is the underlying dtransport_comp_r / dtransport_comp_l 是底层的 dtransport_comp_r *)
  intros C D x y z dx dy dz f f' g e e' ff gg.
  exact (@dtransport_comp_r C D z y x dz dy dx g f f' e e' gg ff).
Qed.
Next Obligation. (* dtransport_comp_r is the underlying dtransport_comp_l / dtransport_comp_r 是底层的 dtransport_comp_l *)
  intros C D x y z dx dy dz f g g' e e' ff gg.
  exact (@dtransport_comp_l C D z y x dz dy dx g g' f e e' gg ff).
Qed.
Next Obligation. (* did_left is the underlying did_right / did_left 是底层的 did_right *)
  intros C D x y dx dy f ff.
  exact (@did_right C D y x dy dx f ff).
Qed.
Next Obligation. (* did_right is the underlying did_left / did_right 是底层的 did_left *)
  intros C D x y dx dy f ff.
  exact (@did_left C D y x dy dx f ff).
Qed.
Next Obligation. (* dcomp_assoc: the underlying associator, reoriented / dcomp_assoc：底层的结合子，重新定向 *)
  intros C D w x y z dw dx dy dz f g h ff gg hh; simpl.
  symmetry.
  apply dtransport_dcomp_assoc.
Qed.

(*
An opcleaving of [D] — chosen opcartesian lifts, pushing displayed
   objects forward along base morphisms — is a cleaving of the
   op-displayed category.

--------
[D] 的对劈分 —— 选择的对笛卡尔提升，将显示对象沿基态态射推动 —— 是对显示范畴的劈分。
*)
Definition OpCleaving {C : Category} (D : Displayed C) : Type :=
  Cleaving (Displayed_op D).
