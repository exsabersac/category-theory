Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Displayed.
Require Import Category.Theory.Fibration.
Require Import Category.Structure.Pullback.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(* * * The codomain displayed category / * * 显示的陪域类别 *)

(*
 nLab:      https://ncatlab.org/nlab/show/codomain+fibration
 nLab:      https://ncatlab.org/nlab/show/displayed+category
 Wikipedia: https://en.wikipedia.org/wiki/Fibred_category

 The codomain displayed category of [C] displays over each object [x : C]
 the maps INTO [x]: an object over [x] is a pair [(d; p)] of an object
 [d : C] and a morphism [p : d ~> x].  A displayed morphism from [(d; p)]
 over [x] to [(d'; p')] over [y], lying over a base morphism [f : x ~> y],
 is a morphism [u : d ~> d'] making the square

 d  --u-->  d'
 |          |
 p|          | p'        commute, i.e.  p' ∘ u ≈ f ∘ p,
 v          v
 x  --f-->  y

 and two displayed morphisms over [f] are equivalent when their underlying
 morphisms [u] are ≈ — the square proof is irrelevant.  Transport along a
 base proof [e : f ≈ g] leaves the morphism [u] untouched and merely
 rewrites the square along [e], so the transport laws ([dtransport_id],
 [dtransport_trans], and the interchange fields) are reflexivity-shaped.

 Fibres and total category.  The fibre of this displayed category over [x]
 has as objects the maps into [x] — the encoding [∃ d, d ~> x] is
 literally the object encoding of the slice category of
 Construction/Slice.v — and as morphisms over [id[x]] the commuting
 triangles over [x], which are the slice's morphisms.  The total category
 (Construction/Displayed/Total.v) has as objects ALL maps of [C] and as
 morphisms all commuting squares: it is the displayed rendering of the
 arrow category.  The comparison with the comma presentation
 [C ⃗ = (Id[C] ↓ Id[C])] of Construction/Arrow.v is delivered below as the
 mutually inverse functors [Codomain_Total_to_Arrow] and
 [Arrow_to_Codomain_Total], packaged as an isomorphism
 [Codomain_Total_Arrow_iso] in Cat.

 The payoff is the classical characterization of the codomain FIBRATION:
 the codomain displayed category has a cleaving exactly when [C] has all
 pullbacks.  [codomain_cleaving] builds the cartesian lift of [f : x ~> y]
 at [(d; p)] from the chosen pullback of [p] along [f], and
 [codomain_cleaving_pullbacks] conversely reads the pullback of a cospan
 [f : x ~> z], [g : y ~> z] off the cartesian lift of [f] at [(y; g)]; in
 both directions the universal properties are exchanged by turning a
 competing pullback cone into a displayed morphism over a composite. 

 --------
 nLab:       https://ncatlab.org/nlab/show/codomain+fibration 
 nLab:       https://ncatlab.org/nlab/show/displayed+category 
 Wikipedia:  https://en.wikipedia.org/wiki/Fibred_category 

 [C] 的余域显示范畴在每个对象 [x : C] 上显示映射到 [x] ：一个位于 [x] 上的对象是一个由对象 [d : C] 和态射 [p : d ~> x] 组成的对 [(d; p)] 。

 从 [(d; p)] 到 [(d'; p')] 的显示态射位于 [x] 上到 [y] 上，位于基态射 [f : x ~> y] 上，是一个态射 [u : d ~> d'] ，使得方形

 d  --u-->  d'
 |          |
 p|          | p'        可交换，即 p' ∘ u ≈ f ∘ p,
 v          v
 x  --f-->  y当它们的基础态射 [u] ≈ 时，两个在 [f] 上显示的态射是等价的——平方证明是无关的。沿着基础证明 [e : f ≈ g] 的传输不会改变态射 [u]，只是沿着 [e] 重写平方，因此传输定律（[dtransport_id]、[dtransport_trans] 以及交换域）呈现自反形。纤维和总体范畴。这个显示范畴在 [x] 上的纤维的对象是映射到 [x] 的映射——编码 [∃ d, d ~> x] 字面上是 Construction/Slice.v 的切片范畴的对象编码——在 [id[x] 上的态射是 [x] 上的交换三角形，它们是切片的态射。总体范畴 (Construction/Displayed/Total.v) 的对象是 [C] 的所有映射，态射是所有交换方形：它是箭头范畴的显示表示。与 Construction/Arrow.v 的逗号表示 [C ⃗ = (Id[C] ↓ Id [C] 的比较如下，通过互为逆的函子 [Codomain_Total_to_Arrow] 和 [Arrow_to_Codomain_Total] 提供，并封装为 Cat 中的一个同构 [Codomain_Total_Arrow_iso]。这个结果是对余域纤维(FIBRATION)的经典描述：
 当 [C] 具有所有的拉回时，余域显示范畴恰好有一个分解(cleving)。[codomain_cleaving] 构建 [f : x ~> y] 在 [(d; p)] 的笛卡尔提升(cartesian lift)，由沿 [f] 选择的 [p] 的拉回得到；[codomain_cleaving_pullbacks] 反过来从 [(y; g)] 处 [f] 的笛卡尔提升中读出 [f : x ~> z]、[g : y ~> z] 的余箭(cospan)的拉回；在两个方向中，通过将竞争的拉回锥转化为复合上的显示态射(displayed morphism)，普遍性质被互换。
*)

#[local] Obligation Tactic := idtac.

Program Definition Codomain_Displayed (C : Category) : Displayed C := {|
  dobj := fun x => ∃ d : C, d ~> x;
  dhom := fun x y dx dy f => ∃ u : `1 dx ~> `1 dy, `2 dy ∘ u ≈ f ∘ `2 dx;
  dhomset := fun x y dx dy f => {| equiv := fun u v => `1 u ≈ `1 v |};
  dtransport := fun x y dx dy f g e ff => (`1 ff; _);
  did := fun x dx => (id; _);
  dcomp := fun x y z dx dy dz f g ff gg => (`1 ff ∘ `1 gg; _)
|}.
Next Obligation.
  (* the displayed hom-setoid compares underlying morphisms / 显示的同构集合比较基础态射 *)
  intros C x y dx dy f.
  equivalence.
Qed.
Next Obligation.
  (* transport keeps the morphism and rewrites its square along e / 传递保持同态并沿着 e 重写其平方 *)
  intros C x y dx dy f g e ff; simpl.
  rewrite (`2 ff).
  now rewrite e.
Qed.
Next Obligation.
  (*
 dtransport_respects: transport is the identity on the morphism 

 --------
 dtransport_respects: 传输在态射上是恒等映射
*)
  intros C x y dx dy f g e; repeat intro; simpl in *.
  assumption.
Qed.
Next Obligation.
  (*
 dtransport_id: transport along a loop is the identity 

 --------
 dtransport_id: 沿着环上的平移是恒等映射
*)
  intros C x y dx dy f e ff; simpl.
  reflexivity.
Qed.
Next Obligation.
  (*
 dtransport_trans: two transports fuse, on the nose 

 --------
 dtransport_trans：两个运输工具融合，正面
*)
  intros C x y dx dy f g h e1 e2 ff; simpl.
  reflexivity.
Qed.
Next Obligation.
  (* the identity square over id / 恒等映射上的方块 *)
  intros C x dx; simpl.
  rewrite id_left, id_right.
  reflexivity.
Qed.
Next Obligation.
  (* squares over f and g paste to a square over f ∘ g / f 和 g 上的平方粘贴到 f ∘ g 上的平方 *)
  intros C x y z dx dy dz f g ff gg; simpl.
  rewrite comp_assoc.
  rewrite (`2 ff).
  rewrite <- (comp_assoc f (`2 dy) (`1 gg)).
  rewrite (`2 gg).
  apply comp_assoc.
Qed.
Next Obligation.
  (*
 dcomp_respects: composition of underlying morphisms respects ≈ 

 --------
 dcomp_respects: 底层态射的复合尊重 ≈
*)
  intros C x y z dx dy dz f g ff ff' Hff gg gg' Hgg; simpl in *.
  now rewrite Hff, Hgg.
Qed.
Next Obligation.
  (*
 dtransport_comp_l: transport is invisible to the morphism data 

 --------
 dtransport_comp_l: 传输对态射数据是不可见的
*)
  intros C x y z dx dy dz f f' g e e' ff gg; simpl.
  reflexivity.
Qed.
Next Obligation.
  (* dtransport_comp_r: likewise on the right / dtransport_comp_r：右边同样 *)
  intros C x y z dx dy dz f g g' e e' ff gg; simpl.
  reflexivity.
Qed.
Next Obligation.
  (* did_left: the base law on underlying morphisms / did_left：基础形态映射的基本法则 *)
  intros C x y dx dy f ff; simpl.
  apply id_left.
Qed.
Next Obligation.
  (* did_right / 做对了 *)
  intros C x y dx dy f ff; simpl.
  apply id_right.
Qed.
Next Obligation.
  (* dcomp_assoc / dcomp_结合 *)
  intros C w x y z dw dx dy dz f g h ff gg hh; simpl.
  apply comp_assoc.
Qed.

(* * ** Cartesian lifts from pullbacks / * ** 从拉回中得到的笛卡尔提升 *)

(*
 The cartesian lift of [f : x ~> y] at [(d; p)] is the chosen pullback of
 [p] along [f]:

 x ×_y d --snd--> d
 |             |
 fst|             | p
 v             v
 x  ----f----> y

 The pullback apex with its first projection is the lift object over [x],
 and the second projection is the lift morphism over [f]; its square is
 the pullback square read backwards.  Cartesianness is exactly the
 pullback's universal property: a displayed morphism over [f ∘ g] from
 [(e; q)] is a morphism [h] with [p ∘ h ≈ (f ∘ g) ∘ q], i.e. a competing
 cone [(g ∘ q, h)] over the cospan, and the mediating morphism into the
 apex is the unique displayed factorization over [g]. 

 --------
 [f : x ~> y] 在 [(d; p)] 处的笛卡尔提升是沿着 [f] 选择的 [p] 的拉回：

 x ×_y d --snd--> d
 |             |
 fst|             | p
 v             v
 x  ----f----> y

 带有其第一个投影的拉回顶点是 [x] 之上的提升对象，
 第二个投影是 [f] 之上的提升态射；其方形为倒着看的拉回方形。笛卡尔性正是拉回的普适性：
 [f ∘ g] 上的展示态射从 [(e; q)] 是 [h] 的态射，并伴随 [p ∘ h ≈ (f ∘ g) ∘ q]，即对余锥 [(g ∘ q, h)] 的竞争锥，而指向顶点的中介态射是唯一的 [g] 上的展示分解。
*)

Section CodomainCleaving.

Context {C : Category}.

Definition codomain_lift_obj {x y : C} (f : x ~> y)
  (dy : @dobj C (Codomain_Displayed C) y) (P : Pullback f (`2 dy)) :
  @dobj C (Codomain_Displayed C) x :=
  (Pull f (`2 dy) P; pullback_fst f (`2 dy) P).

Definition codomain_lift_mor {x y : C} (f : x ~> y)
  (dy : @dobj C (Codomain_Displayed C) y) (P : Pullback f (`2 dy)) :
  @dhom C (Codomain_Displayed C) x y (codomain_lift_obj f dy P) dy f :=
  (pullback_snd f (`2 dy) P; symmetry (pullback_commutes f (`2 dy) P)).

Lemma codomain_lift_cartesian {x y : C} (f : x ~> y)
  (dy : @dobj C (Codomain_Displayed C) y) (P : Pullback f (`2 dy)) :
  DCartesian (codomain_lift_mor f dy P).
Proof.
  constructor; intros z g dz hh.
  (*
 [hh] is a square over [f ∘ g]: its underlying morphism [`1 hh]
 satisfies [`2 dy ∘ `1 hh ≈ (f ∘ g) ∘ `2 dz], so [(g ∘ `2 dz, `1 hh)]
 is a competing cone over the pullback's cospan. 

 --------
 [hh] 是一个在 [f ∘ g] 上的方形：它的基础态射 [`1 hh] 满足 [`2 dy ∘ `1 hh ≈ (f ∘ g) ∘ `2 dz]，因此 [(g ∘ `2 dz, `1 hh)] 是拉回的余锥的一个竞争锥。
*)
  assert (Hcone : f ∘ (g ∘ `2 dz) ≈ `2 dy ∘ `1 hh).
  { rewrite (`2 hh).
    apply comp_assoc. }
  pose proof (ump_pullbacks f (`2 dy) P (`1 dz) (g ∘ `2 dz) (`1 hh) Hcone)
    as U.
  destruct (unique_property U) as [Ufst Usnd].
  unshelve refine {| unique_obj := (unique_obj U; Ufst) |}.
  - (* the mediator composes with the lift to give back [hh] / 调解员与电梯协作以返回 [hh] *)
    simpl.
    exact Usnd.
  - (* and is the only displayed morphism over [g] that does so / 并且是唯一在 [g] 上显示的具有此性质的态射 *)
    intros v Hv; simpl in Hv.
    apply (uniqueness U); split.
    + exact (`2 v).
    + exact Hv.
Defined.

(*
 The (⇐) direction of the payoff: pullbacks induce a cleaving of the
 codomain displayed category. 

 --------
 收益的 (⇐) 方向：回调会导致所显示的陪域范畴的分裂。
*)
Definition codomain_cleaving `{H : @HasPullbacks C} :
  Cleaving (Codomain_Displayed C) := {|
  clift := fun x y f dy =>
    (codomain_lift_obj f dy (pullback f (`2 dy));
     (codomain_lift_mor f dy (pullback f (`2 dy));
      codomain_lift_cartesian f dy (pullback f (`2 dy))))
|}.

(* * ** Pullbacks from cartesian lifts / * ** 来自笛卡尔提升的回拉 *)

(*
 The (⇒) direction: a cleaving of the codomain displayed category yields
 all pullbacks.  To pull [g : y ~> z] back along [f : x ~> z], regard [g]
 as the displayed object [(y; g)] over [z] and take the chosen cartesian
 lift of [f] at it: the lift object [(P; p1)] over [x] and the lift
 morphism [u] over [f] assemble into the square

 P  ---u--->  y
 |            |
 p1|            | g
 v            v
 x  ---f--->  z .

 For its universal property, a competing cone [(q1, q2)] from [Q] is
 exactly a displayed morphism [(q2; _)] over the composite [f ∘ q1] from
 the displayed object [(Q; id)] — the identity anchors [Q] over itself —
 and [dcart_factor] provides the unique displayed factorization over
 [q1], whose underlying morphism is the mediator. 

 --------
 （⇒）方向：余域显示范畴的一个劈分产生了所有的拉回。为了沿着 [f : x ~> z] 将 [g : y ~> z] 拉回，可以将 [g] 看作 [z] 上的显示对象 [(y; g)]，并取 [f] 在其上的选定笛卡尔提升：提升对象 [(P; p1)] 位于 [x] 上，提升态射 [u] 位于 [f] 上，它们组成如下方形

 P  ---u--->  y
 |            |
 p1|            | g
 v            v
 x  ---f--->  z 。由于其普适性，来自 [Q] 的一个竞争锥 [(q1, q2)] 恰好是一个显示态射 [(q2; _)]，作用于显示对象 [(Q; id)] 上的复合态射 [f ∘ q1]——恒等映射 [Q] 本身作为锚点——并且 [dcart_factor] 提供了在 [q1] 上的唯一显示分解，其基础态射是中介态射。
*)

Definition codomain_cleaving_pullbacks
  `{H : @Cleaving C (Codomain_Displayed C)} : HasPullbacks C.
Proof.
  constructor; intros x y z f g.
  destruct (@clift C (Codomain_Displayed C) H x z f (y; g))
    as [dx [ff cart]].
  destruct dx as [P p1].
  destruct ff as [u sq].
  (*
 sq : g ∘ u ≈ f ∘ p1 — the lift's square is the pullback square 

 --------
 sq : g ∘ u ≈ f ∘ p1 — 抬升的方形是拉回方形
*)
  unshelve refine {| Pull := P; pullback_fst := p1; pullback_snd := u |}.
  - (* the square commutes / 这个方框是可换的 *)
    exact (symmetry sq).
  - (* universal property / 通用属性 *)
    intros Q q1 q2 Hq.
    (*
 the competing square becomes a displayed morphism over [f ∘ q1] 

 --------
 竞争的方形变为 [f ∘ q1] 上的显示态态射
*)
    assert (sqh : g ∘ q2 ≈ (f ∘ q1) ∘ id).
    { rewrite id_right.
      symmetry.
      exact Hq. }
    destruct (@dcart_factor C (Codomain_Displayed C) x z f (P; p1) (y; g)
                (u; sq) cart Q q1
                (existT (fun d : C => d ~{ C }~> Q) Q id) (q2; sqh))
      as [w Hw Huniq].
    simpl in Hw.
    unshelve refine {| unique_obj := `1 w |}.
    + split.
      * (* p1 ∘ w ≈ q1: the factorization's own square, sans the id / p1 ∘ w ≈ q1：因式分解自身的平方，不包括恒等式 *)
        rewrite <- (id_right q1).
        exact (`2 w).
      * (* u ∘ w ≈ q2: the factorization equation / u ∘ w ≈ q2：因式分解方程 *)
        exact Hw.
    + (* uniqueness: a competing mediator is itself a displayed factorization over [q1], so [dcart_factor]'s uniqueness applies / 唯一性：一个竞争的中介本身是在 [q1] 上显示的因式分解，因此 [dcart_factor] 的唯一性适用 *)
      intros v [Hv1 Hv2].
      assert (sqv : p1 ∘ v ≈ q1 ∘ id).
      { rewrite id_right.
        exact Hv1. }
      exact (Huniq (v; sqv) Hv2).
Defined.

End CodomainCleaving.

(* * ** Comparison with the comma-based arrow category / * ** 与基于逗号的箭头类别的比较 *)

(*
 The total category of the codomain displayed category has as objects the
 pairs [(x; (d; p : d ~> x))] — the maps of [C] — and as morphisms the
 pairs [(f; (u; _))] of a base morphism and a square over it.  Reshuffling
 the components yields exactly an object [((d, x); p)] and a morphism
 [((u, f); _)] of the comma category [C ⃗ = (Id[C] ↓ Id[C])] of
 Construction/Arrow.v, with the very same commuting square; and both
 equivalences compare the same two components.  The two reshufflings are
 functorial and mutually inverse on the nose, giving an isomorphism (not
 merely an equivalence) in Cat. 

 --------
 显示范畴的值域的总范畴的对象是对  [(x; (d; p : d ~> x))]  — 即  [C]  的映射 — 而态射是对  [(f; (u; _))]  的一对基态射和其上的方形图。重新排列这些分量恰好产生一个对象  [((d, x); p)]  和态射  [((u, f); _)]  属于 Construction/Arrow.v 中的逗号范畴 [C ⃗ = (Id[C] ↓ Id [C])，且具有完全相同的交换方形图；并且这两个等价都比较相同的两个分量。这两种重新排列是函子性的，并且在精确意义上互为逆元，从而在 Cat 中得到一个同构（不仅仅是等价）。
*)

#[local] Obligation Tactic := program_simpl.

Program Definition Codomain_Total_to_Arrow {C : Category} :
  Total (Codomain_Displayed C) ⟶ @Arrow C := {|
  fobj := fun x => ((`1 (`2 x), `1 x); `2 (`2 x));
  fmap := fun x y f => ((`1 (`2 f), `1 f); `2 (`2 f))
|}.
Next Obligation.
  (* respects ≈: both sides compare the square's leg and the base / 尊重 ≈：双方比较正方形的边和底 *)
  intros f g [e He]; split.
  - exact He.
  - exact e.
Qed.
Next Obligation.
  (* preserves identities, componentwise on the nose / 逐组件精确保持身份 *)
  split; reflexivity.
Qed.
Next Obligation.
  (* preserves composition, componentwise on the nose / 严格保持组成关系、逐组件保持 *)
  split; reflexivity.
Qed.

Program Definition Arrow_to_Codomain_Total {C : Category} :
  @Arrow C ⟶ Total (Codomain_Displayed C) := {|
  fobj := fun x => (snd (`1 x); (fst (`1 x); `2 x));
  fmap := fun x y f => (snd (`1 f); (fst (`1 f); `2 f))
|}.
Next Obligation.
  (* respects ≈, with the reflexivity proof carrying the transport / 尊重 ≈，自反性证明携带运输 *)
  intros f g [e1 e2].
  exists e2; simpl.
  exact e1.
Qed.
Next Obligation.
  (* preserves identities / 保留身份 *)
  exists (Equivalence_Reflexive _); simpl.
  reflexivity.
Qed.
Next Obligation.
  (* preserves composition / 保持组成 *)
  exists (Equivalence_Reflexive _); simpl.
  reflexivity.
Qed.

Program Definition Codomain_Total_Arrow_iso {C : Category} :
  Total (Codomain_Displayed C) ≅[Cat] @Arrow C := {|
  to := Codomain_Total_to_Arrow;
  from := Arrow_to_Codomain_Total
|}.
Next Obligation.
  (* to ∘ from ≈ id on the arrow category / 在箭头范畴上，to ∘ from ≈ id *)
  constructive; simplify; simpl in *; cat.
Qed.
Next Obligation.
  (* from ∘ to ≈ id on the total category / 从 ∘ 到 ≈ id 在总范畴上 *)
  constructive; simplify; simpl in *; cat.
Qed.
