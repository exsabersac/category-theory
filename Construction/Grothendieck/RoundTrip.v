Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Displayed.
Require Import Category.Theory.Fibration.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Displayed.Total.
Require Import Category.Construction.Indexed.
Require Import Category.Construction.Grothendieck.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.StrictCat.ToCat.

Generalizable All Variables.

(*
   * * The round trip: split cleavings versus indexed categories 

   --------
   * * 往返：分裂的劈开与索引范畴
*)

(*
 nLab:      https://ncatlab.org/nlab/show/Grothendieck+construction
 nLab:      https://ncatlab.org/nlab/show/Grothendieck+fibration
 nLab:      https://ncatlab.org/nlab/show/cloven+fibration
 nLab:      https://ncatlab.org/nlab/show/indexed+category
 Wikipedia: https://en.wikipedia.org/wiki/Grothendieck_construction
 Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

 The correspondence between fibrations and indexed categories, in the
 direction that turns a chosen-lift structure on a functor into an indexed
 category and closes the round trip back to the total category.  For
 [P : E ⟶ B] equipped with a cloven structure:

 - [IndexedCat_of_SplitCleaving] builds an [IndexedCat B] (Construction/
 Indexed.v) whose fibre over [x] is the STRICT fibre [{e : E & P e = x}]
 (objects anchored by a propositional object equality [P e = x], the
 sanctioned use of object-level [=]), with reindexing along [f] given by
 the chosen opcartesian lift.  The three coherence families
 [idx_resp]/[idx_id]/[idx_comp] are the mediating fibre isomorphisms
 produced by the lift's universal property, and every pseudofunctor law
 is discharged from that universal property by joint monicity of the
 lift ([vunique]) — never from an object-level equation between lift
 objects, which would require [UIP].

 - [RoundTrip_Comparison] is the comparison functor
 Grothendieck (IndexedCat_of_SplitCleaving P) ⟶ E
 sending a fibre object [(e; p)] to its carrier [e] and a morphism
 [(f; k)] to the vertical part [`1 k] precomposed with the chosen lift
 [pf_mor f].  It lies over the projection: [P ◯ RoundTrip_Comparison] is
 [Grothendieck_Proj] up to the natural isomorphism whose components are
 the anchoring isomorphisms [iso_of_eq (P e = x)]
 ([RoundTrip_Comparison_Proj]).

 - The comparison is full ([RoundTrip_Full], the preimage built from the
 opcartesian universal property), faithful ([RoundTrip_Faithful], base
 component recovered through the projection square and vertical component
 by joint monicity), and strictly surjective on objects; hence an
 equivalence of categories ([RoundTrip_Equivalence]), assembled through
 the full + faithful + essentially-surjective characterization
 (Theory/Equivalence/FullFaithful.v).

 Two deliberate, disclosed departures from the most literal reading:

 (1) VARIANCE.  [IndexedCat B] is covariant — reindexing along [f : x ~> y]
 is a functor [idx_fib x ⟶ idx_fib y] — matching the OPfibration that
 the Grothendieck construction produces (Construction/Indexed.v).  The
 chosen-lift input is therefore taken as a [SplitCleaving (P^op)]: a
 split opfibration of [P], equivalently a split (Grothendieck)
 fibration of [P^op].  The classical contravariant presentation is the
 instance at [B^op].  Concretely the opcartesian lifts of [P] are read
 off the cartesian lifts of [P^op] (Theory/Fibration.v), unwound to
 clean [E]/[B] data by [pf_lift]/[pf_mor]/[pf_over]/[pf_ump] below.

 (2) CLOVEN SUFFICES.  Only the underlying [ClovenFibration (P^op)] of the
 split cleaving is consumed; the two strictness fields [split_lift_id]
 and [split_lift_comp] are not used.  This is a strengthening, not a
 gap: [IndexedCat]'s coherence is iso-valued (a pseudofunctor, not a
 strict 2-functor), so the opcartesian universal property already
 provides coherent [idx_id]/[idx_comp] isomorphisms and discharges the
 unit and cocycle laws.  Splitness would be needed only to make the
 reindexing strictly functorial, i.e. for a STRICT indexed category;
 the round trip and its equivalence hold for any cloven structure.
 The public interface still takes a [SplitCleaving] argument, so the
 stated theorem is exactly "from a split cleaving of [P]". 

 --------
 nLab:       https://ncatlab.org/nlab/show/Grothendieck+construction 
 nLab:       https://ncatlab.org/nlab/show/Grothendieck+fibration 
 nLab:       https://ncatlab.org/nlab/show/cloven+fibration 
 nLab:       https://ncatlab.org/nlab/show/indexed+category 
 Wikipedia:  https://en.wikipedia.org/wiki/Grothendieck_construction 
 Wikipedia:  https://en.wikipedia.org/wiki/Equivalence_of_categories 

 纤维化与索引范畴之间的对应关系，方向是将函子上的选取提升结构转化为索引范畴，并闭合到总范畴的回程。对于
 配备有分裂结构的 [P : E ⟶ B]:- [IndexedCat_of_SplitCleaving] 构造了一个 [IndexedCat B]（Construction/Indexed.v），其在 [x] 上的纤维是严格纤维 [{e : E & P e = x}]（由命题对象等式 [P e = x] 锚定的对象，允许使用对象级别的 [=]），沿 [f] 的重索引由选定的上升余笛卡尔态给出。三个相干族 [idx_resp] / [idx_id] / [idx_comp] 是提升的普遍性质产生的中介纤维同构，每个伪函子律都由提升（[vunique]）的联合单性从该普遍性质中推导出——从不依赖于提升对象之间的对象级别等式，这将需要 [UIP]。- [RoundTrip_Comparison] 是比较函子
 Grothendieck (IndexedCat_of_SplitCleaving P) ⟶ E
 将纤维对象 [(e; p)] 发送到其载体 [e]，并将态射 [(f; k)] 发送到与所选提升 [pf_mor f] 复合的垂直部分 [`1 k]。它位于投影之上：[P ◯ RoundTrip_Comparison] 在自然同构意义下是 [Grothendieck_Proj]，其分量是锚定同构 [iso_of_eq (P e = x)] ([RoundTrip_Comparison_Proj])。- 比较是满的（[RoundTrip_Full]，由opcartesian通用性质构建的前像）、忠实的（[RoundTrip_Faithful]，通过投影平方恢复基分量，通过联合单态恢复垂直分量），并且在对象上严格满射；因此是一个范畴等价（[RoundTrip_Equivalence]），通过满 + 忠实 + 本质上满射的特征组合而成（Theory/Equivalence/FullFaithful.v）。

 两个有意的、公开说明的偏离最字面理解的地方：(1) 方差。[IndexedCat B] 是协变的 — 沿着 [f : x ~> y] 重新索引是一个函子 [idx_fib x ⟶ idx_fib y] — 与 Grothendieck 构造生成的 OP纤维（Construction/Indexed.v）相匹配。因此，所选的提升输入被视为 [SplitCleaving (P^op)]：[P] 的分裂上纤维，同样也等价于 [P^op] 的分裂（Grothendieck）纤维。经典的逆变表示是在 [B^op] 的实例。具体来说，[P] 的上笛卡尔提升可以从 [P^op] 的笛卡尔提升中读出（Theory/Fibration.v），通过下面的 [pf_lift] / [pf_mor] / [pf_over] / [pf_ump] 来展开为干净的 [E] / [B] 数据。(2) 分裂的充分条件。只有分裂劈裂的基础 [ClovenFibration (P^op)] 被使用；两个严格度字段 [split_lift_id] 和 [split_lift_comp] 未被使用。这是一个强化，而不是一个空缺：[IndexedCat] 的相干性是同值的（一个伪函子，而不是严格的 2-函子），因此上笛卡尔普遍性质已经提供了一致的 [idx_id] / [idx_comp] 同构，并满足单位和余循环律。只有在使重索引严格函子化时才需要分裂性，即对于一个严格的索引范畴；往返和其等价性对于任何分裂结构都成立。公共接口仍然接受一个 [SplitCleaving] 参数，因此所陈述的定理正是“从 [P] 的分裂劈裂出发”。
*)

Lemma iso_of_eq_op_to {C : Category} {a b : C} (q : a = b) :
  to (iso_of_eq (C:=C^op) q) ≈ from (iso_of_eq (C:=C) q).
Proof. destruct q; simpl; reflexivity. Qed.

Section RoundTrip.
Context {E B : Category}.
Context (P : E ⟶ B).
Context (Cl : ClovenFibration (P^op)).

(* ---- clean opcartesian interface ---- / ---- 清理 opcartesian 接口 ---- *)

Definition pf_lift {x y : B} (f : x ~> y) (e : E) (p : P e = x) :
  CartesianLift (P^op) (f ∘ to (iso_of_eq p) : P e ~{B}~> y) :=
  @cloven_lift (B^op) (E^op) (P^op) Cl y e (f ∘ to (iso_of_eq p)).

Definition pf_obj {x y : B} (f : x ~> y) (e : E) (p : P e = x) : E :=
  lift_obj (pf_lift f e p).

Definition pf_anchor {x y : B} (f : x ~> y) (e : E) (p : P e = x) :
  P (pf_obj f e p) = y :=
  lift_anchor (pf_lift f e p).

Definition pf_mor {x y : B} (f : x ~> y) (e : E) (p : P e = x) :
  e ~{E}~> pf_obj f e p :=
  lift_mor (pf_lift f e p).

Lemma pf_over {x y : B} (f : x ~> y) (e : E) (p : P e = x) :
  fmap[P] (pf_mor f e p)
    ≈ from (iso_of_eq (pf_anchor f e p)) ∘ (f ∘ to (iso_of_eq p)).
Proof using Cl.
  unfold pf_mor, pf_anchor, pf_obj.
  etransitivity; [ exact (lift_over (pf_lift f e p)) | ].
  rewrite iso_of_eq_op_to.
  reflexivity.
Qed.

Definition pf_ump {x y : B} (f : x ~> y) (e : E) (p : P e = x)
  {c : E} (ψ : e ~> c) (g : P (pf_obj f e p) ~> P c)
  (Hfac : fmap[P] ψ ≈ g ∘ fmap[P] (pf_mor f e p)) :
  ∃! χ : pf_obj f e p ~> c, (χ ∘ pf_mor f e p ≈ ψ) ∧ (fmap[P] χ ≈ g) :=
  @cart_factor (B^op) (E^op) (P^op) (pf_obj f e p) e (pf_mor f e p)
    (lift_cartesian (pf_lift f e p)) c ψ g Hfac.

(* ---- the strict fibre category ---- / ---- 严格的纤维类别 ---- *)

#[local] Obligation Tactic := idtac.

Program Definition StrictFiber (x : B) : Category := {|
  obj := { e : E & P e = x };
  hom := fun a b =>
    { φ : `1 a ~> `1 b
    & fmap[P] φ ≈ from (iso_of_eq (`2 b)) ∘ to (iso_of_eq (`2 a)) };
  homset := fun a b => {| equiv := fun u v => `1 u ≈ `1 v |};
  id := fun a => (id; _);
  compose := fun a b c u v => (`1 u ∘ `1 v; _)
|}.
Next Obligation.
  (* homset is an equivalence relation / homset 是一个等价关系 *)
  intros x a b; simpl.
  equivalence.
Qed.
Next Obligation.
  (* id is vertical / ID 是垂直的 *)
  intros x a; simpl.
  rewrite fmap_id.
  now rewrite iso_from_to.
Qed.
Next Obligation.
  (* composition is vertical / 构图是垂直的 *)
  intros x a b c u v; simpl.
  rewrite fmap_comp.
  rewrite (`2 u), (`2 v).
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to (iso_of_eq (`2 b)))).
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.
Next Obligation.
  (* composition respects ≈ / 作曲尊重 ≈ *)
  intros x a b c u u' Hu v v' Hv; simpl in *.
  now rewrite Hu, Hv.
Qed.
Next Obligation. intros x a b u; simpl; apply id_left. Qed.
Next Obligation. intros x a b u; simpl; apply id_right. Qed.
Next Obligation. intros x a b c d u v w; simpl; apply comp_assoc. Qed.
Next Obligation. intros x a b c d u v w; simpl; apply comp_assoc_sym. Qed.

(* ---- the reindexing functor ---- / ---- 重建索引函子 ---- *)

(*
 The base witness that the reindexed morphism lies over: the identity of
 the target fibre, expressed through the two anchors. 

 --------
 重索引态射所位于的基础见证：目标纤维的恒等，通过两个锚点表示。
*)
Definition rmap_g {x y : B} (f : x ~> y) (a b : { e : E & P e = x }) :
  P (pf_obj f (`1 a) (`2 a)) ~> P (pf_obj f (`1 b) (`2 b)) :=
  from (iso_of_eq (pf_anchor f (`1 b) (`2 b)))
    ∘ to (iso_of_eq (pf_anchor f (`1 a) (`2 a))).

Lemma rmap_fac {x y : B} (f : x ~> y) (a b : { e : E & P e = x })
  (u : { φ : `1 a ~> `1 b
       & fmap[P] φ ≈ from (iso_of_eq (`2 b)) ∘ to (iso_of_eq (`2 a)) }) :
  fmap[P] (pf_mor f (`1 b) (`2 b) ∘ `1 u)
    ≈ rmap_g f a b ∘ fmap[P] (pf_mor f (`1 a) (`2 a)).
Proof using Cl.
  destruct a as [ea pa], b as [eb pb], u as [φ vφ]; simpl in *.
  unfold rmap_g; simpl.
  rewrite fmap_comp.
  rewrite (pf_over f eb pb).
  rewrite vφ.
  rewrite (pf_over f ea pa).
  (*
 left:  (from(anchor_b) ∘ (f ∘ to pb)) ∘ (from pb ∘ to pa)
 right: (from(anchor_b) ∘ to(anchor_a)) ∘ (from(anchor_a) ∘ (f ∘ to pa)) 

 --------
 左:  (从(anchor_b) ∘ (f ∘ 到 pb)) ∘ (从 pb ∘ 到 pa)
 右: (从(anchor_b) ∘ 到(anchor_a)) ∘ (从(anchor_a) ∘ (f ∘ 到 pa))
*)
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (iso_of_eq pb))).
  rewrite iso_to_from, id_left.
  rewrite (comp_assoc (to (iso_of_eq (pf_anchor f ea pa)))).
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

Definition rmap {x y : B} (f : x ~> y) (a b : { e : E & P e = x })
  (u : { φ : `1 a ~> `1 b
       & fmap[P] φ ≈ from (iso_of_eq (`2 b)) ∘ to (iso_of_eq (`2 a)) }) :=
  pf_ump f (`1 a) (`2 a) (pf_mor f (`1 b) (`2 b) ∘ `1 u) (rmap_g f a b)
    (rmap_fac f a b u).

Program Definition Reindex {x y : B} (f : x ~> y) :
  StrictFiber x ⟶ StrictFiber y := {|
  fobj := fun a => (pf_obj f (`1 a) (`2 a); pf_anchor f (`1 a) (`2 a));
  fmap := fun a b u => (unique_obj (rmap f a b u); _)
|}.
Next Obligation.
  (* the reindexed morphism is vertical over y / 重建指数的态射在 y 上是垂直的 *)
  intros x y f a b u; simpl.
  exact (snd (unique_property (rmap f a b u))).
Qed.
Next Obligation.
  (* fmap respects ≈ / fmap 遵守 ≈ *)
  intros x y f a b u u' Huu'; simpl in *.
  apply (uniqueness (rmap f a b u)).
  pose proof (unique_property (rmap f a b u')) as [H1 H2].
  split.
  - rewrite H1; now rewrite Huu'.
  - exact H2.
Qed.
Next Obligation.
  (* fmap preserves identities / fmap 保持恒等式 *)
  intros x y f a; simpl.
  apply (uniqueness (rmap f a a _)); simpl.
  split.
  - now rewrite id_right, id_left.
  - rewrite fmap_id.
    unfold rmap_g.
    now rewrite iso_from_to.
Qed.
Next Obligation.
  (* fmap preserves composition / fmap 保持组合性 *)
  intros x y f a b c u v; simpl.
  apply (uniqueness (rmap f a c _)); simpl.
  pose proof (unique_property (rmap f b c u)) as [Hu1 Hu2].
  pose proof (unique_property (rmap f a b v)) as [Hv1 Hv2].
  split.
  - rewrite <- comp_assoc.
    rewrite Hv1.
    rewrite comp_assoc.
    rewrite Hu1.
    now rewrite comp_assoc.
  - rewrite fmap_comp.
    rewrite Hu2, Hv2.
    unfold rmap_g.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to (iso_of_eq (pf_anchor f (`1 b) (`2 b))))).
    rewrite iso_to_from, id_left.
    reflexivity.
Qed.

(*
 ---- workhorses: the mediating vertical morphism and joint monicity ---- 

 --------
 ---- 骆驼马：中介垂直态射与联合单态 ----
*)

Lemma mediate_fac {x y : B} (f : x ~> y) (e : E) (p : P e = x)
  (d : E) (q : P d = y) (m : e ~> d)
  (Hm : fmap[P] m ≈ from (iso_of_eq q) ∘ (f ∘ to (iso_of_eq p))) :
  fmap[P] m
    ≈ (from (iso_of_eq q) ∘ to (iso_of_eq (pf_anchor f e p)))
        ∘ fmap[P] (pf_mor f e p).
Proof using Cl.
  rewrite (pf_over f e p).
  rewrite Hm.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (iso_of_eq (pf_anchor f e p)))).
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

Definition med {x y : B} (f : x ~> y) (e : E) (p : P e = x)
  (d : E) (q : P d = y) (m : e ~> d)
  (Hm : fmap[P] m ≈ from (iso_of_eq q) ∘ (f ∘ to (iso_of_eq p))) :=
  pf_ump f e p m (from (iso_of_eq q) ∘ to (iso_of_eq (pf_anchor f e p)))
    (mediate_fac f e p d q m Hm).

Definition mediate {x y : B} (f : x ~> y) (e : E) (p : P e = x)
  (d : E) (q : P d = y) (m : e ~> d)
  (Hm : fmap[P] m ≈ from (iso_of_eq q) ∘ (f ∘ to (iso_of_eq p))) :
  pf_obj f e p ~> d :=
  unique_obj (med f e p d q m Hm).

Lemma mediate_comm {x y : B} (f : x ~> y) (e : E) (p : P e = x)
  (d : E) (q : P d = y) (m : e ~> d)
  (Hm : fmap[P] m ≈ from (iso_of_eq q) ∘ (f ∘ to (iso_of_eq p))) :
  mediate f e p d q m Hm ∘ pf_mor f e p ≈ m.
Proof using Cl. exact (fst (unique_property (med f e p d q m Hm))). Qed.

Lemma mediate_over {x y : B} (f : x ~> y) (e : E) (p : P e = x)
  (d : E) (q : P d = y) (m : e ~> d)
  (Hm : fmap[P] m ≈ from (iso_of_eq q) ∘ (f ∘ to (iso_of_eq p))) :
  fmap[P] (mediate f e p d q m Hm)
    ≈ from (iso_of_eq q) ∘ to (iso_of_eq (pf_anchor f e p)).
Proof using Cl. exact (snd (unique_property (med f e p d q m Hm))). Qed.

(*
 Joint monicity of the opcartesian lift: two morphisms out of a pushforward
 that agree after precomposition with the lift and on the base are equal. 

 --------
 opcartesian 抬升的联合单性：两个从推前来的态射，如果在与抬升预组合后以及在基上相等，则它们相等。
*)
Lemma vunique {x y : B} (f : x ~> y) (e : E) (p : P e = x) (d : E)
  (u v : pf_obj f e p ~> d)
  (Hcomm : u ∘ pf_mor f e p ≈ v ∘ pf_mor f e p)
  (Hover : fmap[P] u ≈ fmap[P] v) :
  u ≈ v.
Proof using Cl.
  assert (Hfac : fmap[P] (v ∘ pf_mor f e p)
                   ≈ fmap[P] v ∘ fmap[P] (pf_mor f e p)) by apply fmap_comp.
  pose (U := pf_ump f e p (v ∘ pf_mor f e p) (fmap[P] v) Hfac).
  transitivity (unique_obj U).
  - symmetry. apply (uniqueness U). split; [ exact Hcomm | exact Hover ].
  - apply (uniqueness U). split; reflexivity.
Qed.

(*
 ---- packaging a fibre isomorphism from two inverse vertical morphisms ---- 

 --------
 ---- 从两个逆垂直态射打包一个纤维同构 ----
*)

Definition sfiso {y : B} {d1 d2 : E} (q1 : P d1 = y) (q2 : P d2 = y)
  (t : d1 ~> d2) (fr : d2 ~> d1)
  (Ht : fmap[P] t ≈ from (iso_of_eq q2) ∘ to (iso_of_eq q1))
  (Hf : fmap[P] fr ≈ from (iso_of_eq q1) ∘ to (iso_of_eq q2))
  (Htf : t ∘ fr ≈ id) (Hft : fr ∘ t ≈ id) :
  @Isomorphism (StrictFiber y) (d1; q1) (d2; q2) :=
  @Build_Isomorphism (StrictFiber y) (d1; q1) (d2; q2)
    (t; Ht) (fr; Hf) Htf Hft.

(*
 ---- idx_resp: reindexing respects ≈ on base morphisms ---- 

 --------
 ---- idx_resp：重建索引遵循基态同态上的≈ ----
*)

Lemma pf_over_cast {x y : B} (f g : x ~> y) (ε : f ≈ g) (e : E) (p : P e = x) :
  fmap[P] (pf_mor g e p)
    ≈ from (iso_of_eq (pf_anchor g e p)) ∘ (f ∘ to (iso_of_eq p)).
Proof using Cl. now rewrite (pf_over g e p), ε. Qed.

Lemma vfmap_cancel {y : B} {d1 d2 d3 : E}
  (q1 : P d1 = y) (q2 : P d2 = y) (q3 : P d3 = y)
  (u : d1 ~> d2) (v : d2 ~> d3)
  (Hu : fmap[P] u ≈ from (iso_of_eq q2) ∘ to (iso_of_eq q1))
  (Hv : fmap[P] v ≈ from (iso_of_eq q3) ∘ to (iso_of_eq q2)) :
  fmap[P] (v ∘ u) ≈ from (iso_of_eq q3) ∘ to (iso_of_eq q1).
Proof using Cl.
  rewrite fmap_comp, Hu, Hv.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (iso_of_eq q2))).
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

Section IdxResp.
Context {x y : B} {f g : x ~> y} (ε : f ≈ g) (a : { e : E & P e = x }).

Let e := `1 a.
Let p := `2 a.

Definition resp_to : pf_obj f e p ~> pf_obj g e p :=
  mediate f e p (pf_obj g e p) (pf_anchor g e p) (pf_mor g e p)
    (pf_over_cast f g ε e p).

Definition resp_from : pf_obj g e p ~> pf_obj f e p :=
  mediate g e p (pf_obj f e p) (pf_anchor f e p) (pf_mor f e p)
    (pf_over_cast g f (symmetry ε) e p).

Lemma resp_tf : resp_to ∘ resp_from ≈ id.
Proof using Cl.
  apply (vunique g e p (pf_obj g e p)).
  - rewrite <- comp_assoc.
    unfold resp_from; rewrite mediate_comm.
    unfold resp_to; rewrite mediate_comm.
    now rewrite id_left.
  - rewrite fmap_id.
    transitivity (from (iso_of_eq (pf_anchor g e p))
                    ∘ to (iso_of_eq (pf_anchor g e p))).
    + apply (vfmap_cancel (pf_anchor g e p) (pf_anchor f e p)
               (pf_anchor g e p)); apply mediate_over.
    + apply iso_from_to.
Qed.

Lemma resp_ft : resp_from ∘ resp_to ≈ id.
Proof using Cl.
  apply (vunique f e p (pf_obj f e p)).
  - rewrite <- comp_assoc.
    unfold resp_to; rewrite mediate_comm.
    unfold resp_from; rewrite mediate_comm.
    now rewrite id_left.
  - rewrite fmap_id.
    transitivity (from (iso_of_eq (pf_anchor f e p))
                    ∘ to (iso_of_eq (pf_anchor f e p))).
    + apply (vfmap_cancel (pf_anchor f e p) (pf_anchor g e p)
               (pf_anchor f e p)); apply mediate_over.
    + apply iso_from_to.
Qed.

Definition idx_resp_iso :
  @Isomorphism (StrictFiber y)
    (pf_obj f e p; pf_anchor f e p) (pf_obj g e p; pf_anchor g e p) :=
  sfiso (pf_anchor f e p) (pf_anchor g e p) resp_to resp_from
    (mediate_over f e p (pf_obj g e p) (pf_anchor g e p) (pf_mor g e p)
       (pf_over_cast f g ε e p))
    (mediate_over g e p (pf_obj f e p) (pf_anchor f e p) (pf_mor f e p)
       (pf_over_cast g f (symmetry ε) e p))
    resp_tf resp_ft.

Lemma resp_to_comm : resp_to ∘ pf_mor f e p ≈ pf_mor g e p.
Proof using Cl. unfold resp_to; apply mediate_comm. Qed.

Lemma resp_to_over :
  fmap[P] resp_to
    ≈ from (iso_of_eq (pf_anchor g e p)) ∘ to (iso_of_eq (pf_anchor f e p)).
Proof using Cl. unfold resp_to; apply mediate_over. Qed.

Lemma resp_from_comm : resp_from ∘ pf_mor g e p ≈ pf_mor f e p.
Proof using Cl. unfold resp_from; apply mediate_comm. Qed.

Lemma resp_from_over :
  fmap[P] resp_from
    ≈ from (iso_of_eq (pf_anchor f e p)) ∘ to (iso_of_eq (pf_anchor g e p)).
Proof using Cl. unfold resp_from; apply mediate_over. Qed.

End IdxResp.

(* ---- idx_id: reindexing along the identity ---- / ---- idx_id：沿身份重新索引 ---- *)

Section IdxId.
Context {x : B} (a : { e : E & P e = x }).

Let e := `1 a.
Let p := `2 a.

Lemma id_to_over :
  fmap[P] (@id E e) ≈ from (iso_of_eq p) ∘ (@id B x ∘ to (iso_of_eq p)).
Proof using Cl. now rewrite fmap_id, id_left, iso_from_to. Qed.

Definition idid_to : pf_obj (@id B x) e p ~> e :=
  mediate (@id B x) e p e p (@id E e) id_to_over.

Lemma idid_from_over :
  fmap[P] (pf_mor (@id B x) e p)
    ≈ from (iso_of_eq (pf_anchor (@id B x) e p)) ∘ to (iso_of_eq p).
Proof using Cl. now rewrite (pf_over (@id B x) e p), id_left. Qed.

Lemma idid_tf : idid_to ∘ pf_mor (@id B x) e p ≈ id.
Proof using Cl. unfold idid_to; apply mediate_comm. Qed.

Lemma idid_ft : pf_mor (@id B x) e p ∘ idid_to ≈ id.
Proof using Cl.
  apply (vunique (@id B x) e p (pf_obj (@id B x) e p)).
  - rewrite <- comp_assoc, idid_tf.
    now rewrite id_left, id_right.
  - rewrite fmap_id.
    transitivity (from (iso_of_eq (pf_anchor (@id B x) e p))
                    ∘ to (iso_of_eq (pf_anchor (@id B x) e p))).
    + apply (vfmap_cancel (pf_anchor (@id B x) e p) p
               (pf_anchor (@id B x) e p)).
      * exact (mediate_over (@id B x) e p e p (@id E e) id_to_over).
      * exact idid_from_over.
    + apply iso_from_to.
Qed.

Definition idx_id_iso :
  @Isomorphism (StrictFiber x)
    (pf_obj (@id B x) e p; pf_anchor (@id B x) e p) (e; p) :=
  sfiso (pf_anchor (@id B x) e p) p idid_to (pf_mor (@id B x) e p)
    (mediate_over (@id B x) e p e p (@id E e) id_to_over)
    idid_from_over idid_tf idid_ft.

End IdxId.

(*
 The unit iso [idx_id_iso a] has codomain [(`1 a; `2 a)]; the [IndexedCat]
 field wants codomain [a].  The two objects have definitionally identical
 hom-sets (the hom depends only on the projections), so the morphisms and
 proofs transport, but the [Isomorphism] record type is pinned to the
 codomain object and must be rebuilt.  The rebuilt iso reuses the same
 underlying [to]/[from], so [to (RT_idx_id a)] is [to (idx_id_iso a)]
 definitionally and the unit coherence lemmas apply unchanged. 

 --------
 单位同构 [idx_id_iso a] 的余域是 [(`1 a; `2 a)]；[IndexedCat] 字段希望的余域是 [a]。两个对象的同态集在定义上是相同的（同态只依赖于投影），因此态射和证明可以传输，但 [Isomorphism] 记录类型固定在余域对象上，必须重新构建。重新构建的同构重复使用相同的底层 [to] / [from]，因此 [to (RT_idx_id a)] 在定义上是 [to (idx_id_iso a)]，并且单位相干引理适用且不变。
*)
Definition RT_idx_id {x : B} (a : StrictFiber x) :
  @Isomorphism (StrictFiber x) (Reindex (@id B x) a) a :=
  @Build_Isomorphism (StrictFiber x) (Reindex (@id B x) a) a
    (to (idx_id_iso a)) (from (idx_id_iso a))
    (iso_to_from (idx_id_iso a)) (iso_from_to (idx_id_iso a)).

(* ---- idx_comp: reindexing along a composite ---- / ---- idx_comp：沿复合索引重新索引 ---- *)

Section IdxComp.
Context {x y z : B} (f : y ~> z) (g : x ~> y) (a : { e : E & P e = x }).

Let e := `1 a.
Let p := `2 a.

(* the two pushforward legs / 两个前推腿 *)
Definition eg : E := pf_obj g e p.
Definition qg : P eg = y := pf_anchor g e p.
Definition D1 : E := pf_obj f eg qg.
Definition qD1 : P D1 = z := pf_anchor f eg qg.
Definition D2 : E := pf_obj (f ∘ g) e p.
Definition qD2 : P D2 = z := pf_anchor (f ∘ g) e p.

Definition mfg : e ~> D1 := pf_mor f eg qg ∘ pf_mor g e p.

Lemma mfg_over :
  fmap[P] mfg ≈ from (iso_of_eq qD1) ∘ ((f ∘ g) ∘ to (iso_of_eq p)).
Proof using Cl.
  unfold mfg.
  rewrite fmap_comp.
  rewrite (pf_over f eg qg).
  rewrite (pf_over g e p).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (iso_of_eq qg))).
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

Lemma mg_fac :
  fmap[P] (pf_mor (f ∘ g) e p)
    ≈ (from (iso_of_eq qD2) ∘ (f ∘ to (iso_of_eq qg)))
        ∘ fmap[P] (pf_mor g e p).
Proof using Cl.
  rewrite (pf_over (f ∘ g) e p).
  rewrite (pf_over g e p).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (iso_of_eq qg))).
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

Definition mg_u :=
  pf_ump g e p (pf_mor (f ∘ g) e p)
    (from (iso_of_eq qD2) ∘ (f ∘ to (iso_of_eq qg))) mg_fac.

Definition mg : eg ~> D2 := unique_obj mg_u.

Lemma mg_comm : mg ∘ pf_mor g e p ≈ pf_mor (f ∘ g) e p.
Proof using Cl. exact (fst (unique_property mg_u)). Qed.

Lemma mg_over :
  fmap[P] mg ≈ from (iso_of_eq qD2) ∘ (f ∘ to (iso_of_eq qg)).
Proof using Cl. exact (snd (unique_property mg_u)). Qed.

Definition comp_to : D1 ~> D2 := mediate f eg qg D2 qD2 mg mg_over.
Definition comp_from : D2 ~> D1 := mediate (f ∘ g) e p D1 qD1 mfg mfg_over.

Lemma from_mg : comp_from ∘ mg ≈ pf_mor f eg qg.
Proof using Cl.
  apply (vunique g e p D1).
  - rewrite <- comp_assoc, mg_comm.
    unfold comp_from; rewrite (mediate_comm (f ∘ g) e p D1 qD1 mfg mfg_over).
    reflexivity.
  - rewrite fmap_comp.
    unfold comp_from; rewrite (mediate_over (f ∘ g) e p D1 qD1 mfg mfg_over).
    rewrite mg_over.
    rewrite (pf_over f eg qg).
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (to (iso_of_eq qD2))).
    rewrite iso_to_from, id_left.
    reflexivity.
Qed.

Lemma comp_tf : comp_to ∘ comp_from ≈ id.
Proof using Cl.
  apply (vunique (f ∘ g) e p D2).
  - rewrite <- comp_assoc.
    unfold comp_from; rewrite (mediate_comm (f ∘ g) e p D1 qD1 mfg mfg_over).
    unfold mfg.
    rewrite comp_assoc.
    unfold comp_to; rewrite (mediate_comm f eg qg D2 qD2 mg mg_over).
    rewrite mg_comm.
    now rewrite id_left.
  - rewrite fmap_id.
    transitivity (from (iso_of_eq qD2) ∘ to (iso_of_eq qD2)).
    + apply (vfmap_cancel qD2 qD1 qD2).
      * exact (mediate_over (f ∘ g) e p D1 qD1 mfg mfg_over).
      * exact (mediate_over f eg qg D2 qD2 mg mg_over).
    + apply iso_from_to.
Qed.

Lemma comp_ft : comp_from ∘ comp_to ≈ id.
Proof using Cl.
  apply (vunique f eg qg D1).
  - rewrite <- comp_assoc.
    unfold comp_to; rewrite (mediate_comm f eg qg D2 qD2 mg mg_over).
    rewrite from_mg.
    now rewrite id_left.
  - rewrite fmap_id.
    transitivity (from (iso_of_eq qD1) ∘ to (iso_of_eq qD1)).
    + apply (vfmap_cancel qD1 qD2 qD1).
      * exact (mediate_over f eg qg D2 qD2 mg mg_over).
      * exact (mediate_over (f ∘ g) e p D1 qD1 mfg mfg_over).
    + apply iso_from_to.
Qed.

Definition idx_comp_iso :
  @Isomorphism (StrictFiber z) (D1; qD1) (D2; qD2) :=
  sfiso qD1 qD2 comp_to comp_from
    (mediate_over f eg qg D2 qD2 mg mg_over)
    (mediate_over (f ∘ g) e p D1 qD1 mfg mfg_over)
    comp_tf comp_ft.

Lemma comp_to_comm : comp_to ∘ pf_mor f eg qg ≈ mg.
Proof using Cl. unfold comp_to; apply (mediate_comm f eg qg D2 qD2 mg mg_over). Qed.

Lemma comp_to_over :
  fmap[P] comp_to ≈ from (iso_of_eq qD2) ∘ to (iso_of_eq qD1).
Proof using Cl. unfold comp_to; apply (mediate_over f eg qg D2 qD2 mg mg_over). Qed.

Lemma comp_from_comm : comp_from ∘ pf_mor (f ∘ g) e p ≈ mfg.
Proof using Cl.
  unfold comp_from; apply (mediate_comm (f ∘ g) e p D1 qD1 mfg mfg_over).
Qed.

Lemma comp_from_over :
  fmap[P] comp_from ≈ from (iso_of_eq qD1) ∘ to (iso_of_eq qD2).
Proof using Cl.
  unfold comp_from; apply (mediate_over (f ∘ g) e p D1 qD1 mfg mfg_over).
Qed.

End IdxComp.

(*
 ---- accessors for the reindexing functor's action on morphisms ---- 

 --------
 ---- 重索引函子在态射上的作用的访问器 ----
*)

Lemma rmap_comm {x y : B} (f : x ~> y) (a b : { e : E & P e = x })
  (u : { φ : `1 a ~> `1 b
       & fmap[P] φ ≈ from (iso_of_eq (`2 b)) ∘ to (iso_of_eq (`2 a)) }) :
  unique_obj (rmap f a b u) ∘ pf_mor f (`1 a) (`2 a)
    ≈ pf_mor f (`1 b) (`2 b) ∘ `1 u.
Proof using Cl. exact (fst (unique_property (rmap f a b u))). Qed.

Lemma rmap_over {x y : B} (f : x ~> y) (a b : { e : E & P e = x })
  (u : { φ : `1 a ~> `1 b
       & fmap[P] φ ≈ from (iso_of_eq (`2 b)) ∘ to (iso_of_eq (`2 a)) }) :
  fmap[P] (unique_obj (rmap f a b u)) ≈ rmap_g f a b.
Proof using Cl. exact (snd (unique_property (rmap f a b u))). Qed.

(*
 The same accessors phrased through the functor projection, so they match
 the goal shape [`1 (fmap[Reindex f] u)] that arises after reducing a
 [StrictFiber] composite to its underlying vertical morphism. 

 --------
 通过函子投影表达的相同访问器，因此它们匹配在将 [StrictFiber] 复合体约简到其底层垂直态射后出现的目标形状 [`1 (fmap[Reindex f]  u)]。
*)
Lemma reindex_comm {x y : B} (f : x ~> y) {a b : StrictFiber x}
  (u : a ~> b) :
  `1 (fmap[Reindex f] u) ∘ pf_mor f (`1 a) (`2 a)
    ≈ pf_mor f (`1 b) (`2 b) ∘ `1 u.
Proof using Cl. exact (rmap_comm f a b u). Qed.

Lemma reindex_over {x y : B} (f : x ~> y) {a b : StrictFiber x}
  (u : a ~> b) :
  fmap[P] (`1 (fmap[Reindex f] u))
    ≈ from (iso_of_eq (pf_anchor f (`1 b) (`2 b)))
        ∘ to (iso_of_eq (pf_anchor f (`1 a) (`2 a))).
Proof using Cl. exact (rmap_over f a b u). Qed.

(*
 Break a [StrictFiber] composite down to its underlying vertical morphism:
 the fibre's composition is the base composition on first components.  A
 [StrictFiber] object is not in constructor form, so this projection does
 not fire on its own; the lemma exposes it for rewriting. 

 --------
 将一个 [StrictFiber] 复合物分解为其基础的垂直态射：
 纤维的复合是第一分量上的基复合。一个
 [StrictFiber] 对象不是构造形式，因此这个投影不会自行触发；引理将其暴露出来以便重写。
*)
Lemma sf_comp1 {x : B} {a b c : StrictFiber x} (u : b ~> c) (v : a ~> b) :
  `1 (u ∘ v) ≈ `1 u ∘ `1 v.
Proof. reflexivity. Qed.

(*
 Break every [StrictFiber] composite under a first projection down to the
 base composition.  Implicit-argument matching of [sf_comp1] is unreliable
 under the fibre coercions, so each rewrite supplies the two factors
 explicitly. 

 --------
 在第一次投影下，将每个 [StrictFiber] 复合体分解为基础复合体。在纤维强制下，[sf_comp1] 的隐式参数匹配不可靠，因此每次重写都会明确提供两个因子。
*)
Ltac break_sf :=
  repeat match goal with
  | |- context[`1 (?u ∘ ?v)] => rewrite (sf_comp1 u v)
  end.

(*
 Accessors phrased on the iso projections themselves, matching the goal
 shape after [sf_comp1].  Each holds by conversion from the underlying
 [resp_to]/[idid_to]/[comp_to] accessor. 

 --------
 访问器基于 ISO 投影本身进行表述，匹配 [sf_comp1] 之后的目标形状。每个访问器都通过从底层 [resp_to] / [idid_to] / [comp_to] 访问器进行转换来保持。
*)
Lemma respi_to_comm {x y : B} {f g : x ~> y} (ε : f ≈ g)
  (a : { e : E & P e = x }) :
  `1 (to (idx_resp_iso ε a)) ∘ pf_mor f (`1 a) (`2 a)
    ≈ pf_mor g (`1 a) (`2 a).
Proof using Cl. exact (resp_to_comm ε a). Qed.

Lemma respi_to_over {x y : B} {f g : x ~> y} (ε : f ≈ g)
  (a : { e : E & P e = x }) :
  fmap[P] (`1 (to (idx_resp_iso ε a)))
    ≈ from (iso_of_eq (pf_anchor g (`1 a) (`2 a)))
        ∘ to (iso_of_eq (pf_anchor f (`1 a) (`2 a))).
Proof using Cl. exact (resp_to_over ε a). Qed.

Lemma idi_to_comm {x : B} (a : { e : E & P e = x }) :
  `1 (to (idx_id_iso a)) ∘ pf_mor (@id B x) (`1 a) (`2 a) ≈ id.
Proof using Cl. exact (idid_tf a). Qed.

Lemma idi_to_over {x : B} (a : { e : E & P e = x }) :
  fmap[P] (`1 (to (idx_id_iso a)))
    ≈ from (iso_of_eq (`2 a))
        ∘ to (iso_of_eq (pf_anchor (@id B x) (`1 a) (`2 a))).
Proof using Cl.
  exact (mediate_over (@id B x) (`1 a) (`2 a) (`1 a) (`2 a)
           (@id E (`1 a)) (id_to_over a)).
Qed.

Lemma compi_to_comm {x y z : B} (f : y ~> z) (g : x ~> y)
  (a : { e : E & P e = x }) :
  `1 (to (idx_comp_iso f g a))
     ∘ pf_mor f (pf_obj g (`1 a) (`2 a)) (pf_anchor g (`1 a) (`2 a))
    ≈ mg f g a.
Proof using Cl. exact (comp_to_comm f g a). Qed.

Lemma compi_to_over {x y z : B} (f : y ~> z) (g : x ~> y)
  (a : { e : E & P e = x }) :
  fmap[P] (`1 (to (idx_comp_iso f g a)))
    ≈ from (iso_of_eq (pf_anchor (f ∘ g) (`1 a) (`2 a)))
        ∘ to (iso_of_eq
                (pf_anchor f (pf_obj g (`1 a) (`2 a))
                   (pf_anchor g (`1 a) (`2 a)))).
Proof using Cl. exact (comp_to_over f g a). Qed.

Lemma mgi_comm {x y z : B} (f : y ~> z) (g : x ~> y)
  (a : { e : E & P e = x }) :
  mg f g a ∘ pf_mor g (`1 a) (`2 a) ≈ pf_mor (f ∘ g) (`1 a) (`2 a).
Proof using Cl. exact (mg_comm f g a). Qed.

Lemma mgi_over {x y z : B} (f : y ~> z) (g : x ~> y)
  (a : { e : E & P e = x }) :
  fmap[P] (mg f g a)
    ≈ from (iso_of_eq (pf_anchor (f ∘ g) (`1 a) (`2 a)))
        ∘ (f ∘ to (iso_of_eq (pf_anchor g (`1 a) (`2 a)))).
Proof using Cl. exact (mg_over f g a). Qed.

(*
 The [from]-side companions of the mediator comm/over accessors, used by
 the comparison functor below: the inverse mediators split the one-step
 lift back into its constituents. 

 --------
 调解器 comm/over 访问器的 [from] 侧伴随对象，由下面的比较仿函数使用：逆调解器将单步提升拆分回其组成部分。
*)
Lemma respi_from_comm {x y : B} {f g : x ~> y} (ε : f ≈ g)
  (a : { e : E & P e = x }) :
  `1 (from (idx_resp_iso ε a)) ∘ pf_mor g (`1 a) (`2 a)
    ≈ pf_mor f (`1 a) (`2 a).
Proof using Cl. exact (resp_from_comm ε a). Qed.

Lemma respi_from_over {x y : B} {f g : x ~> y} (ε : f ≈ g)
  (a : { e : E & P e = x }) :
  fmap[P] (`1 (from (idx_resp_iso ε a)))
    ≈ from (iso_of_eq (pf_anchor f (`1 a) (`2 a)))
        ∘ to (iso_of_eq (pf_anchor g (`1 a) (`2 a))).
Proof using Cl. exact (resp_from_over ε a). Qed.

Lemma compi_from_comm {x y z : B} (f : y ~> z) (g : x ~> y)
  (a : { e : E & P e = x }) :
  `1 (from (idx_comp_iso f g a)) ∘ pf_mor (f ∘ g) (`1 a) (`2 a)
    ≈ pf_mor f (`1 (Reindex g a)) (`2 (Reindex g a)) ∘ pf_mor g (`1 a) (`2 a).
Proof using Cl. exact (comp_from_comm f g a). Qed.

(* ---- coherence laws ---- / ---- 相干律 ---- *)

Lemma RT_resp_id {x y : B} {f : x ~> y} (ε : f ≈ f) (a : { e : E & P e = x }) :
  to (idx_resp_iso ε a) ≈ @id (StrictFiber y) (Reindex f a).
Proof using Cl.
  apply (vunique f (`1 a) (`2 a) (pf_obj f (`1 a) (`2 a))).
  - unfold resp_to.
    rewrite (mediate_comm f (`1 a) (`2 a) (pf_obj f (`1 a) (`2 a))
               (pf_anchor f (`1 a) (`2 a)) (pf_mor f (`1 a) (`2 a))
               (pf_over_cast f f ε (`1 a) (`2 a))).
    now rewrite id_left.
  - rewrite fmap_id.
    transitivity (from (iso_of_eq (pf_anchor f (`1 a) (`2 a)))
                    ∘ to (iso_of_eq (pf_anchor f (`1 a) (`2 a)))).
    + exact (mediate_over f (`1 a) (`2 a) (pf_obj f (`1 a) (`2 a))
               (pf_anchor f (`1 a) (`2 a)) (pf_mor f (`1 a) (`2 a))
               (pf_over_cast f f ε (`1 a) (`2 a))).
    + apply iso_from_to.
Qed.

Lemma RT_resp_natural {x y : B} {f g : x ~> y} (ε : f ≈ g)
  {a b : StrictFiber x} (k : a ~> b) :
  fmap[Reindex g] k ∘ to (idx_resp_iso ε a)
    ≈ to (idx_resp_iso ε b) ∘ fmap[Reindex f] k.
Proof using Cl.
  apply (vunique f (`1 a) (`2 a) (pf_obj g (`1 b) (`2 b))).
  - break_sf.
    rewrite <- comp_assoc.
    rewrite (respi_to_comm ε a).
    rewrite (reindex_comm g k).
    rewrite <- comp_assoc.
    rewrite (reindex_comm f k).
    rewrite comp_assoc.
    rewrite (respi_to_comm ε b).
    reflexivity.
  - break_sf.
    transitivity (from (iso_of_eq (pf_anchor g (`1 b) (`2 b)))
                    ∘ to (iso_of_eq (pf_anchor f (`1 a) (`2 a)))).
    + apply (vfmap_cancel (pf_anchor f (`1 a) (`2 a))
               (pf_anchor g (`1 a) (`2 a)) (pf_anchor g (`1 b) (`2 b))).
      * exact (respi_to_over ε a).
      * exact (reindex_over g k).
    + symmetry.
      apply (vfmap_cancel (pf_anchor f (`1 a) (`2 a))
               (pf_anchor f (`1 b) (`2 b)) (pf_anchor g (`1 b) (`2 b))).
      * exact (reindex_over f k).
      * exact (respi_to_over ε b).
Qed.

Lemma RT_resp_trans {x y : B} {f g h : x ~> y}
  (e1 : f ≈ g) (e2 : g ≈ h) (a : { e : E & P e = x }) :
  to (idx_resp_iso e2 a) ∘ to (idx_resp_iso e1 a)
    ≈ to (idx_resp_iso (Equivalence_Transitive _ _ _ e1 e2) a).
Proof using Cl.
  apply (vunique f (`1 a) (`2 a) (pf_obj h (`1 a) (`2 a))).
  - break_sf.
    rewrite <- comp_assoc.
    rewrite (respi_to_comm e1 a).
    rewrite (respi_to_comm e2 a).
    rewrite (respi_to_comm (Equivalence_Transitive _ _ _ e1 e2) a).
    reflexivity.
  - break_sf.
    transitivity (from (iso_of_eq (pf_anchor h (`1 a) (`2 a)))
                    ∘ to (iso_of_eq (pf_anchor f (`1 a) (`2 a)))).
    + apply (vfmap_cancel (pf_anchor f (`1 a) (`2 a))
               (pf_anchor g (`1 a) (`2 a)) (pf_anchor h (`1 a) (`2 a))).
      * exact (respi_to_over e1 a).
      * exact (respi_to_over e2 a).
    + symmetry.
      exact (respi_to_over (Equivalence_Transitive _ _ _ e1 e2) a).
Qed.

Lemma RT_id_natural {x : B} {a b : StrictFiber x} (k : a ~> b) :
  k ∘ to (idx_id_iso a)
    ≈ to (idx_id_iso b) ∘ fmap[Reindex (@id B x)] k.
Proof using Cl.
  apply (vunique (@id B x) (`1 a) (`2 a) (`1 b)).
  - break_sf.
    rewrite <- comp_assoc.
    rewrite (idi_to_comm a).
    rewrite id_right.
    rewrite <- comp_assoc.
    rewrite (reindex_comm (@id B x) k).
    rewrite comp_assoc.
    rewrite (idi_to_comm b).
    rewrite id_left.
    reflexivity.
  - break_sf.
    transitivity (from (iso_of_eq (`2 b))
                    ∘ to (iso_of_eq (pf_anchor (@id B x) (`1 a) (`2 a)))).
    + apply (vfmap_cancel (pf_anchor (@id B x) (`1 a) (`2 a))
               (`2 a) (`2 b)).
      * exact (idi_to_over a).
      * exact (`2 k).
    + symmetry.
      apply (vfmap_cancel (pf_anchor (@id B x) (`1 a) (`2 a))
               (pf_anchor (@id B x) (`1 b) (`2 b)) (`2 b)).
      * exact (reindex_over (@id B x) k).
      * exact (idi_to_over b).
Qed.

(*
 Naturality of the [g]-to-[f∘g] comparison [mg] in the fibre argument: the
 heart of the composition-iso naturality, proven by the universal property
 of the [g]-pushforward.  [mg] lies over [f], so the [over] branch carries
 an [f]-factor rather than a plain vertical cancellation. 

 --------
 纤维论中 [g] 到 [f∘g] 的比较 [mg] 的自然性：组合同构的核心自然性，由 [g] 推前的泛性质证明。[mg] 位于 [f] 之上，因此 [over] 分支携带一个 [f] 因子，而不是一个简单的垂直消去。
*)
Lemma mg_natural {x y z : B} (f : y ~> z) (g : x ~> y)
  {a b : StrictFiber x} (k : a ~> b) :
  `1 (fmap[Reindex (f ∘ g)] k) ∘ mg f g a
    ≈ mg f g b ∘ `1 (fmap[Reindex g] k).
Proof using Cl.
  apply (vunique g (`1 a) (`2 a) (pf_obj (f ∘ g) (`1 b) (`2 b))).
  - rewrite <- comp_assoc.
    rewrite (mgi_comm f g a).
    rewrite (reindex_comm (f ∘ g) k).
    rewrite <- comp_assoc.
    rewrite (reindex_comm g k).
    rewrite comp_assoc.
    rewrite (mgi_comm f g b).
    reflexivity.
  - transitivity (from (iso_of_eq (pf_anchor (f ∘ g) (`1 b) (`2 b)))
                    ∘ (f ∘ to (iso_of_eq (pf_anchor g (`1 a) (`2 a))))).
    + rewrite fmap_comp.
      rewrite (reindex_over (f ∘ g) k).
      rewrite (mgi_over f g a).
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (to (iso_of_eq (pf_anchor (f ∘ g) (`1 a) (`2 a))))).
      rewrite iso_to_from, id_left.
      reflexivity.
    + symmetry.
      rewrite fmap_comp.
      rewrite (mgi_over f g b).
      rewrite (reindex_over g k).
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (to (iso_of_eq (pf_anchor g (`1 b) (`2 b))))).
      rewrite iso_to_from, id_left.
      reflexivity.
Qed.

Lemma RT_comp_natural {x y z : B} (f : y ~> z) (g : x ~> y)
  {a b : StrictFiber x} (k : a ~> b) :
  fmap[Reindex (f ∘ g)] k ∘ to (idx_comp_iso f g a)
    ≈ to (idx_comp_iso f g b) ∘ fmap[Reindex f] (fmap[Reindex g] k).
Proof using Cl.
  apply (vunique f (pf_obj g (`1 a) (`2 a)) (pf_anchor g (`1 a) (`2 a))
           (pf_obj (f ∘ g) (`1 b) (`2 b))).
  - break_sf.
    rewrite <- comp_assoc.
    rewrite (compi_to_comm f g a).
    rewrite <- comp_assoc.
    rewrite (reindex_comm f (fmap[Reindex g] k)).
    rewrite comp_assoc.
    rewrite (compi_to_comm f g b).
    apply mg_natural.
  - break_sf.
    transitivity (from (iso_of_eq (pf_anchor (f ∘ g) (`1 b) (`2 b)))
                    ∘ to (iso_of_eq
                            (pf_anchor f (pf_obj g (`1 a) (`2 a))
                               (pf_anchor g (`1 a) (`2 a))))).
    + apply (vfmap_cancel
               (pf_anchor f (pf_obj g (`1 a) (`2 a))
                  (pf_anchor g (`1 a) (`2 a)))
               (pf_anchor (f ∘ g) (`1 a) (`2 a))
               (pf_anchor (f ∘ g) (`1 b) (`2 b))).
      * exact (compi_to_over f g a).
      * exact (reindex_over (f ∘ g) k).
    + symmetry.
      apply (vfmap_cancel
               (pf_anchor f (pf_obj g (`1 a) (`2 a))
                  (pf_anchor g (`1 a) (`2 a)))
               (pf_anchor f (pf_obj g (`1 b) (`2 b))
                  (pf_anchor g (`1 b) (`2 b)))
               (pf_anchor (f ∘ g) (`1 b) (`2 b))).
      * exact (reindex_over f (fmap[Reindex g] k)).
      * exact (compi_to_over f g b).
Qed.

(*
 Compatibility of [mg] with the ≈-mediator in the outer base argument: the
 [g]-pushforward level of [idx_comp_resp_l].  The [over] branch bridges [f]
 and [f'] through the ≈-witness [e]. 

 --------
 [mg] 与外部基参数中的 ≈-介体的兼容性：[idx_comp_resp_l] 的 [g] 推前水平。[over] 分支通过 ≈-见证 [e] 连接 [f] 和 [f']。
*)
Lemma mg_resp_l {x y z : B} {f f' : y ~> z} (g : x ~> y) (e : f ≈ f')
  (e' : f ∘ g ≈ f' ∘ g) (a : { e : E & P e = x }) :
  mg f' g a ≈ `1 (to (idx_resp_iso e' a)) ∘ mg f g a.
Proof using Cl.
  apply (vunique g (`1 a) (`2 a) (pf_obj (f' ∘ g) (`1 a) (`2 a))).
  - rewrite (mgi_comm f' g a).
    rewrite <- comp_assoc.
    rewrite (mgi_comm f g a).
    rewrite (respi_to_comm e' a).
    reflexivity.
  - transitivity (from (iso_of_eq (pf_anchor (f' ∘ g) (`1 a) (`2 a)))
                    ∘ (f' ∘ to (iso_of_eq (pf_anchor g (`1 a) (`2 a))))).
    + exact (mgi_over f' g a).
    + symmetry.
      rewrite fmap_comp.
      rewrite (respi_to_over e' a).
      rewrite (mgi_over f g a).
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (to (iso_of_eq (pf_anchor (f ∘ g) (`1 a) (`2 a))))).
      rewrite iso_to_from, id_left.
      rewrite e.
      reflexivity.
Qed.

Lemma RT_comp_resp_l {x y z : B} {f f' : y ~> z} (g : x ~> y) (e : f ≈ f')
  (e' : f ∘ g ≈ f' ∘ g) (a : { e : E & P e = x }) :
  to (idx_comp_iso f' g a) ∘ to (idx_resp_iso e (Reindex g a))
    ≈ to (idx_resp_iso e' a) ∘ to (idx_comp_iso f g a).
Proof using Cl.
  apply (vunique f (pf_obj g (`1 a) (`2 a)) (pf_anchor g (`1 a) (`2 a))
           (pf_obj (f' ∘ g) (`1 a) (`2 a))).
  - break_sf.
    rewrite <- comp_assoc.
    rewrite (respi_to_comm e (Reindex g a)).
    rewrite (compi_to_comm f' g a).
    rewrite <- comp_assoc.
    rewrite (compi_to_comm f g a).
    exact (mg_resp_l g e e' a).
  - break_sf.
    transitivity (from (iso_of_eq (pf_anchor (f' ∘ g) (`1 a) (`2 a)))
                    ∘ to (iso_of_eq
                            (pf_anchor f (pf_obj g (`1 a) (`2 a))
                               (pf_anchor g (`1 a) (`2 a))))).
    + apply (vfmap_cancel
               (pf_anchor f (pf_obj g (`1 a) (`2 a))
                  (pf_anchor g (`1 a) (`2 a)))
               (pf_anchor f' (pf_obj g (`1 a) (`2 a))
                  (pf_anchor g (`1 a) (`2 a)))
               (pf_anchor (f' ∘ g) (`1 a) (`2 a))).
      * exact (respi_to_over e (Reindex g a)).
      * exact (compi_to_over f' g a).
    + symmetry.
      apply (vfmap_cancel
               (pf_anchor f (pf_obj g (`1 a) (`2 a))
                  (pf_anchor g (`1 a) (`2 a)))
               (pf_anchor (f ∘ g) (`1 a) (`2 a))
               (pf_anchor (f' ∘ g) (`1 a) (`2 a))).
      * exact (compi_to_over f g a).
      * exact (respi_to_over e' a).
Qed.

(*
 Compatibility of [mg] with the ≈-mediator in the inner base argument: the
 [g]-pushforward level of [idx_comp_resp_r].  Both sides lie over the same
 [f], so no ≈-bridge is needed. 

 --------
 [mg] 与内基参数中的≈-介体的兼容性：[g] 的推前水平为 [idx_comp_resp_r]。双方位于相同的 [f] 上，因此不需要≈-桥。
*)
Lemma mg_resp_r {x y z : B} (f : y ~> z) {g g' : x ~> y} (e : g ≈ g')
  (e' : f ∘ g ≈ f ∘ g') (a : { e : E & P e = x }) :
  mg f g' a ∘ `1 (to (idx_resp_iso e a))
    ≈ `1 (to (idx_resp_iso e' a)) ∘ mg f g a.
Proof using Cl.
  apply (vunique g (`1 a) (`2 a) (pf_obj (f ∘ g') (`1 a) (`2 a))).
  - rewrite <- comp_assoc.
    rewrite (respi_to_comm e a).
    rewrite (mgi_comm f g' a).
    rewrite <- comp_assoc.
    rewrite (mgi_comm f g a).
    rewrite (respi_to_comm e' a).
    reflexivity.
  - transitivity (from (iso_of_eq (pf_anchor (f ∘ g') (`1 a) (`2 a)))
                    ∘ (f ∘ to (iso_of_eq (pf_anchor g (`1 a) (`2 a))))).
    + rewrite fmap_comp.
      rewrite (mgi_over f g' a).
      rewrite (respi_to_over e a).
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (to (iso_of_eq (pf_anchor g' (`1 a) (`2 a))))).
      rewrite iso_to_from, id_left.
      reflexivity.
    + symmetry.
      rewrite fmap_comp.
      rewrite (respi_to_over e' a).
      rewrite (mgi_over f g a).
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (to (iso_of_eq (pf_anchor (f ∘ g) (`1 a) (`2 a))))).
      rewrite iso_to_from, id_left.
      reflexivity.
Qed.

Lemma RT_comp_resp_r {x y z : B} (f : y ~> z) {g g' : x ~> y} (e : g ≈ g')
  (e' : f ∘ g ≈ f ∘ g') (a : { e : E & P e = x }) :
  to (idx_comp_iso f g' a) ∘ fmap[Reindex f] (to (idx_resp_iso e a))
    ≈ to (idx_resp_iso e' a) ∘ to (idx_comp_iso f g a).
Proof using Cl.
  apply (vunique f (pf_obj g (`1 a) (`2 a)) (pf_anchor g (`1 a) (`2 a))
           (pf_obj (f ∘ g') (`1 a) (`2 a))).
  - break_sf.
    rewrite <- comp_assoc.
    rewrite (reindex_comm f (to (idx_resp_iso e a))).
    rewrite comp_assoc.
    rewrite (compi_to_comm f g' a).
    rewrite <- comp_assoc.
    rewrite (compi_to_comm f g a).
    exact (mg_resp_r f e e' a).
  - break_sf.
    transitivity (from (iso_of_eq (pf_anchor (f ∘ g') (`1 a) (`2 a)))
                    ∘ to (iso_of_eq
                            (pf_anchor f (pf_obj g (`1 a) (`2 a))
                               (pf_anchor g (`1 a) (`2 a))))).
    + apply (vfmap_cancel
               (pf_anchor f (pf_obj g (`1 a) (`2 a))
                  (pf_anchor g (`1 a) (`2 a)))
               (pf_anchor f (pf_obj g' (`1 a) (`2 a))
                  (pf_anchor g' (`1 a) (`2 a)))
               (pf_anchor (f ∘ g') (`1 a) (`2 a))).
      * exact (reindex_over f (to (idx_resp_iso e a))).
      * exact (compi_to_over f g' a).
    + symmetry.
      apply (vfmap_cancel
               (pf_anchor f (pf_obj g (`1 a) (`2 a))
                  (pf_anchor g (`1 a) (`2 a)))
               (pf_anchor (f ∘ g) (`1 a) (`2 a))
               (pf_anchor (f ∘ g') (`1 a) (`2 a))).
      * exact (compi_to_over f g a).
      * exact (respi_to_over e' a).
Qed.

(*
 The [g]-pushforward level of the left unit coherence: reindexing along
 [id ∘ f] then correcting by the left-unit ≈-mediator returns the identity
 on the [f]-pushforward. 

 --------
 左单位相干性的 [g] 推前层次：沿着 [id ∘ f] 重新索引，然后通过左单位 ≈-调解器进行校正，会返回 [f] 推前上的恒等映射。
*)
Lemma mg_unit_left {x y : B} (f : x ~> y) (a : { e : E & P e = x }) :
  `1 (to (idx_resp_iso (id_left f) a)) ∘ mg (@id B y) f a ≈ id.
Proof using Cl.
  apply (vunique f (`1 a) (`2 a) (pf_obj f (`1 a) (`2 a))).
  - rewrite <- comp_assoc.
    rewrite (mgi_comm (@id B y) f a).
    rewrite (respi_to_comm (id_left f) a).
    now rewrite id_left.
  - rewrite fmap_id.
    rewrite fmap_comp.
    rewrite (respi_to_over (id_left f) a).
    rewrite (mgi_over (@id B y) f a).
    rewrite (id_left (to (iso_of_eq (pf_anchor f (`1 a) (`2 a))))).
    rewrite <- !comp_assoc.
    rewrite (comp_assoc
               (to (iso_of_eq (pf_anchor (@id B y ∘ f) (`1 a) (`2 a))))).
    rewrite iso_to_from, id_left.
    apply iso_from_to.
Qed.

Lemma RT_unit_left {x y : B} (f : x ~> y) (a : { e : E & P e = x }) :
  to (idx_resp_iso (id_left f) a) ∘ to (idx_comp_iso (@id B y) f a)
    ≈ to (idx_id_iso (Reindex f a)).
Proof using Cl.
  apply (vunique (@id B y) (pf_obj f (`1 a) (`2 a)) (pf_anchor f (`1 a) (`2 a))
           (pf_obj f (`1 a) (`2 a))).
  - break_sf.
    rewrite <- comp_assoc.
    rewrite (compi_to_comm (@id B y) f a).
    rewrite (idi_to_comm (Reindex f a)).
    exact (mg_unit_left f a).
  - break_sf.
    transitivity (from (iso_of_eq (pf_anchor f (`1 a) (`2 a)))
                    ∘ to (iso_of_eq
                            (pf_anchor (@id B y) (pf_obj f (`1 a) (`2 a))
                               (pf_anchor f (`1 a) (`2 a))))).
    + apply (vfmap_cancel
               (pf_anchor (@id B y) (pf_obj f (`1 a) (`2 a))
                  (pf_anchor f (`1 a) (`2 a)))
               (pf_anchor (@id B y ∘ f) (`1 a) (`2 a))
               (pf_anchor f (`1 a) (`2 a))).
      * exact (compi_to_over (@id B y) f a).
      * exact (respi_to_over (id_left f) a).
    + symmetry.
      exact (idi_to_over (Reindex f a)).
Qed.

(*
 The [id]-pushforward level of the right unit coherence: reindexing along
 [f ∘ id] then correcting by the right-unit ≈-mediator equals the
 [f]-pushforward precomposed with the unit iso. 

 --------
 右单位相干性的 [id] 推前层：沿着 [f ∘ id] 重新索引，然后通过右单位 ≈-中介进行校正，等于与单位同构预组合的 [f] 推前。
*)
Lemma mg_unit_right {x y : B} (f : x ~> y) (a : { e : E & P e = x }) :
  `1 (to (idx_resp_iso (id_right f) a)) ∘ mg f (@id B x) a
    ≈ pf_mor f (`1 a) (`2 a) ∘ `1 (to (idx_id_iso a)).
Proof using Cl.
  apply (vunique (@id B x) (`1 a) (`2 a) (pf_obj f (`1 a) (`2 a))).
  - rewrite <- comp_assoc.
    rewrite (mgi_comm f (@id B x) a).
    rewrite (respi_to_comm (id_right f) a).
    rewrite <- comp_assoc.
    rewrite (idi_to_comm a).
    now rewrite id_right.
  - transitivity (from (iso_of_eq (pf_anchor f (`1 a) (`2 a)))
                    ∘ (f ∘ to (iso_of_eq (pf_anchor (@id B x) (`1 a) (`2 a))))).
    + rewrite fmap_comp.
      rewrite (respi_to_over (id_right f) a).
      rewrite (mgi_over f (@id B x) a).
      rewrite <- !comp_assoc.
      rewrite (comp_assoc
                 (to (iso_of_eq (pf_anchor (f ∘ @id B x) (`1 a) (`2 a))))).
      rewrite iso_to_from, id_left.
      reflexivity.
    + symmetry.
      rewrite fmap_comp.
      rewrite (pf_over f (`1 a) (`2 a)).
      rewrite (idi_to_over a).
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (to (iso_of_eq (`2 a)))).
      rewrite iso_to_from, id_left.
      reflexivity.
Qed.

Lemma RT_unit_right {x y : B} (f : x ~> y) (a : { e : E & P e = x }) :
  to (idx_resp_iso (id_right f) a) ∘ to (idx_comp_iso f (@id B x) a)
    ≈ fmap[Reindex f] (to (RT_idx_id a)).
Proof using Cl.
  apply (vunique f (pf_obj (@id B x) (`1 a) (`2 a))
           (pf_anchor (@id B x) (`1 a) (`2 a)) (pf_obj f (`1 a) (`2 a))).
  - break_sf.
    rewrite <- comp_assoc.
    rewrite (compi_to_comm f (@id B x) a).
    rewrite (reindex_comm f (to (RT_idx_id a))).
    exact (mg_unit_right f a).
  - break_sf.
    transitivity (from (iso_of_eq (pf_anchor f (`1 a) (`2 a)))
                    ∘ to (iso_of_eq
                            (pf_anchor f (pf_obj (@id B x) (`1 a) (`2 a))
                               (pf_anchor (@id B x) (`1 a) (`2 a))))).
    + apply (vfmap_cancel
               (pf_anchor f (pf_obj (@id B x) (`1 a) (`2 a))
                  (pf_anchor (@id B x) (`1 a) (`2 a)))
               (pf_anchor (f ∘ @id B x) (`1 a) (`2 a))
               (pf_anchor f (`1 a) (`2 a))).
      * exact (compi_to_over f (@id B x) a).
      * exact (respi_to_over (id_right f) a).
    + symmetry.
      exact (reindex_over f (to (RT_idx_id a))).
Qed.

(*
 The [h]-pushforward level of the associativity cocycle: the two ways of
 nesting the [mg] comparisons agree after correcting by the associator
 ≈-mediator.  The [over] branch reassociates the base composite [(f∘g)∘_]
 against [f∘(g∘_)]. 

 --------
 结合性上同调的 [h] 推前水平：在通过结合子 ≈-中介修正后，嵌套 [mg] 比较的两种方式一致。[over] 分支将基复合 [(f∘g)∘_] 对 [f∘(g∘_)] 重新结合。
*)
Lemma mg_cocycle {w x y z : B} (f : y ~> z) (g : x ~> y) (h : w ~> x)
  (a : { e : E & P e = w }) :
  mg (f ∘ g) h a
    ≈ `1 (to (idx_resp_iso (comp_assoc f g h) a))
        ∘ (mg f (g ∘ h) a ∘ mg g h a).
Proof using Cl.
  apply (vunique h (`1 a) (`2 a) (pf_obj ((f ∘ g) ∘ h) (`1 a) (`2 a))).
  - rewrite (mgi_comm (f ∘ g) h a).
    rewrite <- (comp_assoc (`1 (to (idx_resp_iso (comp_assoc f g h) a)))
                 (mg f (g ∘ h) a ∘ mg g h a) (pf_mor h (`1 a) (`2 a))).
    rewrite <- (comp_assoc (mg f (g ∘ h) a) (mg g h a)
                 (pf_mor h (`1 a) (`2 a))).
    rewrite (mgi_comm g h a).
    rewrite (mgi_comm f (g ∘ h) a).
    rewrite (respi_to_comm (comp_assoc f g h) a).
    reflexivity.
  - transitivity (from (iso_of_eq (pf_anchor ((f ∘ g) ∘ h) (`1 a) (`2 a)))
                    ∘ ((f ∘ g)
                         ∘ to (iso_of_eq (pf_anchor h (`1 a) (`2 a))))).
    + exact (mgi_over (f ∘ g) h a).
    + symmetry.
      rewrite fmap_comp.
      rewrite fmap_comp.
      rewrite (respi_to_over (comp_assoc f g h) a).
      rewrite (mgi_over f (g ∘ h) a).
      rewrite (mgi_over g h a).
      rewrite <- (comp_assoc
                    (from (iso_of_eq (pf_anchor ((f ∘ g) ∘ h) (`1 a) (`2 a))))
                    (to (iso_of_eq (pf_anchor (f ∘ (g ∘ h)) (`1 a) (`2 a))))).
      rewrite <- (comp_assoc
                    (from (iso_of_eq (pf_anchor (f ∘ (g ∘ h)) (`1 a) (`2 a))))
                    (f ∘ to (iso_of_eq (pf_anchor (g ∘ h) (`1 a) (`2 a))))).
      rewrite (comp_assoc
                 (to (iso_of_eq (pf_anchor (f ∘ (g ∘ h)) (`1 a) (`2 a))))).
      rewrite iso_to_from, id_left.
      rewrite <- (comp_assoc f
                    (to (iso_of_eq (pf_anchor (g ∘ h) (`1 a) (`2 a))))).
      rewrite (comp_assoc
                 (to (iso_of_eq (pf_anchor (g ∘ h) (`1 a) (`2 a))))).
      rewrite iso_to_from, id_left.
      rewrite (comp_assoc f g (to (iso_of_eq (pf_anchor h (`1 a) (`2 a))))).
      reflexivity.
Qed.

(*
 The [over]-law of [mg] at a reindexed fibre object, restated so the anchor
 of the inner object appears in its [pf_obj]/[pf_anchor] normal form (rather
 than as [`1]/[`2] of [Reindex h a]); this is what makes the [iso_of_eq]
 cancellations in [RT_cocycle] match syntactically. 

 --------
 在重新索引的纤维对象上的 [mg] 定律 [over]，以这样一种方式重新表述：内部对象的锚出现在其 [pf_obj] / [pf_anchor] 正规形式中（而不是作为 [`1] / [`2] 的 [Reindex h a]）；这就是使 [RT_cocycle] 中的 [iso_of_eq] 消去在语法上匹配的原因。
*)
Lemma mgi_over_Rh {w x y z : B} (f : y ~> z) (g : x ~> y) (h : w ~> x)
  (a : { e : E & P e = w }) :
  fmap[P] (mg f g (Reindex h a))
    ≈ from (iso_of_eq
              (pf_anchor (f ∘ g) (pf_obj h (`1 a) (`2 a))
                 (pf_anchor h (`1 a) (`2 a))))
        ∘ (f ∘ to (iso_of_eq
                     (pf_anchor g (pf_obj h (`1 a) (`2 a))
                        (pf_anchor h (`1 a) (`2 a))))).
Proof using Cl. exact (mgi_over f g (Reindex h a)). Qed.

Lemma RT_cocycle {w x y z : B} (f : y ~> z) (g : x ~> y) (h : w ~> x)
  (a : { e : E & P e = w }) :
  to (idx_comp_iso (f ∘ g) h a) ∘ to (idx_comp_iso f g (Reindex h a))
    ≈ to (idx_resp_iso (comp_assoc f g h) a) ∘ to (idx_comp_iso f (g ∘ h) a)
        ∘ fmap[Reindex f] (to (idx_comp_iso g h a)).
Proof using Cl.
  apply (vunique f
           (pf_obj g (pf_obj h (`1 a) (`2 a)) (pf_anchor h (`1 a) (`2 a)))
           (pf_anchor g (pf_obj h (`1 a) (`2 a)) (pf_anchor h (`1 a) (`2 a)))
           (pf_obj ((f ∘ g) ∘ h) (`1 a) (`2 a))).
  - break_sf.
    rewrite <- (comp_assoc (`1 (to (idx_comp_iso (f ∘ g) h a)))
                 (`1 (to (idx_comp_iso f g (Reindex h a))))
                 (pf_mor f (pf_obj g (pf_obj h (`1 a) (`2 a))
                              (pf_anchor h (`1 a) (`2 a)))
                    (pf_anchor g (pf_obj h (`1 a) (`2 a))
                       (pf_anchor h (`1 a) (`2 a))))).
    rewrite (compi_to_comm f g (Reindex h a)).
    rewrite <- (comp_assoc
                 (`1 (to (idx_resp_iso (comp_assoc f g h) a))
                    ∘ `1 (to (idx_comp_iso f (g ∘ h) a)))
                 (`1 (fmap[Reindex f] (to (idx_comp_iso g h a))))
                 (pf_mor f (pf_obj g (pf_obj h (`1 a) (`2 a))
                              (pf_anchor h (`1 a) (`2 a)))
                    (pf_anchor g (pf_obj h (`1 a) (`2 a))
                       (pf_anchor h (`1 a) (`2 a))))).
    rewrite (reindex_comm f (to (idx_comp_iso g h a))).
    rewrite <- (comp_assoc
                 (`1 (to (idx_resp_iso (comp_assoc f g h) a)))
                 (`1 (to (idx_comp_iso f (g ∘ h) a)))
                 (pf_mor f (pf_obj (g ∘ h) (`1 a) (`2 a))
                    (pf_anchor (g ∘ h) (`1 a) (`2 a))
                    ∘ `1 (to (idx_comp_iso g h a)))).
    rewrite (comp_assoc (`1 (to (idx_comp_iso f (g ∘ h) a)))
               (pf_mor f (pf_obj (g ∘ h) (`1 a) (`2 a))
                  (pf_anchor (g ∘ h) (`1 a) (`2 a)))
               (`1 (to (idx_comp_iso g h a)))).
    rewrite (compi_to_comm f (g ∘ h) a).
    apply (vunique g (pf_obj h (`1 a) (`2 a)) (pf_anchor h (`1 a) (`2 a))
             (pf_obj ((f ∘ g) ∘ h) (`1 a) (`2 a))).
    + rewrite <- (comp_assoc (`1 (to (idx_comp_iso (f ∘ g) h a)))
                   (mg f g (Reindex h a))
                   (pf_mor g (pf_obj h (`1 a) (`2 a))
                      (pf_anchor h (`1 a) (`2 a)))).
      rewrite (mgi_comm f g (Reindex h a)).
      rewrite (compi_to_comm (f ∘ g) h a).
      rewrite <- (comp_assoc
                   (`1 (to (idx_resp_iso (comp_assoc f g h) a)))
                   (mg f (g ∘ h) a ∘ `1 (to (idx_comp_iso g h a)))
                   (pf_mor g (pf_obj h (`1 a) (`2 a))
                      (pf_anchor h (`1 a) (`2 a)))).
      rewrite <- (comp_assoc (mg f (g ∘ h) a)
                   (`1 (to (idx_comp_iso g h a)))
                   (pf_mor g (pf_obj h (`1 a) (`2 a))
                      (pf_anchor h (`1 a) (`2 a)))).
      rewrite (compi_to_comm g h a).
      exact (mg_cocycle f g h a).
    + transitivity (from (iso_of_eq (pf_anchor ((f ∘ g) ∘ h) (`1 a) (`2 a)))
                      ∘ (f ∘ to (iso_of_eq
                                   (pf_anchor g (pf_obj h (`1 a) (`2 a))
                                      (pf_anchor h (`1 a) (`2 a)))))).
      * rewrite fmap_comp.
        rewrite (compi_to_over (f ∘ g) h a).
        rewrite (mgi_over_Rh f g h a).
        rewrite <- (comp_assoc
                      (from (iso_of_eq (pf_anchor ((f ∘ g) ∘ h) (`1 a) (`2 a))))
                      (to (iso_of_eq
                             (pf_anchor (f ∘ g) (pf_obj h (`1 a) (`2 a))
                                (pf_anchor h (`1 a) (`2 a)))))).
        rewrite (comp_assoc
                   (to (iso_of_eq
                          (pf_anchor (f ∘ g) (pf_obj h (`1 a) (`2 a))
                             (pf_anchor h (`1 a) (`2 a)))))).
        rewrite iso_to_from, id_left.
        reflexivity.
      * symmetry.
        rewrite fmap_comp.
        rewrite fmap_comp.
        rewrite (respi_to_over (comp_assoc f g h) a).
        rewrite (mgi_over f (g ∘ h) a).
        rewrite (compi_to_over g h a).
        rewrite <- (comp_assoc
                      (from (iso_of_eq (pf_anchor ((f ∘ g) ∘ h) (`1 a) (`2 a))))
                      (to (iso_of_eq (pf_anchor (f ∘ (g ∘ h)) (`1 a) (`2 a))))).
        rewrite <- (comp_assoc
                      (from (iso_of_eq (pf_anchor (f ∘ (g ∘ h)) (`1 a) (`2 a))))
                      (f ∘ to (iso_of_eq (pf_anchor (g ∘ h) (`1 a) (`2 a))))).
        rewrite (comp_assoc
                   (to (iso_of_eq (pf_anchor (f ∘ (g ∘ h)) (`1 a) (`2 a))))).
        rewrite iso_to_from, id_left.
        rewrite <- (comp_assoc f
                      (to (iso_of_eq (pf_anchor (g ∘ h) (`1 a) (`2 a))))).
        rewrite (comp_assoc
                   (to (iso_of_eq (pf_anchor (g ∘ h) (`1 a) (`2 a))))).
        rewrite iso_to_from, id_left.
        reflexivity.
  - break_sf.
    transitivity (from (iso_of_eq (pf_anchor ((f ∘ g) ∘ h) (`1 a) (`2 a)))
                    ∘ to (iso_of_eq
                            (pf_anchor f
                               (pf_obj g (pf_obj h (`1 a) (`2 a))
                                  (pf_anchor h (`1 a) (`2 a)))
                               (pf_anchor g (pf_obj h (`1 a) (`2 a))
                                  (pf_anchor h (`1 a) (`2 a)))))).
    + apply (vfmap_cancel
               (pf_anchor f
                  (pf_obj g (pf_obj h (`1 a) (`2 a)) (pf_anchor h (`1 a) (`2 a)))
                  (pf_anchor g (pf_obj h (`1 a) (`2 a))
                     (pf_anchor h (`1 a) (`2 a))))
               (pf_anchor (f ∘ g) (pf_obj h (`1 a) (`2 a))
                  (pf_anchor h (`1 a) (`2 a)))
               (pf_anchor ((f ∘ g) ∘ h) (`1 a) (`2 a))).
      * exact (compi_to_over f g (Reindex h a)).
      * exact (compi_to_over (f ∘ g) h a).
    + symmetry.
      apply (vfmap_cancel
               (pf_anchor f
                  (pf_obj g (pf_obj h (`1 a) (`2 a)) (pf_anchor h (`1 a) (`2 a)))
                  (pf_anchor g (pf_obj h (`1 a) (`2 a))
                     (pf_anchor h (`1 a) (`2 a))))
               (pf_anchor f (pf_obj (g ∘ h) (`1 a) (`2 a))
                  (pf_anchor (g ∘ h) (`1 a) (`2 a)))
               (pf_anchor ((f ∘ g) ∘ h) (`1 a) (`2 a))).
      * exact (reindex_over f (to (idx_comp_iso g h a))).
      * apply (vfmap_cancel
                 (pf_anchor f (pf_obj (g ∘ h) (`1 a) (`2 a))
                    (pf_anchor (g ∘ h) (`1 a) (`2 a)))
                 (pf_anchor (f ∘ (g ∘ h)) (`1 a) (`2 a))
                 (pf_anchor ((f ∘ g) ∘ h) (`1 a) (`2 a))).
        -- exact (compi_to_over f (g ∘ h) a).
        -- exact (respi_to_over (comp_assoc f g h) a).
Qed.

(* ---- assembling the indexed category ---- / ---- 正在组装索引类别 ---- *)

Definition RT_Indexed : IndexedCat B := {|
  idx_fib := StrictFiber;
  idx_map := @Reindex;
  idx_resp := @idx_resp_iso;
  idx_resp_natural := @RT_resp_natural;
  idx_resp_id := @RT_resp_id;
  idx_resp_trans := @RT_resp_trans;
  idx_id := @RT_idx_id;
  idx_id_natural := @RT_id_natural;
  idx_comp := @idx_comp_iso;
  idx_comp_natural := @RT_comp_natural;
  idx_comp_resp_l := @RT_comp_resp_l;
  idx_comp_resp_r := @RT_comp_resp_r;
  idx_unit_left := @RT_unit_left;
  idx_unit_right := @RT_unit_right;
  idx_cocycle := @RT_cocycle
|}.

(*
 ---- the comparison functor back to the total category E ---- 

 --------
 ---- 将比较函子回到总范畴 E ----
*)

(*
 An object of the Grothendieck construction of [RT_Indexed] over [x] is a
 strict fibre object [(e; p)] with [P e = x]; the comparison sends it to
 the carrier [e].  A morphism [(f; k)] with [f : x ~> y] and
 [k : Reindex f a ~> b] is sent to the vertical part [`1 k] precomposed
 with the chosen lift [pf_mor f], recovering an [E]-morphism [`1 a ~> `1 b]. 

 --------
 一个在  [x] 上的 [RT_Indexed] 的 Grothendieck 构造的对象是一个严格的纤维对象 [(e; p)]，具有 [P e = x]；比较将它发送到承载者 [e]。一个具有 [f : x ~> y] 和 [k : Reindex f a ~> b] 的态射 [(f; k)] 被发送到先与所选提升 [pf_mor f] 复合的垂直部分 [`1 k]，从而恢复一个 [E]-态射 [`1 a ~> `1 b]。
*)
Program Definition RT_Comparison : Grothendieck RT_Indexed ⟶ E := {|
  fobj := fun o => `1 (`2 o);
  fmap := fun o1 o2 m => `1 (`2 m) ∘ pf_mor (`1 m) (`1 (`2 o1)) (`2 (`2 o1))
|}.
Next Obligation.
  (*
 fmap respects ≈: the transport mediator splits back into the two lifts 

 --------
 fmap 遵守 ≈：传输中介分裂回两个提升
*)
  intros o1 o2 m m' [ε Hε].
  change (`1 (`2 m) ∘ `1 (from (idx_resp_iso ε (`2 o1))) ≈ `1 (`2 m')) in Hε.
  rewrite <- Hε.
  rewrite <- comp_assoc.
  now rewrite (respi_from_comm ε (`2 o1)).
Qed.
Next Obligation.
  (* identities: the unit iso cancels its lift / 身份：单位 iso 取消了它的升力 *)
  intros o.
  exact (idi_to_comm (`2 o)).
Qed.
Next Obligation.
  (*
 composition: the compositor's inverse rebuilds the two-step lift, then
 the reindexed leg is natural against [pf_mor] 

 --------
 作曲：排版者的逆过程重建了两步提升，然后重新索引的腿自然地对应于 [pf_mor]
*)
  intros [x a] [y b] [z c] [f k] [g l]; simpl.
  break_sf.
  rewrite <- !comp_assoc.
  rewrite (compi_from_comm f g a).
  rewrite (comp_assoc (`1 (fmap[Reindex f] l))
            (pf_mor f (`1 (Reindex g a)) (`2 (Reindex g a)))
            (pf_mor g (`1 a) (`2 a))).
  rewrite (reindex_comm f l).
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(*
 The image under [P] of a comparison morphism is the base morphism [`1 m]
 conjugated by the anchoring isomorphisms: the vertical part contributes an
 anchor-cancelling factor, and the chosen lift contributes [`1 m] itself.
 This is the naturality square of the isomorphism [P ◯ RT_Comparison ≅
 Grothendieck_Proj], and the workhorse for both fullness and faithfulness. 

 --------
 在 [P] 下，一个比较态射的像是由锚定同构共轭的基态射 [`1 m]：垂直部分贡献了一个锚点抵消因子，而所选择的提升贡献了 [`1 m] 本身。这是同构 [P ◯ RT_Comparison ≅ Grothendieck_Proj] 的自然性方图，同时也是证明充满性和忠实性的核心工具。
*)
Lemma RT_Comparison_over {o1 o2 : Grothendieck RT_Indexed}
  (m : o1 ~> o2) :
  fmap[P] (fmap[RT_Comparison] m)
    ≈ from (iso_of_eq (`2 (`2 o2)))
        ∘ (`1 m ∘ to (iso_of_eq (`2 (`2 o1)))).
Proof using Cl.
  simpl.
  rewrite fmap_comp.
  rewrite (pf_over (`1 m) (`1 (`2 o1)) (`2 (`2 o1))).
  rewrite (`2 (`2 m)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc
             (to (iso_of_eq (pf_anchor (`1 m) (`1 (`2 o1)) (`2 (`2 o1)))))
             (from (iso_of_eq (pf_anchor (`1 m) (`1 (`2 o1)) (`2 (`2 o1)))))).
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(*
 Inverting the naturality square: the base morphism is recovered from the
 [P]-image of its comparison morphism by conjugating the other way. 

 --------
 反转自然性方：通过以相反的方式共轭比较态射的 [P] 像，可以恢复基态射。
*)
Lemma RT_base_recover {o1 o2 : Grothendieck RT_Indexed}
  (m : o1 ~> o2) :
  `1 m ≈ to (iso_of_eq (`2 (`2 o2)))
          ∘ fmap[P] (fmap[RT_Comparison] m)
          ∘ from (iso_of_eq (`2 (`2 o1))).
Proof using Cl.
  rewrite (RT_Comparison_over m).
  rewrite (comp_assoc (to (iso_of_eq (`2 (`2 o2))))
                      (from (iso_of_eq (`2 (`2 o2))))).
  rewrite iso_to_from, id_left.
  rewrite <- comp_assoc.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(*
 Deliverable: [P] after the comparison is the Grothendieck projection, up
 to the natural isomorphism whose components are the anchoring isos. 

 --------
 可交付成果：比较后的 [P] 是 Grothendieck 投影，至于自然同构，其分量是锚定同构。
*)
Definition RT_Comparison_Proj :
  P ◯ RT_Comparison ≈ Grothendieck_Proj RT_Indexed.
Proof.
  exists (fun o => iso_of_eq (`2 (`2 o))).
  intros o1 o2 m.
  rewrite <- (comp_assoc (from (iso_of_eq (`2 (`2 o2)))) (`1 m)
             (to (iso_of_eq (`2 (`2 o1))))).
  exact (RT_Comparison_over m).
Defined.

(* ---- the comparison is fully faithful ---- / ---- 比较是完全忠实的 ---- *)

(*
 Faithfulness: two comparison morphisms with equal image have equal base
 components (recovered through [RT_base_recover]) and equal vertical parts
 (by joint monicity of the lift, [vunique], with the transport mediator
 supplying the base agreement). 

 --------
 忠实性：两个具有相同像的比较态射的基分量相等（通过 [RT_base_recover] 恢复）且垂直部分相等（由提升的联合单性 [vunique] 与传输中介提供的基一致性保证）。
*)
Definition RT_Faithful : Faithful RT_Comparison.
Proof.
  constructor.
  intros o1 o2 m m' H.
  assert (ε : `1 m ≈ `1 m').
  { rewrite (RT_base_recover m), (RT_base_recover m').
    now rewrite H. }
  exists ε.
  change (`1 (`2 m) ∘ `1 (from (idx_resp_iso ε (`2 o1))) ≈ `1 (`2 m')).
  apply (vunique (`1 m') (`1 (`2 o1)) (`2 (`2 o1)) (`1 (`2 o2))).
  - rewrite <- comp_assoc.
    rewrite (respi_from_comm ε (`2 o1)).
    exact H.
  - rewrite fmap_comp.
    rewrite (`2 (`2 m)).
    rewrite (respi_from_over ε (`2 o1)).
    rewrite (`2 (`2 m')).
    rewrite <- !comp_assoc.
    rewrite (comp_assoc
               (to (iso_of_eq (pf_anchor (`1 m) (`1 (`2 o1)) (`2 (`2 o1)))))
               (from (iso_of_eq (pf_anchor (`1 m) (`1 (`2 o1)) (`2 (`2 o1)))))).
    rewrite iso_to_from, id_left.
    reflexivity.
Qed.

(* ---- the comparison is full ---- / ---- 比较已满 ---- *)

(*
 Given an [E]-morphism [h : `1 a ~> `1 b] between the carriers, its
 preimage in the Grothendieck construction is built from the opcartesian
 universal property: the base leg is [h] transported across the anchoring
 isos, and the vertical leg is the unique factorization of [h] through the
 chosen lift. 

 --------
 给定载体之间的一个 [E]-态射 [h : `1 a ~> `1 b]，它在 Grothendieck 构造中的原像是通过上对笛卡尔（opcartesian）的普遍性质构建的：基底腿是 [h] 经过锚定同构（anchoring isos）传送的，垂直腿是 [h] 通过所选择的提升（lift）的唯一分解。
*)
Section Fullness.
Context {o1 o2 : Grothendieck RT_Indexed}.
Context (h : `1 (`2 o1) ~> `1 (`2 o2)).

Definition full_base : `1 o1 ~> `1 o2 :=
  to (iso_of_eq (`2 (`2 o2)))
    ∘ fmap[P] h ∘ from (iso_of_eq (`2 (`2 o1))).

Lemma full_fac :
  fmap[P] h
    ≈ (from (iso_of_eq (`2 (`2 o2)))
        ∘ to (iso_of_eq (pf_anchor full_base (`1 (`2 o1)) (`2 (`2 o1)))))
      ∘ fmap[P] (pf_mor full_base (`1 (`2 o1)) (`2 (`2 o1))).
Proof using Cl.
  rewrite (pf_over full_base (`1 (`2 o1)) (`2 (`2 o1))).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc
             (to (iso_of_eq (pf_anchor full_base (`1 (`2 o1)) (`2 (`2 o1)))))
             (from (iso_of_eq (pf_anchor full_base (`1 (`2 o1)) (`2 (`2 o1)))))).
  rewrite iso_to_from, id_left.
  unfold full_base.
  rewrite <- !comp_assoc.
  rewrite iso_from_to.
  rewrite id_right.
  rewrite comp_assoc.
  rewrite iso_from_to, id_left.
  reflexivity.
Qed.

Definition full_u :=
  pf_ump full_base (`1 (`2 o1)) (`2 (`2 o1)) h
    (from (iso_of_eq (`2 (`2 o2)))
      ∘ to (iso_of_eq (pf_anchor full_base (`1 (`2 o1)) (`2 (`2 o1)))))
    full_fac.

Definition full_lift :
  pf_obj full_base (`1 (`2 o1)) (`2 (`2 o1)) ~> `1 (`2 o2) :=
  unique_obj full_u.

Lemma full_lift_comm :
  full_lift ∘ pf_mor full_base (`1 (`2 o1)) (`2 (`2 o1)) ≈ h.
Proof using Cl. exact (fst (unique_property full_u)). Qed.

Lemma full_lift_over :
  fmap[P] full_lift
    ≈ from (iso_of_eq (`2 (`2 o2)))
        ∘ to (iso_of_eq (pf_anchor full_base (`1 (`2 o1)) (`2 (`2 o1)))).
Proof using Cl. exact (snd (unique_property full_u)). Qed.

Definition full_preimage : o1 ~{ Grothendieck RT_Indexed }~> o2 :=
  (full_base; (full_lift; full_lift_over)).

Lemma full_sur : fmap[RT_Comparison] full_preimage ≈ h.
Proof using Cl. exact full_lift_comm. Qed.

End Fullness.

Definition RT_Full : Full RT_Comparison :=
  @Build_Full _ _ RT_Comparison
    (fun o1 o2 h => @full_preimage o1 o2 h)
    (fun o1 o2 h => @full_sur o1 o2 h).

(*
 ---- the comparison is essentially (indeed strictly) surjective ---- 

 --------
 ---- 这个比较本质上（确实严格地）是满射的 ----
*)

(*
 Every carrier [d : E] is the image of the strict fibre object [(d; eq_refl)]
 over [P d]: [RT_Comparison (P d; (d; eq_refl))] reduces to [d] on the nose,
 so the witnessing isomorphism is the identity. 

 --------
 每一个载体 [d : E] 都是严格纤维对象 [(d; eq_refl)] 在 [P d] 上的像：[RT_Comparison (P d; (d; eq_refl))] 精确地化简为 [d]，因此所见的同构是恒等映射。
*)
Definition RT_EssSurj : EssentiallySurjective RT_Comparison :=
  @Build_EssentiallySurjective _ _ RT_Comparison
    (fun d => (P d; (d; eq_refl)))
    (fun d => @iso_id E d).

(* ---- the comparison is an equivalence of categories ---- / ---- 比较是类别的等价 ---- *)

(*
 Assembled from the full + faithful + essentially-surjective
 characterization (Theory/Equivalence/FullFaithful.v). 

 --------
 从完全 + 忠实 + 本质上满射的刻画（Theory/Equivalence/FullFaithful.v）组装而成。
*)
Definition RT_Equivalence : EquivalenceOfCategories RT_Comparison :=
  @FF_ESO_Equivalence _ _ RT_Comparison RT_Full RT_Faithful RT_EssSurj.

End RoundTrip.

(*
   * ** The named deliverables

   The split cleaving is consumed only through its underlying cloven
   fibration [Cl] (see the header): the coherence of [IndexedCat] is
   iso-valued, so the opcartesian universal property already discharges
   every pseudofunctor law, and strictness of the cleaving is not needed. 

   --------
   * ** 指定的可交付成果

   分裂的拆分仅通过其底层的劈分纤维 [Cl]（见标题）来消耗：[IndexedCat] 的相干性是同值的，因此 opcartesian 泛性质已经满足了每条伪函子定律，而且不需要拆分的严格性。
*)

(*
 (a) The indexed category built from a split cleaving of [P]. 

 --------
 (a) 从 [P] 的分裂切割构建的索引范畴。
*)
Definition IndexedCat_of_SplitCleaving {E B : Category} (P : E ⟶ B)
  {Cl : ClovenFibration (P^op)}
  (Sp : @SplitCleaving (B^op) (E^op) (P^op) Cl) : IndexedCat B :=
  @RT_Indexed E B P Cl.

(*
 (b) The comparison functor from the Grothendieck construction of the
 round trip back to the total category [E]. 

 --------
 (b) 从 Grothendieck 构造的比较函子回到总范畴 [E] 的往返。
*)
Definition RoundTrip_Comparison {E B : Category} (P : E ⟶ B)
  {Cl : ClovenFibration (P^op)}
  (Sp : @SplitCleaving (B^op) (E^op) (P^op) Cl) :
  Grothendieck (IndexedCat_of_SplitCleaving P Sp) ⟶ E :=
  @RT_Comparison E B P Cl.

(*
 The comparison lies over the projection: [P] after it is the Grothendieck
 projection, up to the natural iso whose components are the anchoring isos. 

 --------
 比较在于投影：[P] 之后是Grothendieck投影，直到其分量是锚定同构的自然同构。
*)
Definition RoundTrip_Comparison_Proj {E B : Category} (P : E ⟶ B)
  {Cl : ClovenFibration (P^op)}
  (Sp : @SplitCleaving (B^op) (E^op) (P^op) Cl) :
  P ◯ RoundTrip_Comparison P Sp
    ≈ Grothendieck_Proj (IndexedCat_of_SplitCleaving P Sp) :=
  @RT_Comparison_Proj E B P Cl.

(* The comparison is full. / 比较是完整的。 *)
Definition RoundTrip_Full {E B : Category} (P : E ⟶ B)
  {Cl : ClovenFibration (P^op)}
  (Sp : @SplitCleaving (B^op) (E^op) (P^op) Cl) :
  Full (RoundTrip_Comparison P Sp) :=
  @RT_Full E B P Cl.

(* The comparison is faithful. / 这个比较是忠实的。 *)
Definition RoundTrip_Faithful {E B : Category} (P : E ⟶ B)
  {Cl : ClovenFibration (P^op)}
  (Sp : @SplitCleaving (B^op) (E^op) (P^op) Cl) :
  Faithful (RoundTrip_Comparison P Sp) :=
  @RT_Faithful E B P Cl.

(* (c) The comparison is an equivalence of categories. / (c) 该比较是范畴的等价。 *)
Definition RoundTrip_Equivalence {E B : Category} (P : E ⟶ B)
  {Cl : ClovenFibration (P^op)}
  (Sp : @SplitCleaving (B^op) (E^op) (P^op) Cl) :
  EquivalenceOfCategories (RoundTrip_Comparison P Sp) :=
  @RT_Equivalence E B P Cl.

(*
   * ** The cloven-only deliverables

   The split-cleaving argument [Sp] on the deliverables above is inert.
   Every lemma feeding the round trip is proved [using Cl], the underlying
   cloven fibration: [IndexedCat]'s coherence is iso-valued, so the
   opcartesian universal property already discharges each pseudofunctor law
   (see the header, point 2), and splitness is never consumed.  The two
   definitions below restate the comparison and its equivalence over a bare
   [ClovenFibration (P^op)], with no splitness hypothesis.  The
   [SplitCleaving]-typed [RoundTrip_Comparison] and [RoundTrip_Equivalence]
   above are then immediate corollaries, retained for API alignment with the
   split-cleaving entry point. 

   --------
   * ** 仅分裂的可交付成果

   上述可交付成果上的分裂劈裂论证 [Sp] 是惰性的。
   每个用于往返转换的引理都已被证明 [using Cl]，其底层
   分裂纤维化：[IndexedCat] 的相干性是同构值的，因此
   伴随笛卡尔泛性质已经满足了每个伪函子定律
   （参见标题，第2点），并且分裂性从未被消耗。下面的两个
   定义重述了在没有任何分裂假设的裸 [ClovenFibration (P^op)] 上的比较及其等价性。
   上述 [SplitCleaving] 类型的 [RoundTrip_Comparison] 和 [RoundTrip_Equivalence]
   随后成为直接推论，为了与分裂劈裂入口点的 API 对齐而保留。
*)

(*
 The comparison functor, needing only a cloven structure on [P^op]. 

 --------
 比较函子，仅需在 [P^op] 上有一个分裂结构。
*)
Definition RoundTrip_Comparison_cloven {E B : Category} (P : E ⟶ B)
  (Cl : ClovenFibration (P^op)) :
  Grothendieck (@RT_Indexed E B P Cl) ⟶ E :=
  @RT_Comparison E B P Cl.

(*
 The comparison is an equivalence of categories, from a cloven structure
 alone. 

 --------
 这种比较仅仅是一种有分裂结构的范畴等价。
*)
Definition RoundTrip_Equivalence_cloven {E B : Category} (P : E ⟶ B)
  (Cl : ClovenFibration (P^op)) :
  EquivalenceOfCategories (RoundTrip_Comparison_cloven P Cl) :=
  @RT_Equivalence E B P Cl.

