Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Homotopy.

Generalizable All Variables.

(* * * The wedge sum is the coproduct in Top∗ / * * 楔和是 Top∗ 中的余积 *)

(*
 Book: Mac Lane, “Categories for the Working Mathematician” (2nd ed.),
 §III.3, book p. 63 (maclane:III.3:remark1)
 Book: Awodey, “Category Theory” (1st ed., CMU pre-print, Sept 2005),
 §3.2, Example 3.6, printed p. 62 (awodey:3.2:example6) — the
 “rooted posets by basepoint identification” clause, here for
 pointed spaces
 Wikipedia: https://en.wikipedia.org/wiki/Wedge_sum

 The last of Mac Lane's four topological/algebraic roster entries: in
 the category of pointed spaces the coproduct is the wedge sum, the
 disjoint union with the two basepoints identified.

 THE CONSTRUCTION, AND WHY THE GLUING CLAUSE COMES BACK.
 Instance/Top/Coproduct.v could DROP the respect-the-gluing clause that
 Instance/Top.v's cokernel-pair topology carries, because over the sum
 setoid equivalent points always lie in the same summand.  Here they do
 not: [wedge_rel] identifies [inl (pt X)] with [inr (pt Y)], so the
 clause returns and [wedge_open] is the full triple — the same shape as
 [CP_open] (Instance/Top.v), with a different relation.  That is the
 whole difference between the two files' topologies, and it is the
 reason the pointed coproduct is not simply the unpointed one with a
 basepoint chosen.

 WHAT IS PROVED, AND AT WHAT STRENGTH.  [Top_pointed_Cocartesian] is
 [@Cocartesian Top_pointed] — the tree's first (co)product structure of
 any kind on the pointed category, [Instance/Top/Homotopy.v] registering
 none.  The injections and the copairing are the evident maps at LEIBNIZ
 EQUALITY ([Wedge_inl_is_inl] and siblings, [eq_refl]), and so is the
 carrier ([Wedge_carrier_eq]).  The identification the construction
 exists for is proved rather than assumed: [wedge_basepoints_identified]
 shows the two injections AGREE at the basepoints, and — the contrast
 that makes it content — [wedge_is_not_sum] exhibits a pointed space
 where the corresponding two points of the UNPOINTED coproduct
 [Instance/Top/Coproduct.v]'s [Sum_Top] are provably distinct.  So the
 wedge genuinely glues, and the two roster entries are different
 objects, not one object read twice.

 Non-degeneracy also on the other side: [wedge_non_basepoints_differ]
 shows that away from the basepoints nothing else is identified, over a
 two-point space built from Instance/Top/Coproduct.v's own [Sum_Top] so
 that no new space has to be constructed.

 A NAMING NOTE.  The wedge object is [WedgeSum], not [Wedge]:
 Structure/Wedge.v already exports a [Class Wedge] — the wedge of a
 profunctor, from the end calculus — and the two would be ambiguous in
 any scope importing both, including the [print-assumptions] audit file,
 which imports enough of the tree to reach Structure/Coend.v.  Nothing
 else in this file collides; the [wedge_*] and [WedgeSum_*] families are
 unused elsewhere.

 UNIVERSES, MEASURED.  [WedgeSum@{u u0} : PointedTop@{u} →
 PointedTop@{u0} → PointedTop@{u}] carries [u = u0], for the same
 reason as Instance/Top/Coproduct.v's [Sum_Top]: the glued carrier is a
 single [SetoidObject@{o o}].  No [Set] appears in this file's
 constraint blocks.

 WHAT IS NOT DELIVERED.  No initial or terminal object of [Top_pointed]
 is built here, so the wedge's unit laws — [coprod_zero_l] and
 [coprod_zero_r] of Structure/Cocartesian.v, which would say the
 one-point space is the unit — are NOT available, unlike in
 Instance/Top/Coproduct.v where Instance/Top.v's [Top_Initial] supplies
 them; [coprod_comm] and [coprod_assoc], which need only the
 cocartesian structure, ARE exhibited.  No smash product, no reduced
 suspension, no products of pointed spaces, and nothing about
 [Instance/Top/Homotopy.v]'s [Toph_pointed] — the wedge is built in
 [Top_pointed], and whether it descends to the based-homotopy quotient
 is not investigated.  Awodey's rooted-poset clause is not formalized:
 this is the pointed-SPACE reading of the same idea. 

 --------
 书籍：Mac Lane，《为工作的数学家准备的范畴论》（第2版），
 第III.3节，书第63页（maclane:III.3:remark1）
 书籍：Awodey，《范畴论》（第1版，CMU预印本，2005年9月），
 第3.2节，例3.6，印刷第62页（awodey:3.2:example6）——“通过基点识别的有根偏序集合”条款，这里用于有基空间
 维基百科：https://en.wikipedia.org/wiki/Wedge_sum

 Mac Lane的四个拓扑/代数条目中的最后一个：在有基空间范畴中，余积是楔和，即通过将两个基点识别而得到的析离并构造，以及为什么粘合条款会返回。Instance/Top/Coproduct.v 可能会去掉 Instance/Top.v 的余核对拓扑所携带的尊重粘合条款，因为在和集合的等价点总是位于同一个直和分量中。但在这里情况并非如此：[wedge_rel] 识别了 [inl (pt X)] 与 [inr (pt Y)]，所以该条款返回，并且 [wedge_open] 是完整的三元组——与 [CP_open]（Instance/Top.v）的形状相同，只是关系不同。这就是两个文件拓扑之间的全部差异，也是指出的余积不仅仅是选定一个基点的无基点余积的原因。什么被证明，以及以何种强度证明。[Top_pointed_Cocartesian] 是 [@Cocartesian Top_pointed] —— 树在有尖点范畴上任意类型的第一个（共）积结构，[Instance/Top/Homotopy.v] 则没有记录。注入和共配对是在莱布尼茨等式（[Wedge_inl_is_inl] 及其同类，[eq_refl]）下显而易见的映射，载体（[Wedge_carrier_eq]）也是如此。构造存在的识别是被证明的，而不是假定的：[wedge_basepoints_identified] 显示两个注入在基点处一致，而——使其有内容的对比——[wedge_is_not_sum] 展示了一个尖点空间，在那里非尖点余积 [Instance/Top/Coproduct.v] 的 [Sum_Top] 对应的两个点可被证明是不同的。因此，楔积真正地粘合起来，而两个花名册条目是不同的对象，而不是同一个对象被读取两次。非退化性也在另一边：[wedge_non_basepoints_differ] 表明，远离基点时没有其他被识别的内容，在由 Instance/Top/Coproduct.v 自身的 [Sum_Top] 构建的两点空间上，因此无需构建新空间。

 命名注释。楔对象是 [WedgeSum]，而不是 [Wedge]：Structure/Wedge.v 已经导出一个 [Class Wedge] —— 来自端计算的 pro-functor 的楔——在导入两者的任何作用域中，这两者都会产生歧义，包括 [print-assumptions] 审计文件，该文件导入了足够的树以到达 Structure/Coend.v。此文件中的其他内容没有冲突；[wedge_*] 和 [WedgeSum_*] 系列在其他地方未使用。宇宙，被测量。[WedgeSum@{u u0} : PointedTop@{u} → PointedTop@{u0} → PointedTop@{u}] 承载 [u = u0]，原因与 Instance/Top/Coproduct.v 中的 [Sum_Top] 相同：粘合的承载是一个单独的 [SetoidObject@{o o}]。此文件的约束块中没有出现 [Set]。没有交付的内容。这里没有构建 [Top_pointed] 的初始或终端对象，因此楔形的单位律——Structure/Cocartesian.v 中的 [coprod_zero_l] 和 [coprod_zero_r]，它们会说明单点空间是单位——不可用，这与 Instance/Top/Coproduct.v 中 Instance/Top.v 的 [Top_Initial] 提供的情况不同；只需要余笛卡尔结构的 [coprod_comm] 和 [coprod_assoc] 已经展示。没有 smash 积，没有约化悬挂，没有有基空间的乘积，也没有关于 [Instance/Top/Homotopy.v] 的 [Toph_pointed] 的内容——楔形在 [Top_pointed] 中构建，其是否降到基点同伦商上没有被研究。Awodey 的根序集条款没有形式化：这是同一思想的有基空间解读。
*)

(** ** The glued carrier / ** 粘合载体 *)

Section WedgeSum.

Context (X Y : PointedTop).

Definition wpoint : Type :=
  (carrier (top_carrier (ptop_space X))
     + carrier (top_carrier (ptop_space Y)))%type.

(* Two points are identified when they agree inside a summand, or when both are basepoints. / 当两个点在加数内部一致时，或者当它们都是基点时，就确定这两个点。 *)
Definition wedge_rel (u v : wpoint) : Type :=
  match u, v with
  | Datatypes.inl a, Datatypes.inl a' => a ≈ a'
  | Datatypes.inr b, Datatypes.inr b' => b ≈ b'
  | Datatypes.inl a, Datatypes.inr b' =>
      ((a ≈ ptop_pt X) ∧ (b' ≈ ptop_pt Y))%type
  | Datatypes.inr b, Datatypes.inl a' =>
      ((b ≈ ptop_pt Y) ∧ (a' ≈ ptop_pt X))%type
  end.

Lemma wedge_rel_Equivalence : Equivalence wedge_rel.
Proof.
  constructor.
  - intros [a|a]; simpl; reflexivity.
  - intros [a|a] [b|b] H; simpl in *.
    + now symmetry.
    + exact (snd H, fst H).
    + exact (snd H, fst H).
    + now symmetry.
  - intros [a|a] [b|b] [c|c] H1 H2; simpl in *.
    + now transitivity b.
    + exact (transitivity H1 (fst H2), snd H2).
    + transitivity (ptop_pt X);
        [ exact (fst H1) | symmetry; exact (snd H2) ].
    + exact (fst H1, transitivity (symmetry H2) (snd H1)).
    + exact (fst H1, transitivity (symmetry H2) (snd H1)).
    + transitivity (ptop_pt Y);
        [ exact (fst H1) | symmetry; exact (snd H2) ].
    + exact (transitivity H1 (fst H2), snd H2).
    + now transitivity b.
Qed.

Definition wedge_setoid : Setoid wpoint := {|
  equiv := wedge_rel;
  setoid_equiv := wedge_rel_Equivalence
|}.

Definition wedge_carrier : SetoidObject := {|
  carrier := wpoint;
  is_setoid := wedge_setoid
|}.

(** ** The quotient topology / ** 商拓扑 *)

(* The [CP_open] shape of Instance/Top.v: a respect-the-gluing clause plus the two restrictions. / Instance/Top.v 的 [CP_open] 形状：一个遵守粘合条款的条款加上两个限制。 *)
Definition wedge_open (W : wedge_carrier → Type) : Type :=
  ((∀ u v : wedge_carrier, wedge_rel u v → W u → W v)
     ∧ IsOpen (ptop_space X) (fun a => W (Datatypes.inl a))
     ∧ IsOpen (ptop_space Y) (fun b => W (Datatypes.inr b)))%type.

Lemma wedge_respects (U V : wedge_carrier → Type) :
  (∀ u, U u ↔ V u) → wedge_open U → wedge_open V.
Proof.
  intros H [HR [HX HY]].
  split; [| split ].
  - intros u v Huv Vu.
    exact (fst (H v) (HR u v Huv (snd (H u) Vu))).
  - exact (open_respects (ptop_space X) _ _
             (fun a => H (Datatypes.inl a)) HX).
  - exact (open_respects (ptop_space Y) _ _
             (fun b => H (Datatypes.inr b)) HY).
Qed.

Lemma wedge_proper (W : wedge_carrier → Type) :
  wedge_open W → ∀ u v : wedge_carrier, u ≈ v → W u → W v.
Proof. intros [HR _] u v Huv Wu; exact (HR u v Huv Wu). Qed.

Lemma wedge_union (I : Type) (U : I → (wedge_carrier → Type)) :
  (∀ i, wedge_open (U i)) → wedge_open (fun u => { i : I & U i u }).
Proof.
  intro H.
  split; [| split ].
  - intros u v Huv [i Hi].
    exact (i; fst (H i) u v Huv Hi).
  - exact (open_union (ptop_space X) I
             (fun i a => U i (Datatypes.inl a))
             (fun i => fst (snd (H i)))).
  - exact (open_union (ptop_space Y) I
             (fun i b => U i (Datatypes.inr b))
             (fun i => snd (snd (H i)))).
Qed.

Lemma wedge_whole : wedge_open (fun _ => poly_unit).
Proof.
  split; [| split ].
  - intros u v _ _; exact ttt.
  - exact (open_whole (ptop_space X)).
  - exact (open_whole (ptop_space Y)).
Qed.

Lemma wedge_inter (U V : wedge_carrier → Type) :
  wedge_open U → wedge_open V → wedge_open (fun u => U u ∧ V u).
Proof.
  intros [HRU [HXU HYU]] [HRV [HXV HYV]].
  split; [| split ].
  - intros u v Huv [Uu Vu].
    exact (HRU u v Huv Uu, HRV u v Huv Vu).
  - exact (open_inter (ptop_space X) _ _ HXU HXV).
  - exact (open_inter (ptop_space Y) _ _ HYU HYV).
Qed.

Definition Wedge_Top : TopSpace := {|
  top_carrier   := wedge_carrier;
  IsOpen        := wedge_open;
  open_respects := wedge_respects;
  open_proper   := wedge_proper;
  open_union    := wedge_union;
  open_whole    := wedge_whole;
  open_inter    := wedge_inter
|}.

Definition WedgeSum : PointedTop := {|
  ptop_space := Wedge_Top;
  ptop_pt := Datatypes.inl (ptop_pt X)
|}.

(** ** The injections / ** 注射 *)

Definition wedge_inl_map :
  SetoidMorphism (top_carrier (ptop_space X)) wedge_carrier.
Proof.
  unshelve notypeclasses refine {| morphism := Datatypes.inl |}.
  intros u v Huv; exact Huv.
Defined.

Definition wedge_inr_map :
  SetoidMorphism (top_carrier (ptop_space Y)) wedge_carrier.
Proof.
  unshelve notypeclasses refine {| morphism := Datatypes.inr |}.
  intros u v Huv; exact Huv.
Defined.

Definition wedge_inl_cont : ptop_space X ~{Top}~> Wedge_Top :=
  Build_ContinuousMorphism (ptop_space X) Wedge_Top wedge_inl_map
    (fun W HW => fst (snd HW)).

Definition wedge_inr_cont : ptop_space Y ~{Top}~> Wedge_Top :=
  Build_ContinuousMorphism (ptop_space Y) Wedge_Top wedge_inr_map
    (fun W HW => snd (snd HW)).

(* The left injection preserves the basepoint on the nose; the right one preserves it BY THE GLUING, which is the whole point of the wedge. / 左边的注射严格保持基点；右边的注射则通过粘合保持基点，这正是楔形的全部意义所在。 *)
Definition Wedge_inl : X ~{Top_pointed}~> WedgeSum :=
  Build_PointedMap X WedgeSum wedge_inl_cont (reflexivity _).

Lemma wedge_inr_preserves :
  wedge_inr_cont (ptop_pt Y) ≈ ptop_pt WedgeSum.
Proof. exact (reflexivity _, reflexivity _). Qed.

Definition Wedge_inr : Y ~{Top_pointed}~> WedgeSum :=
  Build_PointedMap Y WedgeSum wedge_inr_cont wedge_inr_preserves.

End WedgeSum.

Arguments wedge_rel {X Y} u v.
Arguments wedge_open {X Y} W.

(** ** The copairing / ** 配对 *)

(*
 Explicit binders rather than a section, as in
 Instance/Top/Coproduct.v: the tree's default [Proof using] would
 otherwise have to name [f] and [g].

 Well-definedness across the gluing is exactly the two basepoint
 conditions: f (pt X) ≈ pt Z ≈ g (pt Y). 

 --------
 显式绑定器，而不是一个部分，如在 Instance/Top/Coproduct.v 中：树的默认 [Proof using] 否则必须命名为 [f] 和 [g]。

 在粘合上的定义良好性恰好是两个基点条件：f (pt X) ≈ pt Z ≈ g (pt Y).
*)
Definition wedge_merge_map {X Y Z : PointedTop}
  (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z) :
  SetoidMorphism (wedge_carrier X Y) (top_carrier (ptop_space Z)).
Proof.
  unshelve notypeclasses refine {| morphism := fun u =>
    match u with
    | Datatypes.inl a => ptop_map f a
    | Datatypes.inr b => ptop_map g b
    end |}.
  intros [a|a] [b|b] H; simpl in H.
  - exact (proper_morphism (continuous_map (ptop_map f)) a b H).
  - transitivity (ptop_pt Z).
    + transitivity (ptop_map f (ptop_pt X)).
      * exact (proper_morphism (continuous_map (ptop_map f)) _ _ (fst H)).
      * exact (ptop_preserves f).
    + transitivity (ptop_map g (ptop_pt Y)).
      * symmetry; exact (ptop_preserves g).
      * symmetry.
        exact (proper_morphism (continuous_map (ptop_map g)) _ _ (snd H)).
  - transitivity (ptop_pt Z).
    + transitivity (ptop_map g (ptop_pt Y)).
      * exact (proper_morphism (continuous_map (ptop_map g)) _ _ (fst H)).
      * exact (ptop_preserves g).
    + transitivity (ptop_map f (ptop_pt X)).
      * symmetry; exact (ptop_preserves f).
      * symmetry.
        exact (proper_morphism (continuous_map (ptop_map f)) _ _ (snd H)).
  - exact (proper_morphism (continuous_map (ptop_map g)) a b H).
Defined.

Lemma wedge_merge_cont {X Y Z : PointedTop}
  (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z) :
  Continuous (Wedge_Top X Y) (ptop_space Z) (wedge_merge_map f g).
Proof.
  intros W HW.
  split; [| split ].
  - intros u v Huv Wu.
    exact (open_proper (ptop_space Z) W HW _ _
             (proper_morphism (wedge_merge_map f g) u v Huv) Wu).
  - exact (continuity (ptop_map f) W HW).
  - exact (continuity (ptop_map g) W HW).
Qed.

Definition wedge_merge_top {X Y Z : PointedTop}
  (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z) :
  Wedge_Top X Y ~{Top}~> ptop_space Z :=
  Build_ContinuousMorphism (Wedge_Top X Y) (ptop_space Z)
    (wedge_merge_map f g) (wedge_merge_cont f g).

Definition Wedge_merge {X Y Z : PointedTop}
  (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z) :
  WedgeSum X Y ~{Top_pointed}~> Z :=
  Build_PointedMap (WedgeSum X Y) Z (wedge_merge_top f g) (ptop_preserves f).

(** ** The universal property / ** 通用性质 *)

Lemma Wedge_ump {X Y Z : PointedTop}
      (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z)
      (h : WedgeSum X Y ~{Top_pointed}~> Z) :
  h ≈ Wedge_merge f g
    ↔ (h ∘ Wedge_inl X Y ≈ f) ∧ (h ∘ Wedge_inr X Y ≈ g).
Proof.
  split.
  - intro Hh.
    split.
    + intro a; exact (Hh (Datatypes.inl a)).
    + intro b; exact (Hh (Datatypes.inr b)).
  - intros [Hl Hr] [a|a].
    + exact (Hl a).
    + exact (Hr a).
Qed.

(* Field-shaped wrappers: [@Cartesian (Top_pointed^op)]'s [fork] binds the target first, then the two summands. / 字段形包装器：[@Cartesian (Top_pointed^op)] 的 [fork] 首先绑定目标，然后绑定两个加数。 *)
Definition Wedge_cofork (Z X Y : PointedTop)
  (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z) :
  WedgeSum X Y ~{Top_pointed}~> Z := Wedge_merge f g.

Lemma Wedge_cofork_respects (Z X Y : PointedTop) :
  Proper (equiv ==> equiv ==> equiv) (Wedge_cofork Z X Y).
Proof.
  intros f f' Hf g g' Hg [a|a].
  - exact (Hf a).
  - exact (Hg a).
Qed.

Lemma Wedge_cofork_ump (Z X Y : PointedTop)
      (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z)
      (h : WedgeSum X Y ~{Top_pointed}~> Z) :
  h ≈ Wedge_cofork Z X Y f g
    ↔ (h ∘ Wedge_inl X Y ≈ f) ∧ (h ∘ Wedge_inr X Y ≈ g).
Proof. exact (Wedge_ump f g h). Qed.

#[export] Instance Top_pointed_Cocartesian : @Cocartesian Top_pointed :=
  @Build_Cartesian (Top_pointed^op)
    WedgeSum
    Wedge_cofork
    Wedge_inl
    Wedge_inr
    Wedge_cofork_respects
    Wedge_cofork_ump.

(** ** Strict identifications / ** 严格识别 *)

Example Wedge_coprod_obj (X Y : PointedTop) :
  @Coprod Top_pointed Top_pointed_Cocartesian X Y = WedgeSum X Y := eq_refl.

Example Wedge_carrier_eq (X Y : PointedTop) :
  carrier (top_carrier (ptop_space
    (@Coprod Top_pointed Top_pointed_Cocartesian X Y)))
    = wpoint X Y := eq_refl.

Example Wedge_inl_is_inl (X Y : PointedTop) :
  @inl Top_pointed Top_pointed_Cocartesian X Y = Wedge_inl X Y := eq_refl.

Example Wedge_inr_is_inr (X Y : PointedTop) :
  @inr Top_pointed Top_pointed_Cocartesian X Y = Wedge_inr X Y := eq_refl.

Example Wedge_merge_is_merge (X Y Z : PointedTop)
  (f : X ~{Top_pointed}~> Z) (g : Y ~{Top_pointed}~> Z) :
  @merge Top_pointed Top_pointed_Cocartesian Z X Y f g = Wedge_merge f g :=
  eq_refl.

(* The basepoint of the wedge IS the image of X's basepoint. / 楔形的基点是 X 的基点的像。 *)
Example Wedge_basepoint (X Y : PointedTop) :
  ptop_pt (@Coprod Top_pointed Top_pointed_Cocartesian X Y)
    = Datatypes.inl (ptop_pt X) := eq_refl.

(*
 Symmetry and associativity come free from the cocartesian structure;
 the unit laws do not, there being no initial object of [Top_pointed]
 in tree. 

 --------
 对称性和结合性是从余笛卡尔结构中自然得到的；单位律则不是，因为在树中不存在 [Top_pointed] 的初始对象。
*)
Example Wedge_comm (X Y : PointedTop) :
  @Isomorphism Top_pointed (WedgeSum X Y) (WedgeSum Y X) :=
  @coprod_comm Top_pointed Top_pointed_Cocartesian X Y.

Example Wedge_assoc (X Y Z : PointedTop) :
  @Isomorphism Top_pointed
    (WedgeSum (WedgeSum X Y) Z) (WedgeSum X (WedgeSum Y Z)) :=
  @coprod_assoc Top_pointed Top_pointed_Cocartesian X Y Z.

(* * ** The gluing is real, and it is what distinguishes the two rosters / * ** 粘合是真实的，这就是区分这两个名单的原因 *)

(* The two injections agree at the basepoints — the defining property of the wedge. / 这两个注入在基点处一致——这是楔形的定义性质。 *)
Lemma wedge_basepoints_identified (X Y : PointedTop) :
  continuous_map (ptop_map (Wedge_inl X Y)) (ptop_pt X)
    ≈ continuous_map (ptop_map (Wedge_inr X Y)) (ptop_pt Y).
Proof. exact (reflexivity _, reflexivity _). Qed.

(*
 And in the UNPOINTED coproduct of the same two spaces they do not: the
 sum setoid never identifies across summands.  So the wedge genuinely
 quotients, and Mac Lane's two roster entries are different objects. 

 --------
 而在同样两个空间的未加点余积中则不然：和集合范畴从不在求和子上进行识别。因此楔形积是真正的商，而麦克莱恩的两个名册条目是不同的对象。
*)
Lemma wedge_is_not_sum (X Y : PointedTop) :
  continuous_map (Top_inl (ptop_space X) (ptop_space Y)) (ptop_pt X)
    ≈ continuous_map (Top_inr (ptop_space X) (ptop_space Y)) (ptop_pt Y)
  → False.
Proof. exact (fun H => H). Qed.

(* * ** Non-vacuity: away from the basepoints nothing else is glued / * ** 非空性：远离基点，别的什么都没有粘附 *)

(* A two-point discrete space, built from Instance/Top/Coproduct.v's own coproduct of two copies of the point, pointed at its left point. / 一个两点离散空间，由 Instance/Top/Coproduct.v 自己的两个点的余积构建，指向它的左点。 *)
Definition TwoPt : PointedTop := {|
  ptop_space := Sum_Top Point_Top Point_Top;
  ptop_pt := Datatypes.inl ttt
|}.

(* The two non-basepoint points of [TwoPt ∨ TwoPt] stay apart. / [TwoPt ∨ TwoPt] 的两个非基点保持分开。 *)
Lemma wedge_non_basepoints_differ :
  @wedge_rel TwoPt TwoPt
    (Datatypes.inl (Datatypes.inr ttt))
    (Datatypes.inr (Datatypes.inr ttt))
  → False.
Proof. exact (fun H => fst H). Qed.

(* While the basepoints are glued, in the same space. / 当基点被粘合时，在同一个空间里。 *)
Example wedge_two_pt_basepoints :
  @wedge_rel TwoPt TwoPt
    (Datatypes.inl (Datatypes.inl ttt))
    (Datatypes.inr (Datatypes.inl ttt)) :=
  (reflexivity _, reflexivity _).
