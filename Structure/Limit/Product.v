Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(* * * Indexed products as limits of discrete diagrams / * * 将乘积作为离散图的极限 *)

(*
 nLab:      https://ncatlab.org/nlab/show/product
 Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)

 An [A]-indexed product of a family [f : A → C] is an object [p] together
 with a family of projections [proj a : p ~> f a] that is universal: every
 competing family [pi a : c ~> f a] factors through the projections by a
 unique mediating map [u : c ~> p] with [proj a ∘ u ≈ pi a] for all [a].
 This is exactly the limit of the discrete diagram [DiscreteCat_Functor f]
 (Instance/Discrete.v): a cone over that diagram is precisely a family of
 legs [c ~> f a] — the discrete category has only identity morphisms, so
 the cone-coherence condition is vacuous — and the terminal such cone is
 the indexed product.

 This file plays, for indexed products, the role that
 [Structure/Equalizer/Fork.v] plays for equalizers: it wraps the bundled
 limit ([Structure/Limit.v]) in elementary, fork-shaped accessors that
 insulate callers from all cone plumbing.  [IsIndexedProduct] records the
 universal property directly on a family [proj]; [iprod]/[iprod_proj]/
 [iprod_ump] read a [Limit (DiscreteCat_Functor f)] as such a product at
 its apex, translating a plain family to and from a cone over the discrete
 diagram; [limit_is_indexed_product] bundles those three into the record;
 and [HasIndexedProducts] packages a choice of indexed product for every
 family.  No finiteness is assumed: [A] is an arbitrary [Type].

 STATUS: axiom-free.  The discrete cone-coherence proof merely destructs an
 equality witness, and nothing here Requires funext, choice, or classical
 logic.  Universe note: because the hom-setoid of [DiscreteCat A] is strict
 equality, forming [Limit (DiscreteCat_Functor f)] pins the hom/proof
 universes of [C] accordingly; every definition below is universe
 polymorphic (via [Category.Lib]) and simply carries that constraint, so no
 single ambient category is over-committed.  For that reason the accessors
 are top-level definitions parameterized by [C], [A], [f], rather than a
 shared [Section] context. 

 --------
 nLab：https://ncatlab.org/nlab/show/product
 Wikipedia：https://en.wikipedia.org/wiki/Product_(category_theory)

 一个[A]索引的[f : A → C]族的乘积是一个对象[p]，以及一个[proj a : p ~> f a]的投影族，它是普遍的：每个竞争族[pi a : c ~> f a]都通过一个唯一的中介映射[u : c ~> p]通过投影来分解，并且对于所有[a]满足[proj a ∘ u ≈ pi a]。这正是离散图[DiscreteCat_Functor f]（Instance/Discrete.v）的极限：该图上的一个锥正是腿[c ~> f a]的一个族——离散范畴只有恒等态射，因此锥的一致性条件是无效的——而这样一个终锥就是索引乘积。该文件对于索引产品起到了 [Structure/Equalizer/Fork.v] 对均衡器的作用：它将捆绑的极限（[Structure/Limit.v]）封装在基本的、分叉形的访问器中，从而将调用者与所有锥形布线隔离开来。[IsIndexedProduct] 直接在一个族 [proj] 上记录了通用性质；[iprod] / [iprod_proj] / [iprod_ump] 将 [Limit (DiscreteCat_Functor f)] 作为其顶点的此类产品读取，将一个普通族在离散图上转换为锥形并从锥形转换回普通族；[limit_is_indexed_product] 将这三者捆绑到记录中；[HasIndexedProducts] 为每个族打包一个索引产品的选择。不假设有限性：[A] 是任意的 [Type]。状态：无公理。离散锥一致性证明仅仅是分解一个等式见证，这里不需要函数扩展、选择公理或经典逻辑。宇宙注记：因为 [DiscreteCat A] 的同态集是严格相等，形成 [Limit (DiscreteCat_Functor f)] 会相应地固定 [C] 的同态/证明宇宙；下面的每个定义都是宇宙多态的（通过 [Category.Lib]）并且只是承载该约束，因此没有单一的环境范畴被过度使用。因此，访问器是顶层定义，由 [C]、[A]、[f] 参数化，而不是共享的 [Section] 上下文。
*)

(*
 The elementary universal property of an indexed product: the family [proj]
 of projections is universal, so every competing family [pi] factors
 uniquely across it.  This mirrors the [IsEqualizer] record of
 [Structure/Equalizer/Fork.v]. 

 --------
 索引积的基本泛性质：投影的族 [proj] 是普遍的，因此每一个竞争族 [pi] 都可以独特地通过它分解。这对应于 [IsEqualizer] 的 [Structure/Equalizer/Fork.v] 记录。
*)
Record IsIndexedProduct {C : Category} {A : Type} (f : A → C)
  (p : C) (proj : ∀ a : A, p ~> f a) := {
  (*
 universal property: every family [pi] into the [f a] factors uniquely
 through the projections 

 --------
 泛性质：每个族  [pi]  到  [f a]  都唯一地通过投影分解
*)
  iprod_desc {c : C} (pi : ∀ a, c ~> f a) :
    ∃! u : c ~> p, ∀ a, proj a ∘ u ≈ pi a
}.

Arguments iprod_desc {_ _ _ _ _} _ {_} _.

(* * ** From a plain family to a cone over the discrete diagram / * ** 从一个平凡的族到离散图上的圆锥 *)

(*
 Cone coherence over the discrete diagram is vacuous: the only morphisms of
 [DiscreteCat A] are equality witnesses, and pushing a leg along [fmap] of
 an equality proof recovers the leg at the (necessarily equal) codomain.
 This statement is definitionally the [cone_coherence] field of an [ACone]
 over [DiscreteCat_Functor f]. 

 --------
 离散图上的圆锥相干性是空的：[DiscreteCat A] 的唯一态射是相等的证明，将一个支沿着相等证明的 [fmap] 推动，会在（必然相等的）上域恢复该支。这个陈述在定义上就是 [ACone] 在 [DiscreteCat_Functor f] 上的 [cone_coherence] 域。
*)
Lemma family_cone_coherence {C : Category} {A : Type} (f : A → C)
  (c : C) (pi : ∀ a, c ~> f a) :
  ∀ (x y : DiscreteCat A) (e : x ~{DiscreteCat A}~> y),
    fmap[DiscreteCat_Functor f] e ∘ pi x ≈ pi y.
Proof.
  intros x y e.
  destruct e.                   (* the only case is [eq_refl]; then [y := x] / 唯一的情况是 [eq_refl]；然后是 [y := x] *)
  simpl.                        (* [fmap] of [eq_refl] computes to [id] / [fmap] 的 [eq_refl] 计算结果为 [id] *)
  apply id_left.
Qed.

(* The cone over [DiscreteCat_Functor f] induced by a plain family of legs. / 由一组普通腿引起的 [DiscreteCat_Functor f] 上的圆锥。 *)
Definition family_cone {C : Category} {A : Type} (f : A → C)
  (c : C) (pi : ∀ a, c ~> f a) : Cone (DiscreteCat_Functor f).
Proof.
  unshelve econstructor.
  - exact c.                                  (* apex *)
  - unshelve econstructor.
    + exact pi.                               (* legs *)
    + exact (family_cone_coherence f c pi).   (* coherence, vacuous here / 连贯性，这里空洞 *)
Defined.

(* * ** Reading a limit of the discrete diagram as an indexed product / * ** 将离散图的极限视为一个索引积 *)

(* The product object: the apex of the limit cone. / 乘积对象：极限圆锥的顶点。 *)
Definition iprod {C : Category} {A : Type} (f : A → C)
  (L : Limit (DiscreteCat_Functor f)) : C :=
  vertex_obj[L].

(* The projections: the limit legs, one for each index. / 投影：极限腿，每个指标一个。 *)
Definition iprod_proj {C : Category} {A : Type} (f : A → C)
  (L : Limit (DiscreteCat_Functor f)) (a : A) : iprod f L ~> f a :=
  limit_leg (limit_is_alimit L) a.

(*
 The universal property: every competing family [pi] factors uniquely
 through the projections, by mediating into the limit from the cone the
 family induces. 

 --------
 泛性质：每个竞争族 [pi] 都通过从锥体引入极限的方式，由投影唯一地分解。
*)
Definition iprod_ump {C : Category} {A : Type} (f : A → C)
  (L : Limit (DiscreteCat_Functor f))
  (c : C) (pi : ∀ a, c ~> f a) :
  ∃! u : c ~> iprod f L, ∀ a, iprod_proj f L a ∘ u ≈ pi a.
Proof.
  unshelve eapply Build_Unique.
  - exact (limit_med (limit_is_alimit L) (family_cone f c pi)).
  - intros a.
    exact (limit_med_commutes (limit_is_alimit L) (family_cone f c pi) a).
  - intros v Hv.
    exact (limit_med_unique (limit_is_alimit L) (family_cone f c pi) v Hv).
Defined.

(* The limit, packaged as an elementary indexed product at its apex. / 极限，被包装成其顶点的基本索引乘积。 *)
Definition limit_is_indexed_product {C : Category} {A : Type} (f : A → C)
  (L : Limit (DiscreteCat_Functor f)) :
  IsIndexedProduct f (iprod f L) (iprod_proj f L) :=
  {| iprod_desc := fun c pi => iprod_ump f L c pi |}.

(*
 A category has all indexed products when every family [f : A → C] over an
 arbitrary index [Type] carries an elementary indexed product.  This is the
 indexed-product analogue of [HasEqualizers] in
 [Structure/Equalizer/Fork.v]. 

 --------
 当每个族  [f : A → C]  在任意指标  [Type]  上都携带一个基本指标乘积时，一个范畴具有所有指标乘积。这是  [Structure/Equalizer/Fork.v] 中  [HasEqualizers] 的指标乘积类比。
*)
Class HasIndexedProducts (C : Category) := {
  indexed_product {A : Type} (f : A → C) : C;
  indexed_product_proj {A : Type} (f : A → C) (a : A) :
    indexed_product f ~> f a;
  indexed_product_ump {A : Type} (f : A → C) :
    IsIndexedProduct f (indexed_product f) (indexed_product_proj f)
}.
