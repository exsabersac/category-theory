Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Mod.
Require Import Category.Structure.Limit.Product.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(*
   * * Indexed products of modules

   The product ∏_{i∈I} V_i of an arbitrary family of R-modules, with every
   operation pointwise, and its universal property — in the two clauses,
   and assembled into Structure/Limit/Product.v's [IsIndexedProduct].
   Written for Instance/FdVect/NoRightAdjoint.v (#433), which needs the
   countable power F^ℕ as an object of [RMod (field_ring F)]; nothing here
   is specific to fields or to ℕ.

   BEFORE THIS FILE the tree had no indexed product or coproduct in any
   algebraic category: Instance/Mod/Coproduct.v's [RMod_Biproduct] and
   Instance/Ab/Coproduct.v's coproduct are binary, and the tree's
   [HasIndexedProducts] inhabitants — Sets' (Instance/Sets/Products.v),
   Cat's and StrictCat's (Instance/Cat/Limit.v), functor
   categories' and [[_2, Sets]]'s (Instance/Fun/Terminal.v) and
   [_1]'s (Structure/Limit/Power/Adjunction.v) — include no algebraic
   category; measured by `grep -rn 'Instance .*HasIndexedProducts\|
   Definition .*HasIndexedProducts' --include='*.v'`.

   WHAT IS HERE.  Over [Context {R : RingObject} {I : Type} (V : I →
   RModObject R)]: the carrier [modprod_setoid] (the dependent function
   space [∀ i, carrier (V i)] under pointwise [≈]), the commutative monoid
   [modprod_cmon], the abelian group [modprod_ab], the module [ProdMod],
   the projections [prod_proj i : RModHom ProdMod (V i)], the mediator
   [prod_tuple f : RModHom Z ProdMod] out of a family [f : ∀ i, RModHom Z
   (V i)], the two clauses of the universal property, [prod_tuple_proj]
   ([prod_proj i ∘ prod_tuple f ≈ f i], stated as a composite in [RMod R])
   and [prod_tuple_unique] (any [u] with the same projections is [≈
   prod_tuple f]) — both [reflexivity] pointwise, because the projections
   compute: [prod_proj_component] reads [cmon_map (rm_hom (prod_proj i)) f
   = f i] by [eq_refl] — and their assembly [ProdMod_IsIndexedProduct :
   IsIndexedProduct V ProdMod prod_proj], whose mediator IS [prod_tuple]
   ([prod_iprod_mediator], by [eq_refl]).

   NOT DELIVERED.  The [HasIndexedProducts (RMod R)] instance itself — not
   attempted: #433 needs only the one product, and Instance/Sets/Products.v
   (its header, “the class quantifies its index by a bare [Type]”) records
   the universe negotiation the class demands, which is left for the issue
   that needs the class; indexed COPRODUCTS ⊕_I (finite support needs a
   decidable index or a free construction; none is built); the
   identification of the binary case with Instance/Mod/Coproduct.v's
   [RMod_Biproduct].

   MEASURED.  11 `.glob` heads (9 `def`, 2 `prf`) and 20 [Program]
   obligations, all 31 “Closed under the global context”, zero `Axioms:`
   lines; the 20 obligations are the respectfulness and law proofs of the
   six [Program Definition]s, every one closed by hand under
   [Obligation Tactic := idtac] with `Qed` — twenty-two `Qed` in all, and
   ONE `Defined`, [ProdMod_IsIndexedProduct], LOAD-BEARING (flipped to
   `Qed` in a copy of the whole file, [prod_iprod_mediator] stops).
   Universes ([About] under `Set Printing Universes`): no [Set] anywhere;
   the data ([modprod_setoid], [modprod_cmon], [modprod_ab], [ProdMod])
   carry no equation and — apart from [modprod_setoid], which carries no
   strict constraint at all — one strict constraint, the module carrier
   level below the product's (`u6 < u11` for the monoid and the group,
   `u6 < u13` for the module); [prod_proj], [prod_tuple] and
   [prod_proj_component] carry [RModHom]'s identification of the three
   module-internal levels (`u5 = u6 = u7`) and `u6 < u8`; the four heads
   stated inside [RMod R] — [prod_tuple_proj], [prod_tuple_unique],
   [ProdMod_IsIndexedProduct], [prod_iprod_mediator] — inherit that
   category's identification of the module levels with the ring's (`u =
   u3 = u5 = u6 = u7`, `u1 = u4`), two strict constraints (`u < u8`,
   `u < u9`) and the stdlib caps `Basics.compose` and `ID` (the readback
   adds `Setoid.u`).  Closure 43 files excluding self (Structure/Limit/
   Product.v 7 at the margin, Instance/Mod.v 6, the other six `Require`s
   0; none of the eight is droppable); zero name collisions across the
   tree for the eleven names (`grep -rlw --include='*.v'`; the first
   draft's [prod_setoid] became [modprod_setoid] because
   Lib/Datatypes.v owns [prod_setoid]).  The `make print-assumptions`
   gate carries the eleven heads. 

   --------
   * * 模块的索引积

   任意 R-模族 {V_i}_{i ∈ I} 的积 ∏_{i∈I} V_i，每个操作按点定义，以及它的泛性质——在两个子句中，并汇总于 Structure/Limit/Product.v 的 [IsIndexedProduct]。
   为 Instance/FdVect/NoRightAdjoint.v (#433) 所写，该文件需要可数次幂 F^ℕ 作为 [RMod (field_ring F)] 的对象；这里的内容并不特定于域或 ℕ。在此文件之前，树中没有任何索引的积或余积
   代数类别：Instance/Mod/Coproduct.v 的 [RMod_Biproduct] 和
   Instance/Ab/Coproduct.v 的余积是二元的，树的
   [HasIndexedProducts]居民 — 集合（实例/集合/产品.v），
   Cat 和 StrictCat（实例/cat/Limit.v），函子
   categories' 和 [[_2, Sets] ]'（实例/趣味/终端.v）以及
   [_1] 的（Structure/Limit/Power/Adjunction.v）——不含代数
   类别;通过 'grep -rn '实例 .*HasIndexedProducts\|
   定义 .*HasIndexedProducts' --include='*.v''。这里是什么。在 [Context {R : RingObject} {I : Type} (V : I → RModObject R)] 上：载体 [modprod_setoid]（在逐点 [≈] 下的依赖函数空间 [∀ i, carrier (V i)]）、可交换幺半群 [modprod_cmon]、阿贝尔群 [modprod_ab]、模 [ProdMod]、投影 [prod_proj i : RModHom ProdMod (V i)]、由族 [f : ∀ i, RModHom Z (V i)] 得出的中介 [prod_tuple f : RModHom Z ProdMod]、两条普遍性性质的条款 [prod_tuple_proj]（[prod_proj i ∘ prod_tuple f ≈ f i]，在 [RMod R] 中作为复合给出）和 [prod_tuple_unique]（任何具有相同投影的 [u] 是 [≈ prod_tuple f]）——两者都是逐点的，因为投影计算为：[prod_proj_component] 读作 [cmon_map (rm_hom (prod_proj i)) f = f i] 通过 [eq_refl] ——及其组合 [ProdMod_IsIndexedProduct : IsIndexedProduct V ProdMod prod_proj]，其中介为 [prod_tuple] ([prod_iprod_mediator]，依 [eq_refl]Z)Z ).未交付。[HasIndexedProducts (RMod R)] 实例本身——未尝试：#433 只需要一个产品，而 Instance/Sets/Products.v （其头文件，“类通过一个裸 [Type] 来量化其索引”）记录了类所要求的宇宙协商，这留给需要该类的问题处理；索引的 COPRODUCTS ⊕_I（有限支持需要一个可判定的索引或自由构造；没有构建）；将二元情况与 Instance/Mod/Coproduct.v 的 [RMod_Biproduct] 进行识别。测量。11  `.glob`  头（9  `def` ，2  `prf` ）和20  [Program] 义务，共31个“在全球环境下关闭”，零  `Axioms:`  行；这20个义务是六个  [Program Definition] 的尊重和法律证明，每一个都由手工在  [Obligation Tactic := idtac] 下关闭，附有  `Qed` ——总共二十二个  `Qed` ，以及一个  `Defined` ，[ProdMod_IsIndexedProduct] ，承重（在整个文件的一份副本中翻转到  `Qed` ，[prod_iprod_mediator] 停止）。宇宙（在 `Set Printing Universes` 下的 [About]）：任何地方都没有 [Set]；
   数据（[modprod_setoid]、[modprod_cmon]、[modprod_ab]、[ProdMod]）
   不包含方程，并且——除了 [modprod_setoid]，它根本不带任何严格约束——有一个严格约束，即模块承载级别低于产品的（对于幺半群和群是 `u6 < u11`，对于模块是 `u6 < u13`）；[prod_proj]、[prod_tuple] 和 [prod_proj_component] 承载 [RModHom] 对三个模块内部级别（`u5 = u6 = u7`）和 `u6 < u8` 的标识；[RMod R] 内部声明的四个头部——[prod_tuple_proj]、[prod_tuple_unique]、[ProdMod_IsIndexedProduct]、[prod_iprod_mediator]——继承了该类别对模块级别与环的标识（`u = u3 = u5 = u6 = u7 `, ` u1 = u4 `), two strict constraints (` u < u8`, `u < u9`）以及 stdlib 上限 `Basics.compose` 和 `ID`（回读添加了 `Setoid.u` ).闭包 43 个文件，不包括自身（Structure/Limit/Product.v 7 在边缘，Instance/Mod.v 6，其余六个 `Require` 为 0；这八个中没有可删除的）；在整个树中这十一名称之间没有名称冲突（`grep -rlw --include='*.v'`；第一稿的 [prod_setoid] 因为 Lib/Datatypes.v 拥有 [prod_setoid] 而变为 [modprod_setoid]）。`make print-assumptions` 门承载这十一条头。
*)

#[local] Obligation Tactic := idtac.

Section ProdMod.

Context {R : RingObject}.
Context {I : Type}.
Context (V : I → RModObject R).

(* The carrier is the dependent function space, with pointwise [≈]. / 载体是依赖函数空间，具有逐点 [≈] 。 *)
Program Definition modprod_setoid : SetoidObject := {|
  carrier := ∀ i : I, carrier (cmon_setoid (V i));
  is_setoid := {| equiv := fun f g => ∀ i, f i ≈ g i |}
|}.
Next Obligation.
  intros; constructor.
  - intros f i; reflexivity.
  - intros f g H i; now symmetry.
  - intros f g h H1 H2 i; now transitivity (g i).
Qed.

(*
 The carrier is a pointwise product of propositional carriers, so it is
 propositional pointwise: Lib/Setoid/Propositional.v's
 [dep_fun_PropEquiv], with the two implications the identity because the
 relation [modprod_setoid] writes inline IS the pointwise one. 

 --------
 载体是命题载体的逐点乘积，因此它是逐点命题的：Lib/Setoid/Propositional.v 的 [dep_fun_PropEquiv]，两个蕴含是恒等的，因为关系 [modprod_setoid] 内联写的就是逐点关系。
*)
Program Definition modprod_cmon : CMonObject := {|
  cmon_setoid := modprod_setoid;
  cmon_zero   := fun i => cmon_zero (V i);
  cmon_plus   := fun f g i => cmon_plus (V i) (f i) (g i);
  cmon_prop   := dep_fun_PropEquiv (is_setoid modprod_setoid)
                   (fun _ _ h => h) (fun _ _ h => h)
                   (fun i => cmon_prop (V i))
|}.
Next Obligation. intros f f' Hf g g' Hg i; now rewrite (Hf i), (Hg i). Qed.
Next Obligation. intros f g h i; apply cmon_plus_assoc. Qed.
Next Obligation. intros f g i; apply cmon_plus_comm. Qed.
Next Obligation. intros f i; apply cmon_plus_zero_l. Qed.

Program Definition modprod_ab : AbObject := {|
  ab_cmon := modprod_cmon;
  ab_neg  := fun f i => ab_neg (V i) (f i)
|}.
Next Obligation. intros f g H i; now rewrite (H i). Qed.
Next Obligation. intros f i; apply ab_neg_left. Qed.

(* The product module: all operations pointwise. / 乘积模块：所有运算都是逐点进行的。 *)
Program Definition ProdMod : RModObject R := {|
  rm_ab   := modprod_ab;
  rm_smul := fun r f i => rm_smul (V i) r (f i)
|}.
Next Obligation. intros r s Hrs f g Hfg i; now rewrite Hrs, (Hfg i). Qed.
Next Obligation. intros r f g i; apply rm_smul_distr_l. Qed.
Next Obligation. intros r s f i; apply rm_smul_distr_r. Qed.
Next Obligation. intros r s f i; apply rm_smul_assoc. Qed.
Next Obligation. intros f i; apply rm_smul_one. Qed.

(* The projections. / 预测。 *)
Program Definition prod_proj (i : I) : RModHom ProdMod (V i) := {|
  rm_hom := {| cmon_map := {| morphism := fun f => f i |} |}
|}.
Next Obligation. intros i f g H; exact (H i). Qed.
Next Obligation. intros i; reflexivity. Qed.
Next Obligation. intros i f g; reflexivity. Qed.
Next Obligation. intros i r f; reflexivity. Qed.

(* The mediating map out of a family of maps. / 从一族映射中的中介映射。 *)
Program Definition prod_tuple {Z : RModObject R} (f : ∀ i, RModHom Z (V i)) :
  RModHom Z ProdMod := {|
  rm_hom := {|
    cmon_map := {| morphism := fun z i => cmon_map (rm_hom (f i)) z |}
  |}
|}.
Next Obligation. intros Z f z z' H i; now rewrite H. Qed.
Next Obligation. intros Z f i; apply (cmon_map_zero (rm_hom (f i))). Qed.
Next Obligation. intros Z f a b i; apply (cmon_map_plus (rm_hom (f i))). Qed.
Next Obligation. intros Z f r z i; apply (rm_map_smul (f i)). Qed.

(*
 The universal property, in the two clauses [IsIndexedProduct] asks for;
 both are [reflexivity] pointwise. 

 --------
 在两个子句中，[IsIndexedProduct] 的普遍性属性要求；两者都是 [reflexivity] 点对点的。
*)
Lemma prod_tuple_proj {Z : RModObject R} (f : ∀ i, RModHom Z (V i)) (i : I) :
  @compose (RMod R) Z ProdMod (V i) (prod_proj i) (prod_tuple f) ≈ f i.
Proof. intro z; reflexivity. Qed.

Lemma prod_tuple_unique {Z : RModObject R} (f : ∀ i, RModHom Z (V i))
  (u : RModHom Z ProdMod)
  (H : ∀ i, @compose (RMod R) Z ProdMod (V i) (prod_proj i) u ≈ f i) :
  u ≈ prod_tuple f.
Proof. intros z i; exact (H i z). Qed.

(* The projections compute. / 这些预测正在计算。 *)
Example prod_proj_component (i : I) (f : carrier (cmon_setoid ProdMod)) :
  cmon_map (rm_hom (prod_proj i)) f = f i := eq_refl.

(*
 The two clauses assembled into the tree's own record: [ProdMod] with its
 projections is an indexed product in [RMod R]. 

 --------
 这两个从句组装进了树自身的记录：[ProdMod]，它的投影是 [RMod R] 中的一个索引乘积。
*)
Definition ProdMod_IsIndexedProduct :
  @IsIndexedProduct (RMod R) I V ProdMod prod_proj.
Proof.
  constructor; intros Z pi.
  exists (prod_tuple pi).
  - exact (prod_tuple_proj pi).
  - intros u Hu; symmetry; exact (prod_tuple_unique pi u Hu).
Defined.

(* The record's mediator IS [prod_tuple]. / 该记录的中介是 [prod_tuple]。 *)
Example prod_iprod_mediator {Z : RModObject R} (pi : ∀ i, RModHom Z (V i)) :
  unique_obj (iprod_desc ProdMod_IsIndexedProduct pi) = prod_tuple pi
  := eq_refl.

End ProdMod.
