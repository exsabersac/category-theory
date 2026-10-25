Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.

Generalizable All Variables.

(* * * Propositional equality for the objects and homs of [Sets] / * * [Sets] 的对象和函子命题等式 *)

(*
 nLab:    https://ncatlab.org/nlab/show/Bishop+set
 nLab:    https://ncatlab.org/nlab/show/h-set
 Book:    The Univalent Foundations Program, "Homotopy Type Theory", IAS
 2013, Definition 3.1.1 and Definition 3.3.1
 Book:    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §V.6 and §V.7, printed p. 128

 Lib/Setoid/Propositional.v introduces [PropEquiv S]: the property that a
 setoid's `≈` is logically equivalent to a [Prop]-valued relation, and
 explains why that has to be a property of particular setoids rather than a
 change to [Class Setoid].  This file carries the property along the
 constructions of [Sets] that the concrete algebraic categories are built
 from, since those categories are categories of setoids with structure and
 their limits are created out of [Sets].

 WHAT TRANSPORTS.  Hom-setoids, whose `≈` is pointwise into the target
 ([SetoidMorphism_equiv], Instance/Sets.v); binary products, whose `≈` is
 componentwise ([Sets_Cartesian], Instance/Sets/Cartesian.v); indexed
 products, whose `≈` is pointwise in the index ([Sets_iprod_equiv],
 Instance/Sets/Products.v); and limits, whose `≈` is the underlying
 indexed product's, the compatibility witness playing no part
 ([Sets_limit_equiv], Instance/Sets/Complete.v).  In each case the
 [Prop] relation is the obvious pointwise or componentwise one, and the
 [Example]s below read that back at [eq_refl] rather than asserting it.

 The limit transport is the one with consequences: [Ab] and [RMod R] get
 their limits by CREATION along the forgetful functors down to [Sets]
 (Instance/Ab/Limit.v, Instance/Mod/Limit.v), so [limit_PropEquiv] is what
 makes a limit of propositional algebras propositional again.

 WHAT DOES NOT TRANSPORT, AND HOW THAT WAS MEASURED.  There is no instance
 here of the shape [∀ X : SetoidObject, PropEquiv (is_setoid X)], and none of
 [LocallyPropositional Sets] or [LocallyPropositional Cat].  The obvious
 route -- take [pequiv f g := inhabited (f ≈ g)] -- supplies [pequiv_from] and
 then stops: [pequiv_to] would have to eliminate a [Prop] into the
 [Type]-valued goal [f ≈ g].  For [Cat] that is not merely inconvenient, and
 Test/ProbePropEquiv.v measures it: an [F ≈ G] in [Cat] IS a family of
 isomorphisms (Theory/Functor.v, installed at Instance/Cat.v), and
 projecting the isomorphism at [x] out of an [inhabited (F ≈ G)] is refused.
 For [Sets] the situation is weaker and is stated as such: an arbitrary
 [SetoidObject] carries an arbitrary [Type]-valued `≈`, so no route to a
 [Prop] mirror is available in general; that is an absence of a construction,
 not a proof that none exists.  Which is exactly why the algebraic object
 records of the later phases CARRY a [PropEquiv] field rather than deriving
 one.
 CORRECTION (#469): the absence is now characterized.  A [PropEquiv] on
 every object of [Sets] at once is interderivable with the principle
 ∀ A : Type, inhabited A → A at the carriers' level (Instance/Pos/
 Monadicity.v's [all_PropEquiv_trunc] and [trunc_all_PropEquiv], through
 its [SetsTruncElim], [trunc_choice] and [choice_trunc]).  That principle
 follows from informative excluded middle, and it is believed to have
 no axiom-free proof, by a normal-form argument that file's header
 sketches (argued, not established); no in-tree
 statement proves the unprovability, which is metatheory. 

 --------
 nLab：https://ncatlab.org/nlab/show/Bishop+set
 nLab：https://ncatlab.org/nlab/show/h-set
 书籍：The Univalent Foundations Program，《同伦类型理论》，IAS 2013，第3.1.1定义和第3.3.1定义
 书籍：Mac Lane，《为工作数学家准备的范畴》，第二版，第V.6节和第V.7节，印刷版第128页

 Lib/Setoid/Propositional.v 引入了 [PropEquiv S]：一个集合等价类的 `≈` 在逻辑上等价于一个 [Prop] 值的关系的性质，并解释了为什么这必须是特定集合等价类的性质，而不是对 [Class Setoid] 的改变。这个文件在构建 [Sets] 的过程中保留了该性质，具体代数范畴由其构建，因为这些范畴是具有结构的集合等价类的范畴，并且它们的极限是由 [Sets] 创建的。什么是传输。Hom-集合准则，其 `≈` 在目标 ([SetoidMorphism_equiv], Instance/Sets.v) 中是逐点的；二元积，其 `≈` 在各分量上 ([Sets_Cartesian], Instance/Sets/Cartesian.v)；索引积，其 `≈` 在索引上是逐点的 ([Sets_iprod_equiv], Instance/Sets/Products.v)；以及极限，其 `≈` 是底层索引积的，兼容性证据不起作用 ([Sets_limit_equiv], Instance/Sets/Complete.v)。在每种情况下，[Prop] 关系是显而易见的逐点或逐分量关系，并且下面的 [Example] 在 [eq_refl] 处进行回读，而不是断言它。极限传输是有后果的：[Ab] 和 [RMod R] 通过沿着遗忘函子到 [Sets] 的创建得到它们的极限（Instance/Ab/Limit.v, Instance/Mod/Limit.v），所以 [limit_PropEquiv] 是使命题代数的极限再次成为命题的原因。什么不能传输，以及这是如何测量的。这里没有形状 [∀ X : SetoidObject, PropEquiv (is_setoid X)] 的实例，也没有 [LocallyPropositional Sets] 或 [LocallyPropositional Cat] 的实例。显而易见的路线——取 [pequiv f g := inhabited (f ≈ g)]——提供 [pequiv_from]，然后停止：[pequiv_to] 必须将 [Prop] 消除到 [Type] 值目标 [f ≈ g]。对于 [Cat]，这不仅仅是不方便，并且 Test/ProbePropEquiv.v 测量了它：[Cat] 中的 [F ≈ G] 是一族同构（Theory/Functor.v，在 Instance/Cat.v 中安装），并且从 [inhabited (F ≈ G)] 投影 [x] 上的同构是被拒绝的。对于 [Sets] 情况较弱，并且表述如下：一个任意的 [SetoidObject] 携带一个任意的 [Type] 值的 `≈`，因此通常没有通向 [Prop] 镜像的途径；这是一种构造上的缺失，而不是证明其不存在。这正是为什么后期阶段的代数对象记录携带一个 [PropEquiv] 字段而不是推导一个字段的原因。修正 (#469)：该缺失现在已被描述。在 [Sets] 的每个对象上同时存在一个 [PropEquiv]，可以与原理 ∀ A : Type, inhabited A → A 在载体层面相互推导（Instance/Pos/Monadicity.v 的 [all_PropEquiv_trunc] 和 [trunc_all_PropEquiv]，通过其 [SetsTruncElim]、[trunc_choice] 和 [choice_trunc]）。这个原则源于信息排中律，人们认为它没有无公理证明，通过该文件头部勾画的正规形式论证（是论证，不是确立）；在树内没有语句能证明不可证明性，这属于元理论。
*)

(* * ** The property, at the level of a [Sets] object / * ** 该属性，位于 [Sets] 对象的级别 *)

(*
 [PropEquivObj X] is [PropEquiv] of the setoid [X] carries.  It is the field
 the concrete algebraic object records take, spelled once here so that those
 records need not repeat [is_setoid].

 Measured (About under Set Printing Universes):

 PropEquivObj@{u u0 u1} : SetoidObject@{u0 u1} → Type@{u}
 ( * u u0 u1 |= Set < u, u0 <= u, u1 <= u * )

 -- the carrier and proof universes of the object bound it from below and
 nothing bounds it from above, so it sits at the object's own level. 

 --------
 [PropEquivObj X] 是 [X] 集合中 [PropEquiv] 的载体。它是具体代数对象记录所采用的字段，这里拼写一次，以便那些记录不必重复 [is_setoid]。

 测量（关于集合打印宇宙）：

 PropEquivObj@{u u0 u1} : SetoidObject@{u0 u1} → Type@{u}
 ( * u u0 u1 |= 集合 < u, u0 <= u, u1 <= u * )

 -- 对象的载体和证明宇宙把它从下界绑定，而且没有什么能把它从上界绑定，因此它位于对象自身的层级。
*)
Definition PropEquivObj (X : SetoidObject) : Type := PropEquiv (is_setoid X).

(** ** Hom-setoids / ** 同态集合 *)

(*
 Two setoid maps are `≈` when they agree pointwise up to the target's `≈`
 (Instance/Sets.v), so a [Prop] mirror on the TARGET gives one on the
 hom-setoid, pointwise.  The source needs nothing.

 Measured:

 hom_PropEquiv@{u} :
 ∀ {x y : SetoidObject@{u u}},
 PropEquiv@{u u} y → PropEquiv@{u u} SetoidMorphism_Setoid@{u u u}
 ( * u |=  * )

 -- ONE universe, with no constraint at all: the transport neither raises
 the level nor pins it. 

 --------
 当两个集合态映射在每个点上与目标的 ZZ/WZZ (Instance/Sets.v) 一致时，它们就是 `≈`，所以目标上的 [Prop] 镜像会在点态集合上产生一个镜像。源端不需要任何操作。

 测量：

 hom_PropEquiv@{u} :
 ∀ {x y : SetoidObject@{u u}},
 PropEquiv@{u u} y → PropEquiv@{u u} SetoidMorphism_Setoid@{u u u}
 ( * u |=  * )

 -- 单一宇宙，没有任何约束：传输既不提升等级，也不固定它。
*)
#[export] Instance hom_PropEquiv {x y : SetoidObject} (Py : PropEquiv (is_setoid y)) :
  PropEquiv (@SetoidMorphism_Setoid x y).
Proof.
  unshelve refine
    {| pequiv := fun f g : SetoidMorphism x y =>
                   forall a : carrier x, @pequiv _ _ Py (f a) (g a) |}.
  - intros f g H a; exact (pequiv_to _ _ (H a)).
  - intros f g H a; exact (pequiv_from _ _ (H a)).
Defined.

(* The hom-setoid of [Sets] IS [SetoidMorphism_Setoid] on the nose (Instance/Sets.v), so the instance above is an instance for [Sets]'s [homset] without further work. / [Sets] 的同态集合就是 [SetoidMorphism_Setoid] 本身（Instance/Sets.v），因此上面的实例就是 [Sets] 的 [homset] 的实例，无需进一步操作。 *)
Example hom_PropEquiv_is_Sets_homset (x y : SetoidObject) :
  @SetoidMorphism_Setoid x y = @homset Sets x y := eq_refl.

(* The relation it supplies is the pointwise one, read back at [eq_refl]. / 它提供的关系是逐点关系，在 [eq_refl] 处回读。 *)
Example hom_pequiv_is_pointwise {x y : SetoidObject}
  (Py : PropEquiv (is_setoid y)) (f g : x ~{Sets}~> y) :
  @pequiv _ _ (hom_PropEquiv Py) f g
    = (forall a : carrier x, @pequiv _ _ Py (f a) (g a)) := eq_refl.

(** ** Binary products / ** 二进制产品 *)

(*
 [Sets_Cartesian]'s product setoid is componentwise
 (Instance/Sets/Cartesian.v).  The conjunction below is Coq's [and],
 written `/\`; the library's `∧` is [prod] and would leave the relation in
 [Type].

 Measured:

 product_PropEquiv@{u u0} :
 ∀ {x y : SetoidObject@{u0 u0}},
 PropEquiv@{u0 u0} x → PropEquiv@{u0 u0} y →
 PropEquiv@{u0 u0} (Cartesian.product_obj x y)
 ( * u u0 |= u0 < u, and the stdlib bounds u0 <= prod_rect.u0..u2,
 u0 <= projections.u0, u0 <= projections.u1 * )

 -- the second universe [u] is [Sets]'s own object level, one above the
 carriers, and comes from naming [Sets_Cartesian]; the PropEquiv itself
 stays at [u0]. 

 --------
 [Sets_Cartesian] 的乘积集合是按组件定义的 (Instance/Sets/Cartesian.v)。下面的连接是 Coq 的 [and]，写作 `/\`；库中的 `∧` 是 [prod]，并且会将关系保留在 [Type] 中。

 测量：

 product_PropEquiv@{u u0} :
 ∀ {x y : SetoidObject@{u0 u0}},
 PropEquiv@{u0 u0} x → PropEquiv@{u0 u0} y →
 PropEquiv@{u0 u0} (Cartesian.product_obj x y)
 ( * u u0 |= u0 < u，并且标准库限制 u0 <= prod_rect.u0..u2, u0 <= projections.u0, u0 <= projections.u1 * )

 -- 第二个宇宙 [u] 是 [Sets] 自身的对象层次，高于载体，并来自命名 [Sets_Cartesian]；PropEquiv 本身保持在 [u0] 。
*)
#[export] Instance product_PropEquiv {x y : SetoidObject}
  (Px : PropEquiv (is_setoid x)) (Py : PropEquiv (is_setoid y)) :
  PropEquiv (is_setoid (@product_obj Sets Sets_Cartesian x y)).
Proof.
  unshelve refine
    {| pequiv := fun p q => @pequiv _ _ Px (fst p) (fst q)
                            /\ @pequiv _ _ Py (snd p) (snd q) |}.
  - intros p q [H1 H2]; exact (pequiv_to _ _ H1, pequiv_to _ _ H2).
  - intros p q H; split;
      [ exact (pequiv_from _ _ (fst H)) | exact (pequiv_from _ _ (snd H)) ].
Defined.

Example product_pequiv_is_componentwise {x y : SetoidObject}
  (Px : PropEquiv (is_setoid x)) (Py : PropEquiv (is_setoid y))
  (p q : carrier (@product_obj Sets Sets_Cartesian x y)) :
  @pequiv _ _ (product_PropEquiv Px Py) p q
    = (@pequiv _ _ Px (fst p) (fst q) /\ @pequiv _ _ Py (snd p) (snd q))
  := eq_refl.

(** ** Indexed products / ** 索引产品 *)

(*
 [Sets_iprod_equiv F g h := ∀ i, g i ≈ h i] (Instance/Sets/Products.v):
 pointwise in the index, so the [Prop] mirror is pointwise too.  The index
 type [A] is arbitrary and carries no setoid, exactly as [HasIndexedProducts]
 asks.

 Measured:

 iprod_PropEquiv@{u u0 u1 u2 u3} :
 ∀ {A : Type@{u}} (F : A → SetoidObject@{u2 u3}),
 (∀ i : A, PropEquiv@{u2 u3} (F i)) →
 PropEquiv@{u0 u1} (Sets_iprod_obj@{u u0 u1 u2 u3} F)
 ( * u u0 u1 u2 u3 |= u <= u0, u <= u1, u2 <= u0, u3 <= u1 * )

 -- the product's carrier universe [u0] is bounded below by the INDEX and by
 the components, and by nothing else: a product over a carrier-sized index of
 carrier-sized factors stays carrier-sized. 

 --------
 [Sets_iprod_equiv F g h := ∀ i, g i ≈ h i]（实例/集合/乘积.v）：
 在索引上逐点进行，所以 [Prop] 镜像也是逐点的。索引类型 [A] 是任意的，并且不携带任何等价集，正如 [HasIndexedProducts] 所要求的。

 已测量：

 iprod_PropEquiv@{u u0 u1 u2 u3} ：
 ∀ {A : Type@{u}} (F : A → SetoidObject@{u2 u3}),
 (∀ i : A, PropEquiv@{u2 u3} (F i)) →
 PropEquiv@{u0 u1} (Sets_iprod_obj@{u u0 u1 u2 u3} F)
 ( * u u0 u1 u2 u3 |= u <= u0, u <= u1, u2 <= u0, u3 <= u1 * )

 -- 乘积的承载宇宙 [u0] 受索引和组件的下界限制，而没有其他限制：
 在承载大小索引上，对承载大小因子进行的乘积仍保持承载大小。
*)
#[export] Instance iprod_PropEquiv {A : Type} (F : A -> SetoidObject)
  (H : forall i : A, PropEquiv (is_setoid (F i))) :
  PropEquiv (is_setoid (Sets_iprod_obj F)).
Proof.
  unshelve refine {| pequiv := fun g h => forall i : A, @pequiv _ _ (H i) (g i) (h i) |}.
  - intros g h Hgh i. exact (pequiv_to _ _ (Hgh i)).
  - intros g h Hgh i. exact (pequiv_from _ _ (Hgh i)).
Defined.

Example iprod_pequiv_is_pointwise {A : Type} (F : A -> SetoidObject)
  (H : forall i : A, PropEquiv (is_setoid (F i)))
  (g h : carrier (Sets_iprod_obj F)) :
  @pequiv _ _ (iprod_PropEquiv F H) g h
    = (forall i : A, @pequiv _ _ (H i) (g i) (h i)) := eq_refl.

(** ** Limits *)

(*
 [Sets_limit_equiv p q := `1 p ≈ `1 q] (Instance/Sets/Complete.v): the
 compatibility witness carried alongside a family is not compared, so the
 [Prop] mirror is the underlying indexed product's, i.e. pointwise in the
 shape.

 Measured:

 limit_PropEquiv@{u u0 u1 u2} :
 ∀ {D : Category@{u1 u2 u2}} (F : D ⟶ Sets),
 (∀ d : obj[D], PropEquiv@{u2 u2} (F d)) →
 PropEquiv@{u u} (Sets_limit_obj@{u1 u2 u0 u} F)
 ( * u u0 u1 u2 |= u2 < u0, u1 <= u, u2 <= u, plus Projections and
 compose bounds * )

 -- the limit's carrier universe [u] is bounded below by the SHAPE's object
 universe [u1] as well as by the components, which is the size constraint the
 solution-set argument runs into elsewhere. 

 --------
 [Sets_limit_equiv p q := `1 p ≈ `1 q]（实例/集合/完整.v）：随家族携带的兼容性见证不会被比较，因此 [Prop] 镜像是底层索引积的镜像，即在形状上逐点。

 测量：

 limit_PropEquiv@{u u0 u1 u2} ：
 ∀ {D : Category@{u1 u2 u2}} (F : D ⟶ Sets)，
 (∀ d : obj [D] , PropEquiv@{u2 u2} (F d)) →
 PropEquiv@{u u} (Sets_limit_obj@{u1 u2 u0 u} F)
 ( * u u0 u1 u2 |= u2 < u0, u1 <= u, u2 <= u, 以及 Projection 和 compose 上界 * )

 -- 极限的承载类型宇宙 [u] 受到 SHAPE 的对象宇宙 [u1] 以及各组件的下界限制，这就是解集论证在其他地方遇到的大小约束。
*)
#[export] Instance limit_PropEquiv {D : Category} (F : D ⟶ Sets)
  (H : forall d : D, PropEquiv (is_setoid (F d))) :
  PropEquiv (is_setoid (Sets_limit_obj F)).
Proof.
  unshelve refine
    {| pequiv := fun p q : Sets_limit_carrier F =>
                   forall d : D, @pequiv _ _ (H d) (`1 p d) (`1 q d) |}.
  - intros p q Hpq d. exact (pequiv_to _ _ (Hpq d)).
  - intros p q Hpq d. exact (pequiv_from _ _ (Hpq d)).
Defined.

Example limit_pequiv_is_pointwise {D : Category} (F : D ⟶ Sets)
  (H : forall d : D, PropEquiv (is_setoid (F d)))
  (p q : Sets_limit_carrier F) :
  @pequiv _ _ (limit_PropEquiv F H) p q
    = (forall d : D, @pequiv _ _ (H d) (`1 p d) (`1 q d)) := eq_refl.

(* * ** Locally propositional categories / * ** 局部命题范畴 *)

(*
 A category is LOCALLY PROPOSITIONAL when each of its hom-setoids has a
 [Prop] equality.  This is the hypothesis under which a construction that
 turns an object of an ambient category into a concrete algebraic object --
 a functor of points, an internal hom of group objects -- lands back among
 the propositional carriers.  It is deliberately a property of the AMBIENT
 category and says nothing about its objects.

 Instance/Sets.v's [Sets] is not declared to have it, for the reason in this
 file's header; neither is [Cat], and Test/ProbePropEquiv.v measures the
 refusal for [Cat].

 Measured:

 LocallyPropositional@{u u0} : Category@{u0 u u} → Type@{max(Set+1,u,u0)}
 ( * u u0 |=  * )

 -- at the maximum of the category's OBJECT and HOM universes, the object one
 entering through the [∀ x y : C]. 

 --------
 当每个同态集都具有[Prop]等式时，一个范畴是局部命题的。这是在这样的假设下，一个将环境范畴的对象转换为具体代数对象——点函子、群对象的内部同态——的构造能够重新回到命题承载体之中。它故意是环境范畴的一个性质，并不涉及其对象。

 Instance/Sets.v的[Sets]并未声明具有该性质，原因见本文件的头部；[Cat]也没有，而Test/ProbePropEquiv.v衡量了[Cat]对此性质的拒绝程度。

 已测量：

 LocallyPropositional@{u u0} : Category@{u0 u u} → Type@{max(Set+1,u,u0)}
 ( * u u0 |=  * )

 -- 在范畴的对象和态同质性的宇宙的最大值处，通过[∀ x y : C]进入的对象宇宙
*)
Class LocallyPropositional (C : Category) := {
  locally_prop : forall x y : C, PropEquiv (@homset C x y)
}.

(*
 The constructor: naming a [Prop]-valued relation on each hom and the two
 implications is enough.  As in Lib/Setoid/Propositional.v, the relation has
 to be named -- an ascription [(f ≈ g : Prop)] is refused. 

 --------
 构造函数：在每个同态上命名一个 [Prop] 值关系以及两个蕴涵就足够了。如同在 Lib/Setoid/Propositional.v 中，该关系必须命名——拒绝一个 [(f ≈ g : Prop)] 的指定。
*)
Definition LocallyPropositional_of_relation (C : Category)
  (R : forall x y : C, (x ~> y) -> (x ~> y) -> Prop)
  (to : forall (x y : C) (f g : x ~> y), R x y f g -> f ≈ g)
  (from : forall (x y : C) (f g : x ~> y), f ≈ g -> R x y f g) :
  LocallyPropositional C :=
  {| locally_prop := fun x y =>
       PropEquiv_of_relation (R x y) (to x y) (from x y) |}.

(*
 The hom-setoid whose `≈` is Coq's [eq] (Theory/Category.v) is
 propositional outright.  Any category declaring [homset := Morphism_equality]
 -- Instance/One.v's [_1] and Instance/Zero.v's [_0] among them -- is
 therefore locally propositional by [LocallyPropositional_of_relation] with
 [R := fun _ _ => eq]; the instances for the individual such categories are
 left to the files that need them, since each would pull its own import in
 here. 

 --------
 其同态集合等价类，其 `≈` 是 Coq 的 [eq]（Theory/Category.v），是直接命题性的。任何声明 [homset := Morphism_equality] 的范畴 —— 其中包括 Instance/One.v 的 [_1] 和 Instance/Zero.v 的 [_0] —— 因此通过 [LocallyPropositional_of_relation] 和 [R := fun _ _ => eq] 是局部命题性的；各个此类范畴的实例留给需要它们的文件，因为每个都会在此处导入自己的内容。
*)
#[export] Instance Morphism_equality_PropEquiv {ob : Type}
  {hom : ob -> ob -> Type} (x y : ob) :
  PropEquiv (@Morphism_equality ob hom x y).
Proof.
  unshelve refine {| pequiv := @eq (hom x y) |}.
  - intros f g h; exact h.
  - intros f g h; exact h.
Defined.

(*
 The same statement for a whole category, as a transport rather than an
 instance: "C's hom-setoid IS strict equality" is not a property of an
 arbitrary [C] that instance resolution can check, so it is taken as a
 hypothesis. 

 --------
 对整个类别的相同陈述，作为一种传输而不是一个实例：“C 的同类集合 IS 严格相等”不是任意 [C] 的性质，实例解析无法检查，因此它被视为一个假设。
*)
Definition LocallyPropositional_of_eq (C : Category)
  (H : forall x y : C, @homset C x y = Morphism_equality x y) :
  LocallyPropositional C.
Proof.
  constructor.
  intros x y.
  rewrite (H x y).
  exact (Morphism_equality_PropEquiv x y).
Defined.
