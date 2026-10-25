Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.End.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * Ends in [Sets], computed directly / * * 以 [Sets] 结尾，直接计算 *)

(*
 nLab:      https://ncatlab.org/nlab/show/end
 Wikipedia: https://en.wikipedia.org/wiki/End_(category_theory)

 For a functor of mixed variance [F : C^op ∏ C ⟶ Sets] the end [∫_x F(x,x)]
 is realised here as a concrete setoid, with no recourse to
 function-extensionality.  The carrier is the setoid of "compatible
 families": a choice [s x : F(x,x)] for every object [x : C], subject to the
 wedge (dinaturality) constraint

 fmap[F] (id, f) (s x)  ≈  fmap[F] (op f, id) (s y)      for f : x ~> y.

 Both routes land in [F(x,y)]: the left applies the covariant action [F(x,f)]
 to [s x], the right the contravariant action [F(f,y)] to [s y].  The pair
 [(id, f)] is a morphism [(x,x) ~> (x,y)] of [C^op ∏ C] whose first component
 is an op-morphism, following the variance convention of Theory/Dinatural and
 Structure/Wedge; the pair [(op f, id)] is the morphism [(y,y) ~> (x,y)].

 The equivalence on this carrier is pointwise: two families are identified
 when they agree at every object up to that object's [≈].  Because the apex
 is a setoid, this equivalence is carried by the object itself rather than by
 a quotient type, so the construction is [funext]-free.

 The universal wedge has the projection [s ↦ s x] as its leg at [x]; the wedge
 condition is exactly the family's own constraint.  The end UMP sends a
 competing wedge [W] to the mediator [e ↦ (fun x => wedge_map[W] e)], whose
 compatibility constraint is [W]'s own wedge law read at [e]; commuting and
 uniqueness are both pointwise.  This yields [Sets_End F : End F] for every
 [F : C^op ∏ C ⟶ Sets].

 As with every Sets-valued (co)limit in this development the indexing
 category's object and hom levels are constrained to sit below Sets' carrier
 level, so that the family type [∀ x, F(x,x)] and its constraint fit as a
 setoid carrier; these smallness constraints are inferred by universe
 polymorphism and recorded on [Sets_End]. 

 --------
 nLab：       https://ncatlab.org/nlab/show/end 
 维基百科：  https://en.wikipedia.org/wiki/End_(category_theory) 

 对于一个混合方差的函子  [F : C^op ∏ C ⟶ Sets] ，其余对象  [∫_x F(x,x)] 
 在这里被实现为一个具体的集合等价类，无需
 借助函数外延性。载体是“兼容族”的集合等价类：即对于每个对象  [x : C] ，选择  [s x : F(x,x)] ，满足
 楔形（自然性）约束

 fmap [F]  (id, f) (s x)  ≈  fmap [F]  (op f, id) (s y)      对于 f : x ~> y。

 两种路径都到达  [F(x,y)] ：左边应用协变作用  [F(x,f)] 
 于  [s x] ，右边应用逆变作用  [F(f,y)] 于  [s y] 。该对
 [(id, f)]  是  [C^op ∏ C] 的一个态射  [(x,x) ~> (x,y)] ，其第一个分量是一个 op-态射，遵循 Theory/Dinatural 和
 Structure/Wedge 的方差约定；该对  [(op f, id)]  是态射  [(y,y) ~> (x,y)] 。这个载体上的等价是逐点的：当两个族在每个对象上达成一致（直到该对象的 [≈]）时，它们就被识别为相同。因为顶点是集合等价类，这个等价由对象本身而非商类型承载，所以该构造是 [funext] 自由的。

 普遍楔形在 [x] 处以投影 [s ↦ s x] 作为其边；楔形条件正好是族自身的约束。端对象 UMP 将一个竞争楔形 [W] 发送到中介 [e ↦ (fun x => wedge_map[W] e)]，其兼容性约束是 [W] 在 [e] 处的自身楔形律；交换性和唯一性都是逐点的。这为每个 [F : C^op ∏ C ⟶ Sets] 得出 [Sets_End F : End F]。与本开发中的每一个集合值 (co)极限一样，索引范畴的对象和态射层级被限制在集合的承载层级之下，以便家族类型 [∀ x, F(x,x)] 及其约束可以作为集合体承载；这些小尺度约束通过宇宙多态性推断，并记录在 [Sets_End] 上。
*)

Section SetsEnd.

Context {C : Category}.
Context (F : C^op ∏ C ⟶ Sets).

(*
 The end carrier: compatible families on the diagonal.  The second component
 is the wedge constraint, phrased with the two mixed-variance actions of [F].
 Each pair is annotated with its [C^op ∏ C] hom type so that the product-
 category objects are determined without higher-order unification. 

 --------
 终端载体：对角线上的兼容族。第二个分量是楔形约束，用[F]的两个混合方差作用来表述。每一对都标注有其[C^op ∏ C]同构类型，以便在不进行高阶统一的情况下确定积范畴对象。
*)
Definition end_family : Type :=
  { s : ∀ x : C, F (x, x)
  & ∀ (x y : C) (f : x ~{C}~> y),
      fmap[F] ((@id (C^op) x, f) : (x, x) ~{C^op ∏ C}~> (x, y)) (s x)
        ≈ fmap[F] ((op f, @id C y) : (y, y) ~{C^op ∏ C}~> (x, y)) (s y) }.

(*
 Pointwise equivalence of families: agreement at every object, up to the
 codomain setoid at that object. 

 --------
 族的逐点等价：在每个对象处都一致，直到该对象的余域集合等价为止。
*)
Definition end_family_equiv (s t : end_family) : Type :=
  ∀ x : C, `1 s x ≈ `1 t x.

#[local] Obligation Tactic := idtac.

(*
 The end object as a [SetoidObject]: the family carrier under pointwise [≈].
 Reflexivity, symmetry and transitivity are inherited objectwise from the
 setoids [F(x,x)]. 

 --------
 终对象作为 [SetoidObject]：在逐点 [≈] 下的族承载器。  
 自反性、对称性和传递性从集合类 [F(x,x)] 逐对象继承。
*)
Program Definition Sets_End_obj : SetoidObject := {|
  carrier   := end_family;
  is_setoid := {| equiv := end_family_equiv |}
|}.
Next Obligation.
  constructor.
  - intros s x; reflexivity.
  - intros s t H x; symmetry; exact (H x).
  - intros s t u H1 H2 x; transitivity (`1 t x); [exact (H1 x) | exact (H2 x)].
Qed.

(*
 The projection leg at [x]: evaluate a family at [x].  It respects the
 pointwise equivalence by definition. 

 --------
 在 [x] 的投影腿：评估在 [x] 的一个家族。根据定义，它遵循逐点等价。
*)
Program Definition end_projection (x : C) :
  Sets_End_obj ~{Sets}~> F (x, x) := {|
  morphism := fun s => `1 s x
|}.
Next Obligation.
  intros x s t Hst; exact (Hst x).
Qed.

(*
 The universal wedge of the end: apex [Sets_End_obj] with the projection
 legs.  Its wedge condition is precisely the family constraint (the second
 component of each family), applied to the argument.  The wedge is assembled
 with the explicit constructor because [Structure/End] rebinds the name
 [wedge_obj] as its [End ~> Wedge] coercion, which shadows the record label. 

 --------
 末端的通用楔子：顶点 [Sets_End_obj] 和投影腿。它的楔形条件正是族约束（每个族的第二个组成部分），应用于参数。楔子是通过显式构造函数组装的，因为 [Structure/End] 重新绑定名称 [wedge_obj] 作为其 [End ~> Wedge] 强制类型转换，这会遮蔽记录标签。
*)
Program Definition Sets_End_Wedge : Wedge F :=
  @Build_Wedge C Sets F Sets_End_obj (fun x => end_projection x) _.
Next Obligation.
  intros x y f s.
  exact (`2 s x y f).
Qed.

(*
 Compatibility constraint of the mediator.  Given a competing wedge [W] and
 an element [e] of its apex, the family [fun x => wedge_map[W] e] satisfies
 the end constraint because that constraint, read pointwise at [e], is
 exactly [W]'s own wedge law. 

 --------
 中介者的兼容性约束。给定一个竞争楔形 [W] 和其顶点的一个元素 [e]，族 [fun x => wedge_map[W] e] 满足端点约束，因为在 [e] 处逐点读取该约束时，正好是 [W] 自身的楔形法则。
*)
Lemma end_mediator_constraint (W : Wedge F) (e : Wedge_to_obj F W) :
  ∀ (x y : C) (f : x ~{C}~> y),
    fmap[F] ((@id (C^op) x, f) : (x, x) ~{C^op ∏ C}~> (x, y))
            (@wedge_map _ _ _ W x e)
      ≈ fmap[F] ((op f, @id C y) : (y, y) ~{C^op ∏ C}~> (x, y))
                (@wedge_map _ _ _ W y e).
Proof.
  intros x y f.
  exact (@ump_wedges _ _ _ W x y f e).
Qed.

(* The underlying function of the mediator: package the legs of [W] at [e] into a family, carrying the compatibility constraint above as its witness. / 中介者的基本功能：将 [W] 在 [e] 的腿打包成一个族，并携带上述兼容性约束作为其证明。 *)
Definition end_mediator_fun (W : Wedge F) (e : Wedge_to_obj F W) :
  end_family :=
  (fun x => @wedge_map _ _ _ W x e; end_mediator_constraint W e).

(*
 The mediator as a setoid map [W ~> Sets_End_obj].  It respects [≈] because
 each leg [wedge_map[W]] does. 

 --------
 调解者作为一个集合映射 [W ~> Sets_End_obj]。它遵循 [≈]，因为每一条线段 [wedge_map[W] ] 都遵循。
*)
Program Definition Sets_End_mediator (W : Wedge F) :
  Wedge_to_obj F W ~{Sets}~> Sets_End_obj := {|
  morphism := end_mediator_fun W
|}.
Next Obligation.
  intros W e e' Hee' x.
  exact (proper_morphism (@wedge_map _ _ _ W x) e e' Hee').
Qed.

(*
 The end and its universal property.  For every wedge [W] the mediator above
 is the unique setoid map to the end recovering each leg of [W] by
 post-composition with the corresponding projection; commuting holds by
 reflexivity and uniqueness is the pointwise reading of the leg equations. 

 --------
 端及其普遍性。对于每个楔 [W]，上述中介是到端的唯一集合同构映射，通过与相应的投影后合成来恢复 [W] 的每条腿；对合由自反性成立，唯一性是腿方程的逐点表示。
*)
Program Definition Sets_End : End F := {|
  end_wedge := Sets_End_Wedge
|}.
Next Obligation.
  intro W.
  unshelve refine (Build_Unique _ _ _ (Sets_End_mediator W) _ _).
  - intros x e; reflexivity.
  - intros v Hv e x; symmetry; exact (Hv x e).
Qed.

End SetsEnd.

Arguments end_family {C} F.
Arguments Sets_End_obj {C} F.
Arguments Sets_End {C} F.
