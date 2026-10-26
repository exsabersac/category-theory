(*
   * * Exercise II.4.8: the cylinder and arrow-category encodings agree 

   --------
   * * 练习 II.4.8：圆柱和箭头范畴编码一致
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Product.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Arrow.Functor.
Require Import Category.Construction.Cylinder.
Require Import Category.Instance.Two.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.Cat.Cartesian.Closed.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Shapes.

Generalizable All Variables.

(*
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 §II.4 Exercise 8, printed p. 42 (PDF 52) — maclane:II.4:ex8
 Book:      Awodey, “Category Theory” (1st ed., 2005 pre-print), §7.7,
 Example 7.16, printed p. 171 (PDF pp. 180–181) —
 awodey:7.7:example16

 Exercise II.4.8, and Awodey's “transcendental deduction”: under the
 exponential transpose of Cat, the cylinder encoding of a natural
 transformation — a functor C ∏ 2 ⟶ B restricting to its boundary
 functors — corresponds to the arrow-category encoding — a functor
 C ⟶ B⃗ — of the SAME transformation.  The chain is: [Cat_Closed]'s
 [exp_iso] transposes F : C ∏ 2 ⟶ B to C ⟶ [_2, B]; Theory/Shapes.v's
 [Arrow_of_Fun] (the [to] leg of [Two_Fun_Arrow]) turns functors out
 of the walking arrow into arrow objects; and
 Construction/Arrow/Functor.v's [Arrow_extract] reads the classified
 triple back off.  [cylinder_arrow_agree] states that this composite
 carries [Cyl_functor τ] to a triple equivalent to (S, T, τ) in the
 triple setoid — the two encodings classify the same transformation.

 - [Cyl_transpose]: the exponential transpose of a cylinder
 functor, C ⟶ [_2, B]
 - [Cyl_to_arrow]: the transpose pushed into the arrow category,
 C ⟶ B⃗
 - [cylinder_arrow_agree]: extracting the triple recovers
 (S, T, τ) up to [ArrowTriple_Setoid]

 Design:

 1. UNIVERSE SCOPE, MEASURED.  The composite here elaborates at
 [Category@{Set Set Set}] — object universe INCLUDED — so it
 cannot be applied to categories whose objects live above [Set]
 ([cylinder_arrow_agree_at_two] below witnesses that it has
 content at small categories).  This is a stronger pin than the
 donor's: Theory/Shapes.v's [Arrow_of_Fun] keeps its object
 universe free, and whether the object pin introduced by this
 composite is forced by the [Cat]/[Fun] plumbing or avoidable
 has not been settled here.  It is why this file is separate
 from Construction/Cylinder.v, whose universal property carries
 no Set-level pin at all (verified by instantiation strictly
 above [Set]).

 2. NATURALITY IN THE TRIPLE, IN THE SETOID SENSE.
 [cylinder_arrow_natural] below states it: triples equivalent
 in [ArrowTriple_Setoid] are carried to equivalent extracted
 triples — a corollary of the pointwise agreement and the
 triple setoid's own equivalence.  The stronger packaging of
 the correspondence as an isomorphism in Sets (the shape
 [Arrow_classification] uses) is not delivered here: the
 object-level bijection of the two encodings is already the
 composite of [Arrow_classification] with the exponential
 transpose, and is not restated. 

 --------
 书籍：Mac Lane，《为工作数学家准备的范畴论》，第2版，§II.4 练习8，印刷版第42页（PDF第52页）—— maclane:II.4:ex8
 书籍：Awodey，《范畴论》（第1版，2005年预印本），§7.7，例7.16，印刷版第171页（PDF第180–181页）—— awodey:7.7:example16练习 II.4.8 以及 Awodey 的“先验演绎”：在 Cat 的指数转置下，自然变换的圆柱编码——一个将 C ∏ 2 映射到 B 并限制到其边界函子——对应于箭头范畴编码——同一变换的函子 C ⟶ B⃗。链条是：[Cat_Closed] 的 [exp_iso] 将 F : C ∏ 2 ⟶ B 转置为 C ⟶ [_2, B]；Theory/Shapes.v 的 [Arrow_of_Fun]（[Two_Fun_Arrow] 的 [to] 分支）将行走箭头的函子转为箭头对象；Construction/Arrow/Functor.v 的 [Arrow_extract] 再次读取已分类的三元组。[cylinder_arrow_agree] 陈述这个复合将 [Cyl_functor τ] 转换为与三元组集合中的 (S, T, τ) 等价的三元组——这两种编码对同一变换进行分类。-  [Cyl_transpose]：圆柱函子指数的转置  
 函子 C ⟶ [_2, B]  
 -  [Cyl_to_arrow]：将转置推入箭头范畴，  
 函子 C ⟶ B⃗  
 -  [cylinder_arrow_agree]：提取三重结构可以恢复  
 (S, T, τ) 至 [ArrowTriple_Setoid]  

 设计：1. 宇宙范围，可测量。这里的组合在 [Category@{Set Set Set}] 处展开 —— 对象宇宙包含在内 —— 因此不能应用于那些对象位于 [Set] 之上的类别（[cylinder_arrow_agree_at_two] 以下证明它在小类别上有内容）。这比捐赠者的条件更强：Theory/Shapes.v 的 [Arrow_of_Fun] 保持其对象宇宙自由，并且该组合引入的对象针是否受 [Cat] / [Fun] 管线强制或可避免，这里尚未确定。这就是为什么该文件与 Construction/Cylinder.v 分开的原因，后者的泛性性质根本不携带 Set 级别的针（由严格高于 [Set] 的实例化验证）。2. 三元组的自然性，在集合等价的意义上。
 下面的 [cylinder_arrow_natural] 说明了这一点：在 [ArrowTriple_Setoid] 中等价的三元组会被映射为等价的提取三元组——这是逐点一致性和三元组集合等价自身的一个推论。更强形式的对应包装为集合中的同构（[Arrow_classification] 使用的形式）在这里并未提供：两种编码的对象级双射已经是 [Arrow_classification] 与指数转置的复合，并且没有被重新表述。
*)

(* * ** The transpose and its arrow-category form / * ** 转置及其箭头范畴形式 *)

Definition Cyl_transpose {C B : Category} (F : C ∏ _2 ⟶ B) :
  C ⟶ [_2, B] :=
  @curry' Cat Cat_Cartesian Cat_Closed C _2 B F.

Definition Cyl_to_arrow {C B : Category} (F : C ∏ _2 ⟶ B) :
  C ⟶ @Arrow B :=
  Arrow_of_Fun ◯ Cyl_transpose F.

(* * ** The two encodings classify the same transformation / * ** 这两种编码对相同的转换进行分类 *)

Lemma cylinder_arrow_dom_nat {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  ∀ x y (f : x ~{C}~> y),
    fmap[Arrow_dom (Cyl_to_arrow (Cyl_functor τ))] f
      ≈ from (@iso_id B (S y)) ∘ fmap[S] f ∘ to (@iso_id B (S x)).
Proof.
  intros x y f; simpl; cat.
Qed.

Lemma cylinder_arrow_cod_nat {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  ∀ x y (f : x ~{C}~> y),
    fmap[Arrow_cod (Cyl_to_arrow (Cyl_functor τ))] f
      ≈ from (@iso_id B (T y)) ∘ fmap[T] f ∘ to (@iso_id B (T x)).
Proof.
  intros x y f; simpl; cat.
Qed.

Theorem cylinder_arrow_agree {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  @equiv _ (@ArrowTriple_Setoid C B)
    (Arrow_extract (Cyl_to_arrow (Cyl_functor τ)))
    (S; (T; τ)).
Proof.
  exists (existT _ (fun c => iso_id) (cylinder_arrow_dom_nat τ)).
  exists (existT _ (fun c => iso_id) (cylinder_arrow_cod_nat τ)).
  intro c; simpl; cat.
Qed.

#[local] Existing Instance ArrowTriple_Setoid.

(*
 Naturality in the triple, in the setoid sense: equivalent triples
 are carried to equivalent extracted triples. 

 --------
 三元组中的自然性，在集合等价意义上：等价的三元组会被转化为等价的提取三元组。
*)
Corollary cylinder_arrow_natural {C B : Category}
          {S T S' T' : C ⟶ B} (τ : S ⟹ T) (τ' : S' ⟹ T')
          (E : ((S; (T; τ)) : ArrowTriple C B) ≈ (S'; (T'; τ'))) :
  (Arrow_extract (Cyl_to_arrow (Cyl_functor τ)) : ArrowTriple C B)
    ≈ Arrow_extract (Cyl_to_arrow (Cyl_functor τ')).
Proof.
  transitivity ((S; (T; τ)) : ArrowTriple C B).
  - apply cylinder_arrow_agree.
  - transitivity ((S'; (T'; τ')) : ArrowTriple C B).
    + exact E.
    + symmetry; apply cylinder_arrow_agree.
Qed.

(*
 The theorem has content at small categories; the walking arrow
 itself is the donor's own precedent ([Two_Fun_Arrow_at_three]). 

 --------
 该定理在小范畴中具有内容；步行箭头本身就是给予者自身的先例（[Two_Fun_Arrow_at_three]）。
*)
Example cylinder_arrow_agree_at_two {S T : _2 ⟶ _2} (τ : S ⟹ T) :
  @equiv _ (@ArrowTriple_Setoid _2 _2)
    (Arrow_extract (Cyl_to_arrow (Cyl_functor τ)))
    (S; (T; τ)) :=
  cylinder_arrow_agree τ.
