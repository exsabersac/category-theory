Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(* * * The free coloured-PROP category on a signature / * * 签名上的自由彩色-PROP类别 *)

(*
 nLab: https://ncatlab.org/nlab/show/PROP
 nLab: https://ncatlab.org/nlab/show/free+category
 Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
 Wikipedia: https://en.wikipedia.org/wiki/Free_category

 A coloured PROP over a set [Colour] of wire types is a strict
 symmetric monoidal category whose objects are the finite words
 [list Colour] and whose tensor on objects is concatenation.  The
 free coloured PROP on a signature [S] has as its [cs ~> ds] arrows
 the typed string-diagram terms [CTerm S cs ds] quotiented by the
 laws of a strict symmetric monoidal category; this is the standard
 “free = syntactic” construction, the many-sorted analogue of
 [Construction/PROP/Free.v], with [list Colour] replacing [nat] and
 [++] replacing [Nat.add] throughout.

 This file assembles the underlying [Category] layer of that
 quotient together with its tensor bifunctor:

 - obj        := list Colour                (objects: colour words)
 - hom cs ds  := CTerm S cs ds mod CTermEq  (typed diagrams / ≈)
 - id         := CT_id                      (identity wires)
 - compose    := CT_comp                    (sequential composition)
 - tensor     := CFreeCat_Tensor            (parallel composition)

 The hom-equivalence ≈ is [CTermEq S], so the [Category] laws
 (left/right unit, associativity) are exactly its [CTE_id_left] /
 [CTE_id_right] / [CTE_assoc] constructors, and [compose_respects]
 is its [CTE_comp_cong] congruence.  The [Monoidal],
 [SymmetricMonoidal], and strictness layers — which complete
 [CFreeCat S] to a free strict symmetric monoidal category and then
 to the first inhabitant of [Construction/ColouredPROP.v]'s class —
 live in the successor files ([Construction/ColouredPROP/Cast.v],
 [Monoidal.v], [Braided.v], [Instance.v]).

 Layout note: this file merges the one-sorted spine's donor pair
 [Construction/PROP/Free.v] + [Construction/PROP/Tensor.v].  The
 coloured tensor bifunctor needs nothing beyond the [CTE_tens_*]
 constructors already provided by the equational theory, so it
 lives here rather than in a file of its own.

 Following the coloured spine's proof-using discipline, the
 inductives ([CTerm], [CTermEq]) were declared in sections that
 closed in their home files; every statement below carries the
 signature [S] explicitly. 

 --------
 nLab:  https://ncatlab.org/nlab/show/PROP 
 nLab:  https://ncatlab.org/nlab/show/free+category 
 维基百科:  https://en.wikipedia.org/wiki/PROP_(category_theory) 
 维基百科:  https://en.wikipedia.org/wiki/Free_category 

 一个在集合 [Colour] 上的有色 PROP 是一个严格的对称幺半范畴，其对象是有限字 [list Colour]，对象上的张量是连接。 
 在签名 [S] 上的自由有色 PROP 的 [cs ~> ds] 箭头是类型化的字符串图项 [CTerm S cs ds]，按严格对称幺半范畴的规律取商；这是标准的“自由 = 句法”构造，是 [Construction/PROP/Free.v] 的多排序类比，Z中用 [list Colour] 代替 [nat]，用 [++] 代替 [Nat.add]。

 该文件将该商的基础 [Category] 层及其张量双函子组合在一起：- obj        := list Colour                （对象：颜色词）
 - hom cs ds  := CTerm S cs ds mod CTermEq  （类型化图 / ≈）
 - id         := CT_id                      （恒等线）
 - compose    := CT_comp                    （顺序组合）
 - tensor     := CFreeCat_Tensor            （并行组合）

 同态等价 ≈ 是  [CTermEq S] ，所以  [Category] 定律（左/右单位、结合律）恰好是其  [CTE_id_left] / [CTE_id_right] / [CTE_assoc] 构造器，而  [compose_respects] 是其  [CTE_comp_cong] 同余。[Monoidal]、[SymmetricMonoidal] 和严格层——它们将 [CFreeCat S] 完成为自由严格对称张量范畴，然后作为 [Construction/ColouredPROP.v] 类的第一个实例——存在于后续文件中（[Construction/ColouredPROP/Cast.v]、[Monoidal.v]、[Braided.v]、[Instance.v]）。布局说明：此文件合并了单排序脊的供体对 [Construction/PROP/Free.v] + [Construction/PROP/Tensor.v]。彩色张量双函子不需要超出方程理论已提供的 [CTE_tens_*] 构造，因此它存在于这里，而不是单独的文件中。

 遵循彩色脊的使用证明的规范，归纳类型 ([CTerm], [CTermEq]) 在其所在文件中关闭的部分中声明；下面的每条语句都明确带有签名 [S]。
*)

Section CFreeCategory.

Context {Colour : Type}.
Context (S : CSignature Colour).

(*
   * The hom-setoid: terms are quotiented by [CTermEq]. 

   --------
   * Hom-集合：术语按 [CTermEq] 进行等价类化。
*)
#[export] Program Instance CTerm_Setoid {cs ds : list Colour} :
  Setoid (CTerm S cs ds) := {|
  equiv := @CTermEq Colour S cs ds
|}.
Next Obligation.
  constructor.
  - intros t; apply CTE_refl.
  - intros s t; apply CTE_sym.
  - intros s t u; apply CTE_trans.
Defined.

(*
   * Composition is the [CT_comp] constructor; it respects [CTermEq] by
   [CTE_comp_cong]. 

   --------
   * 组成是 [CT_comp] 构造函数；它通过 [CTE_comp_cong] 尊重 [CTermEq]。
*)
#[export] Program Instance CT_comp_respects {cs ds es : list Colour} :
  Proper (equiv ==> equiv ==> equiv) (@CT_comp Colour S cs ds es).
Next Obligation.
  proper.
  apply CTE_comp_cong; assumption.
Qed.

(*
   * Tensor (parallel composition) is also Proper for [CTermEq], by
   [CTE_tens_cong].  Allows [rewrite] under [CT_tens]. 

   --------
   * 张量（并行组合）对于 [CTermEq] 来说也是 Proper，由 [CTE_tens_cong] 给出。允许 [rewrite] 在 [CT_tens] 下。
*)
#[export] Program Instance CT_tens_respects
  {cs1 ds1 cs2 ds2 : list Colour} :
  Proper (equiv ==> equiv ==> equiv) (@CT_tens Colour S cs1 ds1 cs2 ds2).
Next Obligation.
  proper.
  apply CTE_tens_cong; assumption.
Qed.

(** The free category on [S]. / 在 [S] 上的免费分类。 *)
Program Definition CFreeCat : Category := {|
  obj      := list Colour;
  hom      := @CTerm Colour S;
  homset   := @CTerm_Setoid;
  id       := CT_id;
  compose  := @CT_comp Colour S;
  compose_respects := @CT_comp_respects;
  id_left  := fun cs ds f => CTE_id_left f;
  id_right := fun cs ds f => CTE_id_right f;
  comp_assoc := fun cs ds es fs f g h => CTE_sym _ _ (CTE_assoc f g h);
  comp_assoc_sym := fun cs ds es fs f g h => CTE_assoc f g h
|}.

End CFreeCategory.

Arguments CFreeCat {Colour} S : assert.
Arguments CT_comp_respects {Colour S cs ds es}.
Arguments CT_tens_respects {Colour S cs1 ds1 cs2 ds2}.

(* * * Parallel-composition bifunctor on CFreeCat / * * CFreeCat 上的平行组合双函子 *)

(*
 nLab: https://ncatlab.org/nlab/show/monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category

 The monoidal product of a (strict, symmetric) monoidal category is
 a bifunctor [⊗ : C ∏ C ⟶ C].  For the free coloured PROP
 [CFreeCat S] this is the parallel composition of typed string
 diagrams, with boundaries given by concatenation:

 - on objects:    [(cs, ds) ↦ cs ++ ds]  (tensor on objects is [++])
 - on morphisms:  [(f, g) ↦ CT_tens f g], so [f : cs1 ~> ds1] and
 [g : cs2 ~> ds2] yield
 [f ⊗ g : cs1 ++ cs2 ~> ds1 ++ ds2]

 The bifunctor laws (a functor out of the product category
 [CFreeCat S ∏ CFreeCat S]) follow from the [CTE_tens_*]
 constructors of the [CTermEq] quotient relation:
 - respectfulness (fmap_respects):  [CTE_tens_cong]
 - identity preservation (fmap_id): [CTE_tens_id]
 [id_cs ⊗ id_ds ≈ id_(cs ++ ds)]
 - composition preservation (fmap_comp), i.e. the middle-four
 interchange [(f1 ⊙c f2) ⊗ (g1 ⊙c g2) ≈ (f1 ⊗ g1) ⊙c (f2 ⊗ g2)]:
 [CTE_interchange] (used via [CTE_sym], since the constructor
 states the reverse orientation). 

 --------
 nLab:  https://ncatlab.org/nlab/show/monoidal+category 
 维基百科:  https://en.wikipedia.org/wiki/Monoidal_category 

 （严格的、对称的）单模范畴的单模积是一个双函子  [⊗ : C ∏ C ⟶ C] 。对于自由有色 PROP  [CFreeCat S] ，这是带有边界的类型化字符串图的并行组合，边界通过连接给出：

 - 在对象上:     [(cs, ds) ↦ cs ++ ds]   （对象上的张量是 [++] ）
 - 在态射上:   [(f, g) ↦ CT_tens f g] ，因此 [f : cs1 ~> ds1] 和 [g : cs2 ~> ds2] 产生 [f ⊗ g : cs1 ++ cs2 ~> ds1 ++ ds2]双函子定律（来自乘积范畴 [CFreeCat S ∏ CFreeCat S] 的函子）遵循 [CTE_tens_*] 商关系的构造器：
 - 尊重性（fmap_respects）：[CTE_tens_cong]
 - 恒等保持（fmap_id）：[CTE_tens_id]
 [id_cs ⊗ id_ds ≈ id_(cs ++ ds)]
 - 复合保持（fmap_comp），即中间四元互换 [(f1 ⊙c f2) ⊗ (g1 ⊙c g2) ≈ (f1 ⊗ g1) ⊙c (f2 ⊗ g2)]：
 [CTE_interchange]（通过 [CTE_sym] 使用，因为构造器说明了相反的方向）。
*)

Section CFreeTensor.

Context {Colour : Type}.
Context (S : CSignature Colour).

(** The tensor bifunctor on [CFreeCat S]. / 在 [CFreeCat S] 上的张量双函子。 *)
Program Definition CFreeCat_Tensor :
  CFreeCat S ∏ CFreeCat S ⟶ CFreeCat S := {|
  fobj := fun p => (fst p ++ snd p)%list;
  fmap := fun p q m =>
    @CT_tens Colour S (fst p) (fst q) (snd p) (snd q) (fst m) (snd m)
|}.
Next Obligation.
  unfold Proper, respectful.
  intros [f1 f2] [g1 g2] [Hf Hg]; simpl in *.
  apply CTE_tens_cong; assumption.
Qed.
Next Obligation.
  apply CTE_tens_id.
Qed.
Next Obligation.
  apply CTE_sym, CTE_interchange.
Qed.

End CFreeTensor.

Arguments CFreeCat_Tensor {Colour} S : assert.
