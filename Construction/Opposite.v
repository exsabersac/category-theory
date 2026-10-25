Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** The opposite (dual) category C^op. / 对偶（反向）范畴 C^op。 *)

(*
 nLab: https://ncatlab.org/nlab/show/opposite+category
 Wikipedia: https://en.wikipedia.org/wiki/Opposite_category

 C^op has the same objects as C, with hom-sets reversed,
 hom[C^op] x y := hom[C] y x, so that f : y ~> x in C is read as
 f : x ~{C^op}~> y.  Identities are unchanged and composition is reversed:
 g ∘ f in C^op is f ∘ g in C.

 Duality is built in here so that (C^op)^op = C holds by reflexivity: the
 two associativity laws are swapped (comp_assoc uses comp_assoc_sym and vice
 versa) and compose_respects is re-bracketed symmetrically, so applying the
 construction twice lands every field back on its original (see op_invol,
 provable by [reflexivity]). 

 --------
 nLab：https://ncatlab.org/nlab/show/opposite+category 
 维基百科：https://en.wikipedia.org/wiki/Opposite_category 

 C^op 与 C 具有相同的对象，但同态集合被反转，
 hom [C^op]  x y := hom [C]  y x，因此在 C 中 f : y ~> x 可读作
 f : x ~{C^op}~> y。恒等映射保持不变，组合被反转：
 在 C^op 中 g ∘ f 相当于在 C 中 f ∘ g。

 此处内置对偶性，因此 (C^op)^op = C 通过自反性成立：
 两个结合律交换（comp_assoc 使用 comp_assoc_sym，反之亦然），并且 compose_respects 被对称地重新加括号，所以应用两次该构造会使每个字段回到原来的位置（见 op_invol，可由 [reflexivity] 证明）。
*)

(*
 Duality: the principle, its history, and what strictness buys

 nLab (duality): https://ncatlab.org/nlab/show/duality
 nLab (presheaf): https://ncatlab.org/nlab/show/presheaf
 Wikipedia: https://en.wikipedia.org/wiki/Dual_(category_theory)
 Wikipedia: https://en.wikipedia.org/wiki/Duality_(projective_geometry)

 The opposite category is the theorem-doubling device of category
 theory.  Because the axioms for a category are invariant under
 reversing every arrow, a statement holds in C precisely when its dual —
 source and target swapped, composites read in the other order — holds
 in C^op, so any theorem proved for all categories yields its dual with
 no further work (Mac Lane, "Categories for the Working Mathematician",
 Springer 1978, p. 33; Awodey, "Category Theory", Oxford 2010).  nLab
 states the point at the level of the theory itself: the signature of
 the elementary theory of categories carries a nontrivial involution, so
 every formal theorem has a formal dual — the same phenomenon as the
 meet/join duality of lattices and the point/line duality of the
 projective plane.

 That precedent is older than the subject by a century.  In the
 projective geometry of the early nineteenth century, Gergonne, who
 coined the term "duality", printed dual theorems side by side in his
 journal, while Poncelet held the point/line interchange to be a
 consequence of the theory of poles and polars: two points determine a
 line, two lines meet in a point, one theorem read twice.  Category
 theory then internalized the phenomenon from its first pages —
 Eilenberg and Mac Lane open with the dual vector space, coin
 "contravariant" for the arrow-reversing functor, and observe that the
 double dual is natural where the single dual is not (Eilenberg and
 Mac Lane, "General theory of natural equivalences", Trans. Amer. Math.
 Soc. 58 1945).  Mac Lane soon made duality itself the object of study:
 restate the element-based notions of group theory purely in terms of
 homomorphisms and composition, and dual axioms yield dual theorems
 (Mac Lane, "Groups, categories and duality", Proc. Nat. Acad. Sci. 34
 1948; "Duality for groups", Bull. Amer. Math. Soc. 56 1950).  Pursued
 through Buchsbaum and Grothendieck, that program produced abelian
 categories, whose self-dual axioms hand homological algebra two dual
 results out of one (Goswami and Janelidze, "Duality in non-abelian
 algebra IV", arXiv:1704.01863 2017).

 Downstream of this file the library takes dual concepts by definition,
 not by analogy: a comonad is a monad on C^op (Theory/Monad.v), a
 colimit is a limit of the opposite diagram (Structure/Limit.v), initial
 objects are terminal in C^op (Structure/Initial.v), coproducts are
 opposite products (Structure/Cocartesian.v), a coend is an end of the
 opposed functor (Structure/Coend.v), and F-coalgebras apply the
 construction twice (Construction/FCoalg.v).  Each one-line definition
 inherits the entire theory of its primal concept.  Contravariance is
 equally the substrate of representability: a presheaf is a functor out
 of U^op (Theory/Sheaf.v), and the curried hom [Curried_Hom] of
 Functor/Hom.v, itself a functor from C^op, feeds the Yoneda development
 of Functor/Hom/Yoneda.v.  Opposition extends to functors (F^op, in
 Functor/Opposite.v) and to natural transformations, where the direction
 reverses: a transformation between F^op and G^op corresponds to one
 from G to F (Natural/Transformation/Opposite.v).  Up to natural
 isomorphism the identity and op are the only autoequivalences of Cat
 (nLab): arrow reversal is the one nontrivial symmetry the subject has.

 Whether reversing twice is literally the identity is a genuine design
 fork among proof assistants.  agda-unimath states that its opposite
 construction is a definitional involution, proved by refl; Agda's 1Lab
 swaps its identity laws just as this file does, but keeps a single
 associativity field, reversed by a path inversion, and — with eta
 disabled on its precategory record — exhibits involutivity as an
 isomorphism of precategories with identity components; agda-categories
 records that its bicategory-level op is only almost a definitional
 involution.  The paired fields of the base records here exist for this
 file's sake: [comp_assoc_sym] carries no content beyond [comp_assoc]
 (Theory/Category.v derives it in [Build_Category']), and
 [naturality_sym] repeats the device for 2-cells
 (Theory/Natural/Transformation.v), so [Opposite] permutes fields
 rather than composing them with symmetry proofs, and the dual
 definitions above unfold to their primal counterparts with no
 rewriting along an isomorphism — Comonad/Core.v reads each comonad law
 as its monad law backwards by exactly this.  At the level of arrows
 the construction costs nothing, since [op] and [unop] move no data.
 The working programmer's C^op is Haskell's Data.Functor.Contravariant,
 whose instances — predicates, comparisons, equivalence relations —
 consume values where covariant functors produce them, and whose
 documentation notes that the dual of a Functor is just a Functor;
 because op squared is the identity, there are likewise no cocomonads
 (Milewski, "Products and Coproducts", 2015). 

 --------
 二元性：原理、历史以及严格性带来的收益

 nLab（二元性）：https://ncatlab.org/nlab/show/duality
 nLab（预层）：https://ncatlab.org/nlab/show/presheaf
 维基百科：https://en.wikipedia.org/wiki/Dual_(category_theory)
 维基百科：https://en.wikipedia.org/wiki/Duality_(projective_geometry)相反范畴是范畴论中的定理加倍装置。由于范畴的公理在反转每一条箭头时保持不变，一个命题在 C 中成立当且仅当它的对偶——交换源和目标，合成按相反顺序读取——在 C^op 中成立，因此对所有范畴证明的定理可以直接得到它的对偶，而无需进一步工作（Mac Lane，《为工作数学家准备的范畴》，Springer 1978，第33页；Awodey，《范畴论》，牛津大学出版社，2010）。nLab 在理论本身的层面上表述了这一点：范畴的初等理论的签名具有非平凡的自反性，因此每个形式定理都有一个形式对偶——这与格的交/并对偶和射影平面的点/线对偶现象相同。这个先例比该主题早了一个世纪。在十九世纪初的射影几何中，创造“对偶”一词的盖尔戈纳（Gergonne）在他的期刊中将对偶定理并排打印，而蓬斯莱特（Poncelet）则认为点/直线互换是极点与极线理论的一个结果：两点确定一条直线，两条直线在一点相交，同一个定理读两次。范畴论随后从其第一页就内部化了这一现象——艾伦伯格（Eilenberg）和麦克莱恩（Mac Lane）从对偶向量空间开始，创造“逆变”来描述反转箭头的函子，并观察到在单次对偶不自然的情况下，双对偶是自然的（Eilenberg 和 Mac Lane，《自然等价的一般理论》，美数学会学报 58, 1945）。麦克莱恩很快就将对偶本身作为研究对象：将基于元素的群论概念完全用同态和复合的术语重新表述，而对偶公理则产生对偶定理（Mac Lane，《Groups, categories and duality》，Proc. Nat. Acad. Sci. 34, 1948；《Duality for groups》，Bull. Amer. Math. Soc. 56, 1950）。通过布赫斯鲍姆和格罗滕迪克的研究，这一计划产生了阿贝尔范畴，其自对偶公理为同调代数提供了一个命题的两个对偶结果（Goswami 和 Janelidze，《Duality in non-abelian algebra IV》，arXiv:1704.01863, 2017）。在这个文件之后的下游，库通过定义而不是类比采用双重概念：comonad 是 C^op 上的 monad（Theory/Monad.v），colimit 是相反图的极限（Structure/Limit.v），初始对象在 C^op 中是终对象（Structure/Initial.v），coproduct 是相反的积（Structure/Cocartesian.v），coend 是对立函子上的 end（Structure/Coend.v），F-余代数应用该构造两次（Construction/FCoalg.v）。每一个一行的定义都继承了其原始概念的完整理论。逆变同样是可表示性的基础：presheaf 是从 U^op 出发的函子（Theory/Sheaf.v），以及 Functor/Hom.v 中的 curry 化 hom [Curried_Hom]，本身是来自 C^op 的函子，供 Functor/Hom/Yoneda.v 的 Yoneda 构建使用。对偶扩展到函子（F^op，在 Functor/Opposite.v 中）以及自然变换，其中方向会反转：F^op 和 G^op 之间的变换对应于从 G 到 F 的变换（Natural/Transformation/Opposite.v）。在自然同构的意义下，Cat 的唯一自等价是恒等与对偶（nLab）：箭头反转是该领域唯一非平凡的对称性。是否两次反转字面上就是恒等是证明助理中的一个真正的设计分歧。agda-unimath 表示它的对立构造是一个定义性的自反，通过 refl 证明；Agda 的 1Lab 像这个文件一样交换它的恒等律，但保持单一的结合性字段，通过路径反转进行反转，并且——在其前范畴记录上禁用 eta 的情况下——将自反性表现为具有恒等分量的前范畴的同构；agda-categories 记录其二范畴级别的对立操作仅几乎是一个定义性的自反。这里基本记录的成对字段存在是为了这个文件的缘故：[comp_assoc_sym] 除了 [comp_assoc] 外不携带任何内容（Theory/Category.v 在 [Build_Category'] 中派生它），而 [naturality_sym] 在 2-Cells（Theory/Natural/Transformation.v）中重复了该装置，因此 [Opposite] 对字段进行置换，而不是通过对称性证明来组合它们，上述对偶定义展开为其原始对应项时不沿同构进行重写——Comonad/Core.v 将每条 comonad 法则完全作为其 monad 法则的逆向读取。在箭头层面，该构造不花费任何开销，因为 [op] 和 [unop] 不移动任何数据。工作的程序员的 C^op 是 Haskell 的 Data.Functor.Contravariant，其实例——谓词、比较、等价关系——消耗值，而协变函子产生值，并且其文档指出，函子的对偶只是一个函子；因为 op 的平方是恒等映射，因此同样不存在余可扩范畴（Milewski, “Products and Coproducts”, 2015）。
*)

Definition Opposite `(C : Category) : Category := {|
  obj     := @obj C;
  hom     := fun x y => @hom C y x;
  homset  := fun x y => @homset C y x;
  id      := @id C;
  compose := fun _ _ _ f g => g ∘ f;

  compose_respects := fun x y z f g fg h i hi =>
    @compose_respects C z y x h i hi f g fg;

  id_left  := fun x y f => @id_right C y x f;
  id_right := fun x y f => @id_left C y x f;

  comp_assoc := fun x y z w f g h => @comp_assoc_sym C w z y x h g f;
  comp_assoc_sym := fun x y z w f g h => @comp_assoc C w z y x h g f
|}.

Notation "C ^op" := (@Opposite C)
  (at level 7, format "C ^op", left associativity) : category_scope.

Lemma op_invol {C : Category} : (C^op)^op = C.
Proof.
  unfold Opposite; simpl.
  destruct C; simpl.
  f_equal.
Qed.

(*
 [op] and [unop] re-read a C-morphism as a C^op-morphism and back. Since the
 hom-sets are definitionally equal, both are the identity on the underlying
 arrow; they only flip how its direction is named. 

 --------
 [op] 和 [unop] 将 C-态射重新解读为 C^op-态射再转换回原状。由于同态集在定义上是相等的，它们对底层箭头都是恒等的；它们只是颠倒了箭头方向的命名方式。
*)

Definition op   {C : Category} {x y} (f : y ~{C}~> x) : x ~{C^op}~> y := f.
Definition unop {C : Category} {x y} (f : x ~{C^op}~> y) : y ~{C}~> x := f.

(*
 If two objects are isomorphic in C, then they are also isomorphic in C^op,
 just the conversion arrows are flipped. 

 --------
 如果在范畴 C 中两个对象是同构的，那么它们在 C^op 中也是同构的，只是对应的箭头被翻转了。
*)

Require Import Category.Theory.Isomorphism.

#[export]
Program Instance Isomorphism_Opposite {C : Category} {x y : C}
       (iso : @Isomorphism C x y) :
  @Isomorphism (C^op) x y := {
  to := from iso;
  from := to iso;
  iso_to_from := iso_to_from iso;
  iso_from_to := iso_from_to iso
}.
