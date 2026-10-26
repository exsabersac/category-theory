Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** The slice (over) category C/c and coslice (under) category c/C. / 范畴 C/c 的上切片和 c/C 的下切片。 *)

(*
 nLab: https://ncatlab.org/nlab/show/over+category
 nLab: https://ncatlab.org/nlab/show/under+category
 Wikipedia: https://en.wikipedia.org/wiki/Comma_category

 Fix a category C and an object c : C. The slice category C/c has as objects
 the morphisms a ~> c into c (encoded as the dependent pair (∃ a : C, a ~> c),
 so `1 x is the domain a and `2 x is the structure morphism a ~> c). A
 morphism from x = (a, g : a ~> c) to y = (a', g' : a' ~> c) is a morphism
 f : a ~> a' in C making the triangle commute, `2 y ∘ f ≈ `2 x, i.e.
 g' ∘ f ≈ g:

 a  --f-->  a'
 \         /
 g \       / g'      commute, i.e.  g' ∘ f ≈ g.
 v     v
 c

 Identity is id (g ∘ id ≈ g) and composition is composition in C (the
 triangle for f ∘ f' follows by associativity); two slice morphisms are
 equivalent when their underlying C-morphisms are ≈, the triangle proof being
 irrelevant. Dually, the coslice c/C has objects the morphisms c ~> a out of
 c and morphisms f : a ~> a' with `2 y ≈ f ∘ `2 x, i.e. ι' ≈ f ∘ ι.

 Both are special cases of the comma category (Construction/Comma.v). Taking
 the constant functor =(c) := Δ(c) : 1 ⟶ C selecting c, the slice is the
 comma (Id[C] ↓ =(c)) and the coslice is (=(c) ↓ Id[C]); these isomorphisms
 are proven below as Comma_Slice and Comma_Coslice. The forgetful functor
 C/c ⟶ C sending (a, g) to a is the comma projection comma_proj1 transported
 across Comma_Slice; the post-composition functor C/a ⟶ C/b induced by a
 morphism a ~> b (making C/(-) functorial) lives in Construction/Slice/
 Pullback.v as Bang_Functor. 

 --------
 nLab：https://ncatlab.org/nlab/show/over+category
 nLab：https://ncatlab.org/nlab/show/under+category
 维基百科：https://en.wikipedia.org/wiki/Comma_category

 固定一个范畴 C 和一个对象 c : C。切片范畴 C/c 的对象是指向 c 的态射 a ~> c（编码为依赖对 (∃ a : C, a ~> c)，所以 `1 x is the domain a and ` 中的 x 是结构态射 a ~> c）。从 x = (a, g : a ~> c) 到 y = (a', g' : a' ~> c) 的态射是在 C 中的态射 f : a ~> a'，使得三角形交换，即 `2 y ∘ f ≈ ` 中的 x，换句话说 g' ∘ f ≈ g：

 a  --f-->  a'
 \        /
 g \      / g'  交换，即 g' ∘ f ≈ g。
 v    v
 c恒等是 id（g ∘ id ≈ g），而在 C 中的复合就是复合（f ∘ f' 的三角形由结合律得到）；当两个切片态射的底层 C 态射是 ≈ 时，它们是等价的，三角形证明无关紧要。对偶地，余切片 c/C 的对象是从 c 出发到 a 的态射 c ~> a，态射是 f: a ~> a' 并且 `2 y ≈ f ∘ ` 2 x，即 ι' ≈ f ∘ ι。两者都是逗号范畴（Construction/Comma.v）的特殊情况。取常量函子 =(c) := Δ(c) : 1 ⟶ C 选择 c，则切片是逗号 (Id [C] ↓ =(c))，共切片是 (=(c) ↓ Id [C])；这些同构在下文中作为 Comma_Slice 和 Comma_Coslice 得到证明。忘却函子 C/c ⟶ C 将 (a, g) 发送到 a，是跨 Comma_Slice 传递的逗号投影 comma_proj1；由态射 a ~> b 诱导的后合成函子 C/a ⟶ C/b（使得 C/(-) 成为函子）位于 Construction/Slice/Pullback.v 中，记作 Bang_Functor。
*)

(*
 The relative point of view

 nLab: https://ncatlab.org/nlab/show/locally+cartesian+closed+category
 nLab: https://ncatlab.org/nlab/show/codomain+fibration
 nLab: https://ncatlab.org/nlab/show/fundamental+theorem+of+topos+theory
 nLab: https://ncatlab.org/nlab/show/coreader+comonad
 Wikipedia:
 https://en.wikipedia.org/wiki/Grothendieck%27s_relative_point_of_view

 The slice category is the formal home of the relative point of view:
 it makes “an object over a base” a first-class object, turning
 morphisms into c into objects and commuting triangles into morphisms.
 Comma categories, and with them the slice as their leading special
 case, enter the literature in Lawvere's doctoral dissertation
 (Lawvere, “Functorial Semantics of Algebraic Theories”, Columbia
 1963); Wikipedia records that the technique “did not become generally
 known until many years later”, and that the name — after the comma in
 Lawvere's original notation — displeased even its author.  Yet the
 viewpoint is older.  Grothendieck's relative point of view, dating
 from the Grothendieck–Riemann–Roch period around 1956, replaces the
 study of a single object X by the study of a morphism f : X ~> S
 over a base S: a property of the map becomes a property of an object
 of C/S, a whole family is handled as one thing, and since C/1 is
 isomorphic to C, a theorem proved over an arbitrary base specializes
 to the absolute theorem over the terminal object (nLab, “over
 category”).

 The construction is a dictionary of familiar mathematics.  In Set, an
 object of Set/I is the same data as an I-indexed family of sets: a
 map p : F ~> I carries its fibres, and a family reassembles as the
 disjoint union with its projection — an equivalence Set/I ≃ Set^I
 (Leinster, “Higher Operads, Higher Categories”, CUP 2004; nLab,
 “family of sets”).  A bundle over a base B in any category is simply
 an object equipped with a morphism to B, so bundles over B form the
 slice C/B (nLab, “bundle”), and covering spaces of X form a full
 subcategory of Top/X.  For a poset P, the slice P/p is the principal
 down-set of p (nLab, “over category”).  The dual [Coslice] captures
 pointed structures: pointed sets are the coslice of Set under the
 one-point set (Wikipedia, “Comma category”).

 The slice is the fibre-level piece of a larger apparatus.  A morphism
 f : a ~> b induces the post-composition functor Σ_f : C/a ⟶ C/b —
 here [Bang_Functor] in Construction/Slice/Pullback.v — and, when C
 has pullbacks, the base change functor f^* in the other direction
 ([Star_Functor], same file), with the adjunction Σ_f ⊣ f^* PROVED
 there as [Base_Functor_Adjunction] (nLab, “dependent sum”).  When
 every f^* has a further right adjoint Π_f, C is locally cartesian
 closed.  The triple
 Σ_f ⊣ f^* ⊣ Π_f descends from Lawvere's identification of the
 quantifiers as adjoints to substitution (Lawvere, “Adjointness in
 Foundations”, Dialectica 1969), and it interprets dependent type
 theory: slice objects are dependent types over their base, base
 change is substitution, and Σ and Π are the dependent sum and product
 (Seely, “Locally cartesian closed categories and type theory”, Math.
 Proc. Camb. Phil. Soc. 1984).  Assembling every slice at once yields
 the self-indexing C/(-), whose Grothendieck construction is the
 codomain functor on the arrow category — always an opfibration, and a
 fibration precisely when C has pullbacks, the cartesian lifts being
 the pullback squares (nLab, “codomain fibration”).  In-tree,
 Construction/Displayed/Codomain.v presents that fibration
 displayed-style: its fibre over x uses literally this file's object
 encoding, and [codomain_cleaving] / [codomain_cleaving_pullbacks]
 exchange cartesian lifts for pullbacks.

 Two further readings mark where the theory continues.  The
 fundamental theorem of topos theory states that every slice of a
 topos is again a topos; the construction appears as the “topos
 induit” of SGA4 (Artin, Grothendieck, Verdier, SGA4 1972, exposés
 III.5 and IV.5), while the name is due to McLarty (McLarty,
 “Elementary Categories, Elementary Toposes”, OUP 1992).  Relative to
 Structure/Topos.v's [ElementaryTopos], it remains the headline
 theorem about this construction not yet formalized here.  And
 comonadically, a coalgebra of the environment comonad e × − is the
 same thing as a single morphism into e, so the category of its
 coalgebras is isomorphic to the slice over e (nLab, “coreader
 comonad”); Instance/Coq/Comonad/Env.v and Comonad/Coalgebra.v supply
 the comonad and its coalgebra categories, the identification with
 [Slice] being a natural corollary still to be stated. 

 --------
 相对视角

 nLab:  https://ncatlab.org/nlab/show/locally+cartesian+closed+category 
 nLab:  https://ncatlab.org/nlab/show/codomain+fibration 
 nLab:  https://ncatlab.org/nlab/show/fundamental+theorem+of+topos+theory 
 nLab:  https://ncatlab.org/nlab/show/coreader+comonad 
 维基百科:
 https://en.wikipedia.org/wiki/Grothendieck%27s_relative_point_of_view切片范畴是相对视角的正式归宿：它使“基上的一个对象”成为一等对象，将态射变为对象，将交换三角形变为态射。逗号范畴，以及以切片范畴为其主要特例的情形，出现在劳维尔的博士论文中（Lawvere，《代数理论的函子语义》，哥伦比亚大学，1963）；维基百科记录到，这一技术“直到多年后才为人所知”，而这个名称——取自劳维尔原始符号中的逗号——甚至让其作者本人也感到不悦。然而，这种观点本身更为古老。格罗滕迪克的相对观点可以追溯到约1956年的格罗滕迪克–黎曼–罗赫时期，它将对单一对象X的研究替换为对一个基空间S上的态射f : X → S的研究：映射的一个性质变成了C/S中一个对象的性质，整个族被作为一个整体处理，并且由于C/1同构于C，在任意基上证明的定理会专门化为终对象上的绝对定理（nLab，“上范畴”） 。这个构造是熟悉数学的字典。在集合论中，Set/I 的一个对象与一个 I 索引的集合族具有相同的数据：映射 p : F ~> I 携带它的纤维，而一个集合族通过与其投影的离散并集重新组合——一个等价关系 Set/I ≃ Set^I（Leinster, “Higher Operads, Higher Categories”, CUP 2004; nLab, “family of sets”）。在任意范畴中，基 B 上的丛只是一个带有指向 B 的态射的对象，因此基 B 上的丛构成了切片 C/B（nLab, “bundle”），而 X 的覆盖空间构成了 Top/X 的一个完全子范畴。对于偏序集 P，切片 P/p 是 p 的主要下集（nLab, “over category”）。对偶 [Coslice] 捕捉了有基结构：有基集合是 Set 在单点集合下的余切片（Wikipedia, “Comma category”）。切片是更大装置的纤维级部分。一个态射 f : a ~> b 会引出后组合函子 Σ_f : C/a ⟶ C/b — 在 Construction/Slice/Pullback.v 中为 [Bang_Functor] — 当 C 有拉回时，在另一个方向上有基变函子 f^*（[Star_Functor]，相同文件），其中 Σ_f ⊣ f^* 的对偶在该处被证明为 [Base_Functor_Adjunction]（nLab，“依赖和”）。当每个 f^* 有进一步的右伴随 Π_f 时，C 是局部笛卡尔闭的。这个三重算子 Σ_f ⊣ f^* ⊣ Π_f 源自劳韦尔（Lawvere）将量词识别为替换的伴随函子（Lawvere，《Foundations中的Adjointness》，Dialectica 1969），并且它解释了依赖类型理论：slice 对象是其基下的依赖类型，基变换是替换，而 Σ 和 Π 分别是依赖和与积（Seely，《局部笛卡尔闭范畴与类型理论》，Math. Proc. Camb. Phil. Soc. 1984）。一次性组装每个slice会产生自我索引 C/(-)，其Grothendieck构造是箭头范畴上的余伴函子——总是一个上纤维函子，并且当且仅当C有拉回时是纤维函子，笛卡尔提升即是拉回图形（nLab，“codomain fibration”）。在树中，
 Construction/Displayed/Codomain.v 展示了该纤维化
 显示风格：它在 x 上的纤维字面上使用了该文件的对象编码，且 [codomain_cleaving] / [codomain_cleaving_pullbacks]
 用笛卡尔提升交换拉回。另外两篇阅读材料标志着该理论的延续。拓扑理论的基本定理指出，每一个拓扑的切片仍然是一个拓扑；该构造在 SGA4（Artin、Grothendieck、Verdier，SGA4 1972，第三和第四卷的 exposés III.5 和 IV.5）中出现为“topos induit”，而这个名称归功于 McLarty（McLarty，《Elementary Categories, Elementary Toposes》，牛津大学出版社 1992）。相对于 Structure/Topos.v 中的 [ElementaryTopos]，它仍然是关于此构造的主要定理，而该定理尚未在此处形式化。而在余模范畴的意义下，环境余代数 e × − 与一个指向 e 的单一态射是相同的，因此它的余代数范畴同构于 e 上的切片范畴（nLab，“coreader comonad”）；Instance/Coq/Comonad/Env.v 和 Comonad/Coalgebra.v 提供了余模范畴及其余代数范畴，与 [Slice] 的对应关系仍然是一个待陈述的自然推论。
*)

(*
   【Slice / Coslice 定义展开】/ Slice walkthrough
   （口吻对齐 Theory/Category.v；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      固定 c : C。切片 C/c（记 C ̸ c）：对象 = 指向 c 的箭头 a ~> c；
      态射 = 使三角形交换的 f（g' ∘ f ≈ g）。
      Objects over c; morphisms = commuting triangles.
      余切片 c/C：对象 = 从 c 出发的箭头；对偶三角形。
      Haskell / 类型论对照：依赖类型「在 c 上的族」；Set/I ≃ I-索引族。
      Type-theory: families over a base; Set/I ≃ I-indexed families.

   2) 编码 / Encoding
      - obj := ∃ a, a ~> c     （`1 = 定义域，`2 = 结构映射）
      - hom := ∃ f, `2 y ∘ f ≈ `2 x
      - ≈ 只比较底层 f（三角形证明无关）

   3) 与逗号 / Via comma
      C/c ≅ (Id ↓ =(c))，c/C ≅ (=(c) ↓ Id)（本文件 Comma_Slice / Comma_Coslice）。
      Direct encoding is handier; comma is the theory link.

   阅读：对象=入 c 的箭 → 交换三角 → ≈ 看底层 → 逗号同构。
   Read: arrows into c → triangles → ≈ on underlying → comma iso.
*)

Program Definition Slice `(C : Category) `(c : C) : Category := {|
  obj     := ∃ a : C, a ~> c;
  hom     := fun x y => ∃ f : (`1 x) ~> (`1 y), `2 y ∘ f ≈ `2 x;
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |} ;
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation. rewrite comp_assoc; rewrites; reflexivity. Defined.

Notation "C  ̸ c" := (@Slice C c) (at level 90) : category_scope.

(*
 Although the encoding of Slice above is more convenient, theoretically it's
 the comma category (Id[C] ↓ Δ(c)). 

 --------
 虽然上面的 Slice 编码更方便，但理论上它是逗号范畴 (Id [C] ↓ Δ(c))。
*)

#[local] Set Transparent Obligations.

#[export]
Program Instance Comma_Slice `(C : Category) `(c : C) :
  C ̸ c ≅[Cat] (Id ↓ =(c)) := {
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
}.
Next Obligation.
  destruct p, p0; simpl.
  exists h.
  rewrites; cat.
Defined.
Next Obligation.
  proper; simpl.
  now destruct H0, H1, p; simpl.
Qed.
Next Obligation.
  now destruct p.
Qed.
Next Obligation.
  now destruct p, p0, p1, p2.
Qed.
Next Obligation.
  constructive; simplify; simpl in *; cat.
  - destruct H, H0; simpl; cat.
  - destruct H, H0; cat.
Qed.
Next Obligation.
  constructive; simplify; simpl in *; cat.
Qed.

Program Definition Coslice `(C : Category) `(c : C) : Category := {|
  obj     := ∃ a : C, c ~> a;
  hom     := fun x y => ∃ f : (`1 x) ~> (`1 y), `2 y ≈ f ∘ `2 x;
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |} ;
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; _)
|}.
Next Obligation. rewrite <- comp_assoc; rewrites; reflexivity. Defined.

Notation "c  ̸co C" := (@Coslice C c) (at level 90) : category_scope.

#[export]
Program Instance Comma_Coslice `(C : Category) `(c : C) :
  c ̸co C ≅[Cat] (=(c) ↓ Id) := {
  to   := {| fobj := _; fmap := _ |};
  from := {| fobj := _; fmap := _ |}
}.
Next Obligation.
  destruct p, p0; simpl.
  exists h.
  rewrites; cat.
Defined.
Next Obligation.
  proper; simpl.
  now destruct x0, x1, p; simpl.
Qed.
Next Obligation.
  now destruct p.
Qed.
Next Obligation.
  now destruct p, p0, p1, p2.
Qed.
Next Obligation.
  constructive; simplify; simpl in *; cat.
  - destruct x0, x1; simpl; cat.
  - destruct x0, x1; simpl; cat.
Qed.
Next Obligation.
  constructive; simplify; simpl in *; cat.
Qed.
