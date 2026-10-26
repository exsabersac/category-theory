Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/coproduct
 Wikipedia: https://en.wikipedia.org/wiki/Coproduct

 A cocartesian category has all finite coproducts. For objects x and y the
 coproduct `x + y` comes with injections `inl : x ~> x + y` and
 `inr : y ~> x + y`, and the universal mapping property states that for any
 object w with `f : y ~> x` and `g : z ~> x` there is a unique copairing
 `f ▽ g : y + z ~> x` (the `merge`, written [f, g] in the literature)
 satisfying `f ▽ g ∘ inl ≈ f` (inl_merge) and `f ▽ g ∘ inr ≈ g` (inr_merge);
 uniqueness is recorded by [merge_inv] together with [merge_inl_inr]
 (`inl ▽ inr ≈ id`). This is exactly the dual of the cartesian product: a
 coproduct in C is a product in C^op, with all arrows reversed. 

 --------
 nLab: https://ncatlab.org/nlab/show/coproduct 
 Wikipedia: https://en.wikipedia.org/wiki/Coproduct 

 一个共笛卡尔范畴具有所有有限的余积。对于对象 x 和 y，它们的余积 `x + y` 配有注入映射 `inl : x ~> x + y` 和 `inr : y ~> x + y`，且其泛映射性质表明，对于任何对象 w，如果存在 `f : y ~> x` 和 `g : z ~> x`，则存在唯一的共配对 `f ▽ g : y + z ~> x`（ZW11WZZ，在文献中记作 [f, g]），满足 `f ▽ g ∘ inl ≈ f`（inl_merge）和 `f ▽ g ∘ inr ≈ g`（inr_merge）；唯一性通过 [merge_inv] 以及 [merge_inl_inr]（`inl ▽ inr ≈ id`）来记录。这恰好是笛卡尔积的对偶：在 C 中的余积是 C^op 中的积，所有箭头方向相反。
*)

(*
 To be cocartesian is just to be cartesian in the opposite category; but to
 avoid confusion, we'd like a set of notations specific to categories with
 cocartesian structure. As a consequence the coproduct UMP is not restated
 as a class field here: it is inherited from Cartesian's [ump_products]
 read in C^op, and surfaces below as the dualized equations [inl_merge],
 [inr_merge] and uniqueness [merge_inv] / [merge_inl_inr]. 

 --------
 成为余笛卡尔只是指在对偶范畴中成为笛卡尔；但为了避免混淆，我们希望有一套专门针对具有余笛卡尔结构的范畴的记号。因此，余积的 UMP 在这里不会作为类字段重新陈述：它是从笛卡尔的 [ump_products] 中继承的，在 C^op 中读取，并在下面以对偶化的方程 [inl_merge]、[inr_merge] 以及唯一性 [merge_inv] / [merge_inl_inr] 表现出来。
*)

(*
 Where coproducts come from, and what they are for

 nLab:  https://ncatlab.org/nlab/show/coproduct
 Paper: Mac Lane, “Duality for groups”, Bulletin of the American
 Mathematical Society 56(6), 1950
 Paper: Cockett, “Introduction to distributive categories”, Mathematical
 Structures in Computer Science 3(3), 1993

 The coproduct entered category theory simultaneously with the product,
 each defined as the mirror image of the other.  In “Duality for groups”
 (an address delivered before the American Mathematical Society in
 November 1948, published 1950), Mac Lane characterizes the direct
 product of groups by its universal diagram, observes that the property
 “may serve as a definition” because it determines the object up to
 isomorphism, and then characterizes the free product by the same diagram
 with every arrow reversed, noting explicitly that the two diagrams are
 dual.  The paper, which the Stanford Encyclopedia of Philosophy credits
 with “using arrows to define certain fundamental concepts” (Marquis,
 “Category Theory”, SEP), thus contains this file in embryo, five years
 after categories themselves appeared in Eilenberg and Mac Lane 1945.

 Mac Lane also flags, in the same section, the asymmetry that shapes this
 library: the proof that the direct product exists is not dual to the
 proof that the free product exists, since both arguments handle the
 elements of the groups concerned.  Universal properties transfer across
 duality at no cost; constructions do not.  The notation this file
 introduces is the formal expression of the first half — a coproduct in C
 being a product in C^op, nearly every lemma below is discharged by a
 one-line appeal to its original in Structure/Cartesian.v — while the
 second half is why Instance/Sets/Cocartesian.v, Instance/Coq.v and
 Instance/Props.v must each exhibit their coproducts by hand.

 What the universal property packages is case analysis.  A morphism out
 of x + y is exactly a pair of clauses, one per summand, and the
 copairing f ▽ g is the unique morphism restricting to those clauses:
 morphisms out of a coproduct correspond precisely to families of
 morphisms out of its summands (Wikipedia, “Coproduct”).  One definition
 thereby covers constructions with little surface resemblance — disjoint
 union of sets, free product of groups, direct sum of vector spaces,
 wedge sum of pointed spaces, tensor product of commutative algebras,
 join in a poset (Wikipedia, “Coproduct”).  Yet where products of
 concrete structures sit uniformly on the cartesian product of
 underlying sets, coproducts can be, and typically are, dramatically
 different from products in the same category (Wikipedia, “Coproduct”):
 the underlying set of a free product of groups is not a disjoint union,
 and the injections need not even be monomorphisms (nLab, “coproduct”).

 Read computationally, this file is the algebra of sum types.  [inl] and
 [inr] are the constructors, and [merge] is the case split — Haskell's
 either, the “factorizer” of Milewski, “Products and Coproducts”,
 Category Theory for Programmers (2015).  [inl_merge] and [inr_merge] are
 its beta rules, a split applied to a constructor computing the matching
 branch; [merge_inl_inr] is the eta law, as the comment beside it already
 records (nLab, “sum type”; Harper, Practical Foundations for Programming
 Languages, §12); and [merge_inv] is extensionality, two splits agreeing
 exactly when their branches do.  [left], [right] and [cover] map over
 one or both summands, mirroring the first, second and split of
 Structure/Cartesian.v, and [paws] — Cartesian's swap spelled backwards —
 is the symmetry.  Instance/Coq.v realizes the vocabulary literally, the
 copairing being a match on the sum type, and on skeletal FinSet the
 coproduct structure computes on closed values by eq_refl
 (Instance/FinSet.v).

 The satellites extend the structure in three directions.  With the
 initial object of Structure/Initial.v as unit, the isomorphisms
 [coprod_assoc], [coprod_comm], [coprod_zero_l] and [coprod_zero_r] below
 are the components of a symmetric monoidal structure on (C, +, 0)
 (Wikipedia, “Coproduct”).  Structure/Bicartesian.v combines coproducts
 with products, whereupon Structure/Distributive.v asks that the
 canonical morphism x × y + x × z ~> x × (y + z) be invertible; in any
 distributive category the object 1 + 1 is a boolean algebra, and maps
 into it provide a boolean logic (Cockett 1993), while the companion
 notion of extensivity is disentangled from distributivity by Carboni,
 Lack and Walters, “Introduction to extensive and distributive
 categories”, JPAA 84, 1993.  Structure/BiCCC.v shows no such axiom is
 needed in a bicartesian closed category, where closedness makes the
 product functor a left adjoint and hence colimit-preserving, and a
 bicartesian closed category provides the semantics and proof theory of
 intuitionistic propositional logic (nLab, “bicartesian closed
 category”).  When coproduct and product coincide as biproducts,
 Structure/Semiadditive.v derives a commutative monoid on every
 hom-setoid.  Coproduct-preserving functors are obtained by the same
 duality device as this file, as [CocartesianFunctor] in
 Functor/Structure/Cartesian.v. 

 --------
 余积的来源及其用途

 nLab: https://ncatlab.org/nlab/show/coproduct
 论文: Mac Lane, 《群的对偶性》，美国数学学会公报 56(6), 1950
 论文: Cockett, 《分配范畴导论》，计算机科学中的数学结构 3(3), 1993余积与积同时进入了范畴论，两者彼此定义为对方的镜像。在《群的对偶性》（1948年11月在美国数学学会发表的讲演，1950年出版）中，Mac Lane 通过其普适图来刻画群的直积，指出这一性质“可以作为定义”，因为它决定了对象的同构类型，然后通过将每一条箭头反转的相同图来刻画自由积，并明确指出这两个图是对偶的。这篇论文，被《斯坦福哲学百科全书》认为“使用箭头来定义某些基本概念”（Marquis，“范畴论”，SEP），因此在范畴本身于1945年出现在Eilenberg和Mac Lane之后的五年里，就包含了这个文件的雏形。麦克·莱恩在同一节中还指出，这个库的结构具有不对称性：直积存在性的证明并不是自由积存在性证明的对偶，因为两种论证都处理了相关群的元素。泛性质可以无代价地跨对偶传播；而构造则不行。本文件引入的符号是前半部分的形式表达——在 C 中的余积在 C^op 中就是积，下面几乎每个引理都通过在 Structure/Cartesian.v 中的一行调用其原始版本而解决——而后半部分则说明了为什么 Instance/Sets/Cocartesian.v、Instance/Coq.v 和 Instance/Props.v 必须手工展示它们的余积。泛性质所打包的是情况分析。一个从 x + y 出发的态射恰好是一对子句，每个加数一个，而余配 f ▽ g 是唯一一个限制于那些子句的态射：余积的态射恰好对应于其加数的态射族（维基百科，“余积”）。因此，一个定义涵盖了表面上几乎没有相似之处的构造——集合的离散并、群的自由积、向量空间的直和、指点空间的楔和、交换代数的张量积、偏序集中的连接（维基百科，“余积”）。然而，当具体结构的乘积在底层集合的笛卡尔积上均匀地排列时，余积可以且通常确实与同一范畴中的积有显著不同（维基百科，“余积”）：群的自由积的底层集合并不是一个不相交的并集，而且这些嵌入甚至不必是单射（nLab，“余积”）。从计算角度来看，这个文件是和类型的代数。[inl] 和 [inr] 是构造子，而 [merge] 是案例拆分——Haskell 的 either，Milewski 的“因式分解器”，“积与余积”，《程序员的范畴论》（2015）。[inl_merge] 和 [inr_merge] 是它的 beta 规则，将拆分应用于构造子以计算匹配的分支；[merge_inl_inr] 是 eta 定律，正如旁边的注释已经记录的那样（nLab，“和类型”；Harper，《编程语言的实用基础》，§12）；而 [merge_inv] 是外延性，当两个拆分的分支完全相同时，它们才相等。[left]、[right] 和 [cover] 映射单个或两个求和分量，反映了 Structure/Cartesian.v 中的 first、second 和 split，而 [paws]——Cartesian 的 swap 反写——是对称性。Instance/Coq.v 字面上实现了词汇表，copairing 是对和类型的匹配，并且在骨架 FinSet 上，coproduct 结构通过 eq_refl 对封闭值进行计算 (Instance/FinSet.v)。这些卫星在三个方向上扩展结构。以 Structure/Initial.v 的初始对象为单位，下面的同构 [coprod_assoc]、[coprod_comm]、[coprod_zero_l] 和 [coprod_zero_r] 是 (C, +, 0) 上对称单体范畴结构的组成部分（维基百科，“余积”）。Structure/Bicartesian.v 将余积与积结合，而 Structure/Distributive.v 则要求典范态射 x × y + x × z ~> x × (y + z) 可逆；在任何分配范畴中，对象 1 + 1 是布尔代数，并且映射到其上的函数提供布尔逻辑（Cockett 1993），而伴随的扩展性概念被 Carboni、Lack 和 Walters 在“Introduction to extensive and distributive categories”，JPAA 84，1993 中与分配性区分开来。Structure/BiCCC.v 显示在双笛卡尔闭范畴中不需要这样的公理，其中闭性使得积函子成为左伴随，因此保持余极限，而双笛卡尔闭范畴提供了直觉主义命题逻辑的语义和证明理论（nLab，“bicartesian closed category”）。当余积和积作为双积一致时，Structure/Semiadditive.v 在每个同态集合上推导出一个交换幺半群。保持余积的函子通过与此文件相同的对偶装置获得，如 Functor/Structure/Cartesian.v 中的 [CocartesianFunctor]。
*)

(*
   【Cocartesian 记号与字段展开】/ Notation & field walkthrough

   1) 这是什么 / What this is
      Cocartesian C := Cartesian (C^op) —— 有限余积 = 对偶范畴里的积；不重写 UMP 字段。
      Finite coproducts = products in C^op; UMP inherited, not restated.
      Haskell：Either / (+)；inl/inr 构造子，merge = either / case 拆分。
      Haskell: Either; inl/inr constructors; merge ≈ either.

   2) 本节给出的共变读法 / Covariant API in this Section
      - Coprod / + —— 余积对象 / coproduct object
      - merge / ▽ —— 余配对 [f,g] / copairing
      - inl, inr —— 左右内射 / injections
      - left/right/cover/paws —— 映射分量与交换

   3) 定律（对偶自 Cartesian）/ Laws (dual of product laws)
      inl_merge / inr_merge / merge_inl_inr / merge_inv

   阅读：Cartesian → 本 Notation → merge/inl/inr → β/η 律。
   Read: Cartesian → this Notation → merge/inl/inr → β/η laws.
*)

Notation "'Cocartesian' C" := (@Cartesian (C^op))
  (at level 9) : category_theory_scope.
Notation "@Cocartesian C" := (@Cartesian (C^op))
  (at level 9) : category_theory_scope.

Section Cocartesian_.

Context `{O : @Cocartesian C}.

(* The coproduct object x + y is the product object read in C^op. / 余积对象 x + y 是在 C^op 中读取的积对象。 *)
Definition Coprod : C → C → C := @product_obj _ O.

Infix "+" := Coprod (at level 50, left associativity) : object_scope.

(*
 The copairing [f, g] : y + z ~> x is the fork of C^op; it is the unique
 morphism out of the coproduct furnished by the UMP. 

 --------
 余对偶 [f, g] : y + z ~> x 是 C^op 的叉；它是由 UMP 提供的余积所唯一出的态射。
*)
Definition merge {x y z : C} (f : y ~> x) (g : z ~> x) : y + z ~{C}~> x :=
  @fork _ O _ _ _ f g.

Infix "▽" := merge (at level 26) : morphism_scope.

#[export] Program Instance merge_respects {x y z} :
  Proper (equiv ==> equiv ==> equiv) (@merge x y z).
Next Obligation. apply (@fork_respects _ O). Qed.

(* The coproduct injections are the product projections exl/exr of C^op, whose arrows are reversed: inl : x ~> x + y and inr : y ~> x + y. / 余积注入是 C^op 的积投影 exl/exr，其箭头是反向的：inl : x ~> x + y 和 inr : y ~> x + y。 *)
Definition inl {x y : C} : x ~{C}~> x + y := @exl _ O _ _.
Definition inr {x y : C} : y ~{C}~> x + y := @exr _ O _ _.

Definition left  {x y z : C} (f : x ~> y) : x + z ~{C}~> y + z :=
  (inl ∘ f) ▽ inr.

Definition right  {x y z : C} (f : x ~> y) : z + x ~{C}~> z + y :=
  inl ▽ (inr ∘ f).

Definition cover  {x y z w : C} (f : x ~> y) (g : z ~> w) :
  x + z ~{C}~> y + w :=
  (inl ∘ f) ▽ (inr ∘ g).

#[export] Program Instance left_respects {a b c : C} :
  Proper (equiv ==> equiv) (@left a b c).
Next Obligation. apply (@first_respects _ O). Qed.

#[export] Program Instance right_respects {a b c : C} :
  Proper (equiv ==> equiv) (@right a b c).
Next Obligation. apply (@second_respects _ O). Qed.

#[export] Program Instance cover_respects {a b c d : C} :
  Proper (equiv ==> equiv ==> equiv) (@cover a b c d).
Next Obligation.
  proper.
  unfold cover.
  rewrites.
  reflexivity.
Qed.

Definition paws {x y : C} : x + y ~{C}~> y + x := @swap _ O _ _.

(* UMP, first computation rule: the copairing recovers f along inl. / UMP，第一个计算规则：copairing 在 inl 上恢复 f。 *)
Lemma inl_merge {x z w : C} (f : z ~> x) (g : w ~> x) :
  f ▽ g ∘ inl ≈ f.
Proof. apply (@exl_fork _ O). Qed.

#[local] Hint Rewrite @inl_merge : categories.

(* UMP, second computation rule: the copairing recovers g along inr. / UMP，第二条计算规则：共配对沿着 inr 恢复 g。 *)
Lemma inr_merge {x z w : C} (f : z ~> x) (g : w ~> x) :
  f ▽ g ∘ inr ≈ g.
Proof. apply (@exr_fork _ O). Qed.

#[local] Hint Rewrite @inr_merge : categories.

(* The copairing of the injections is the identity: the eta law for +. / 注射的共配对是恒等映射：+ 的 η 律。 *)
Corollary merge_inl_inr {x y : C} :
  inl ▽ inr ≈ @id C (x + y).
Proof. apply (@fork_exl_exr _ O). Qed.

#[local] Hint Rewrite @merge_inl_inr : categories.

(* UMP uniqueness: two copairings agree iff their components agree. / UMP 唯一性：两个共配对当且仅当它们的分量相同时才相等。 *)
Corollary merge_inv {x y z : C} (f h : y ~> x) (g i : z ~> x) :
  f ▽ g ≈ h ▽ i ↔ (f ≈ h) * (g ≈ i).
Proof. apply (@fork_inv _ O). Qed.

Corollary merge_comp {x y z w : C} (f : y ~> z) (h : w ~> z) (g : z ~> x) :
  (g ∘ f) ▽ (g ∘ h) ≈ g ∘ f ▽ h.
Proof. apply (@fork_comp _ O). Qed.

Ltac unmerge :=
  unfold paws, cover, left, right; simpl;
  repeat (rewrite <- !merge_comp; cat;
          rewrite <- !comp_assoc; cat).

#[local] Obligation Tactic := cat_simpl; unmerge.

Theorem left_id {x y : C} :
  left (id[x]) ≈ id[x + y].
Proof. unfold left; cat. Qed.

#[local] Hint Rewrite @left_id : categories.

Theorem left_comp {x y z w : C} (f : y ~> z) (g : x ~> y) :
  left (z:=w) (f ∘ g) ≈ left f ∘ left g.
Proof. apply (@first_comp _ O). Qed.

Theorem left_fork {x y z w : C} (f : y ~> x) (g : z ~> x) (h : w ~> y) :
  f ▽ g ∘ left h ≈ (f ∘ h) ▽ g.
Proof. apply (@first_fork _ O). Qed.

Theorem right_id {x y : C} :
  right (id[y]) ≈ id[x + y].
Proof. unfold right; cat. Qed.

#[local] Hint Rewrite @right_id : categories.

Theorem right_comp {x y z w : C} (f : y ~> z) (g : x ~> y) :
  right (z:=w) (f ∘ g) ≈ right f ∘ right g.
Proof. apply (@second_comp _ O). Qed.

Theorem right_fork {x y z w : C} (f : y ~> x) (g : z ~> x) (h : w ~> z) :
  f ▽ g ∘ right h ≈ f ▽ (g ∘ h).
Proof. apply (@second_fork _ O). Qed.

Corollary inl_left {x y z : C} (f : x ~> y) :
  left f ∘ @inl x z ≈ inl ∘ f.
Proof. apply (@exl_first _ O). Qed.

#[local] Hint Rewrite @inl_left : categories.

Corollary inr_left {x y z : C} (f : x ~> y) :
  left f ∘ @inr x z ≈ inr.
Proof. apply (@exr_first _ O). Qed.

#[local] Hint Rewrite @inr_left : categories.

Corollary inl_right {x y z : C} (f : x ~> y) :
  right f ∘ @inl z x ≈ inl.
Proof. apply (@exl_second _ O). Qed.

#[local] Hint Rewrite @inl_right : categories.

Corollary inr_right {x y z : C} (f : x ~> y) :
  right f ∘ @inr z x ≈ inr ∘ f.
Proof. apply (@exr_second _ O). Qed.

#[local] Hint Rewrite @inr_right : categories.

Theorem paws_left {x y z : C} (f : x ~> y) :
  paws ∘ left (z:=z) f ≈ right f ∘ paws.
Proof. symmetry; apply (@swap_second _ O y x z f). Qed.

Theorem paws_right {x y z : C} (f : x ~> y) :
  paws ∘ right f ≈ left (z:=z) f ∘ paws.
Proof. symmetry; apply (@swap_first _ O y x z f). Qed.

Theorem left_right {x y z w : C} (f : x ~> y) (g : z ~> w) :
  left f ∘ right g ≈ right g ∘ left f.
Proof. symmetry; apply (@first_second _ O). Qed.

Theorem paws_fork {x y z : C} (f : y ~> x) (g : z ~> x) :
  f ▽ g ∘ paws ≈ g ▽ f.
Proof. apply (@swap_fork _ O). Qed.

Definition paws_invol {x y : C} :
  paws ∘ paws ≈ @id C (x + y).
Proof. unfold paws; apply (@swap_invol _ O). Qed.

#[local] Hint Rewrite @paws_invol : categories.

Theorem cover_id {x y : C} :
  cover (id[x]) (id[y]) ≈ id[x + y].
Proof. now unmerge; cat. Qed.

#[local] Hint Rewrite @cover_id : categories.

Theorem cover_comp {x y z w v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) (i : w ~> v) :
  cover f g ∘ cover h i ≈ cover (f ∘ h) (g ∘ i).
Proof.
  unmerge.
  rewrite !comp_assoc.
  rewrite <- merge_comp.
  unfold cover.
  rewrite !comp_assoc.
  rewrite inl_merge.
  rewrite inr_merge.
  reflexivity.
Qed.

Theorem cover_left {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  cover f g ∘ left h ≈ cover (f ∘ h) g.
Proof.
  unmerge.
  rewrite <- merge_comp.
  rewrite inr_merge.
  rewrite comp_assoc.
  rewrite inl_merge.
  rewrite comp_assoc.
  reflexivity.
Qed.

Theorem left_cover {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  left f ∘ cover h g ≈ cover (f ∘ h) g.
Proof.
  unmerge.
  rewrite <- merge_comp.
  rewrite !comp_assoc.
  rewrite inl_merge.
  rewrite inr_merge.
  reflexivity.
Qed.

Theorem cover_right {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  cover g f ∘ right h ≈ cover g (f ∘ h).
Proof.
  unmerge.
  rewrite <- merge_comp.
  rewrite !comp_assoc.
  rewrite inl_merge.
  rewrite inr_merge.
  reflexivity.
Qed.

Theorem right_cover {x y z v u : C}
        (f : y ~> z) (h : x ~> y) (g : v ~> u) :
  right f ∘ cover g h ≈ cover g (f ∘ h).
Proof.
  unmerge.
  rewrite <- merge_comp.
  rewrite !comp_assoc.
  rewrite inl_merge.
  rewrite inr_merge.
  reflexivity.
Qed.

Theorem cover_inl {x y z w : C} (f : x ~> y) (g : z ~> w):
  cover f g ∘ inl ≈ inl ∘ f.
Proof. unmerge; cat. Qed.

Theorem cover_inr {x y z w : C} (f : x ~> y) (g : z ~> w):
  cover f g ∘ inr ≈ inr ∘ g.
Proof. unmerge; cat. Qed.

#[export] Program Instance coprod_respects_iso :
  Proper (Isomorphism ==> Isomorphism ==> Isomorphism) Coprod.
Next Obligation.
  proper.
  construct.
  - exact (cover (to X) (to X0)).
  - exact (cover (from X) (from X0)).
  - now rewrite cover_comp, !iso_to_from, cover_id.
  - now rewrite cover_comp, !iso_from_to, cover_id.
Defined.

Context `{I : @Initial C}.

#[export] Program Instance coprod_zero_l {x : C} :
  0 + x ≅ x := {
  to   := zero ▽ id;
  from := inr
}.
Next Obligation. apply (@prod_one_l _ _ I). Qed.

#[local] Hint Rewrite @coprod_zero_l : isos.

#[export] Program Instance coprod_zero_r {x : C} :
  x + 0 ≅ x := {
  to   := id ▽ zero;
  from := inl
}.
Next Obligation. apply (@prod_one_r _ _ I). Qed.

#[local] Hint Rewrite @coprod_zero_r : isos.

#[export] Program Instance coprod_comm  {x y : C} :
  x + y ≅ y + x := {
  to   := paws;
  from := paws
}.

#[export] Program Instance coprod_assoc  {x y z : C} :
  (x + y) + z ≅ x + (y + z) := {
  to   := (inl ▽ (inr ∘ inl)) ▽ (inr ∘ inr);
  from := (inl ∘ inl) ▽ ((inl ∘ inr) ▽ inr)
}.
Next Obligation. apply (@prod_assoc _ O). Qed.
Next Obligation. apply (@prod_assoc _ O). Qed.

End Cocartesian_.

Infix "+" := Coprod (at level 50, left associativity) : object_scope.
Infix "▽" := merge (at level 26) : morphism_scope.

#[export] Hint Rewrite @inl_merge : categories.
#[export] Hint Rewrite @inr_merge : categories.
#[export] Hint Rewrite @merge_inl_inr : categories.
#[export] Hint Rewrite @coprod_zero_r : isos.
#[export] Hint Rewrite @coprod_zero_l : isos.

Ltac unmerge :=
  unfold paws, cover, left, right; simpl;
  repeat (rewrite <- !merge_comp; cat;
          rewrite <- !comp_assoc; cat).
