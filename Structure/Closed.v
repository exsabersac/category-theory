Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/closed+category
 nLab: https://ncatlab.org/nlab/show/closed+monoidal+category
 Wikipedia: https://en.wikipedia.org/wiki/Closed_monoidal_category

 This file is an in-progress stub for a "closed category" in the sense of
 Eilenberg and Kelly: a category C equipped with an internal hom bifunctor

 [-, -] : C^op ∏ C ⟶ C,

 a unit object I, a natural isomorphism x ≅ [I, x], an identity element
 I ~> [x, x], and a composition morphism [y, z] ~> [[x, y], [x, z]],
 subject to coherence axioms. Unlike a closed *monoidal* category, a closed
 category need not carry a tensor product; the internal hom is primitive and
 the tensor-hom adjunction Hom(x ⊗ y, z) ≅ Hom(x, [y, z]) is not assumed.

 The [Closed] class capturing this structure is sketched but commented out
 below (see the jww TODO); only the two helper functors [Curry] and [Flip]
 are live. The fully worked closed *monoidal* category, with tensor, an
 evaluation morphism eval[a, b] : (a ⇒ b) ⊗ a ~> b, and the currying
 universal property, lives instead in [Structure.Monoidal.Closed]. 

 --------
 nLab:  https://ncatlab.org/nlab/show/closed+category 
 nLab:  https://ncatlab.org/nlab/show/closed+monoidal+category 
 Wikipedia:  https://en.wikipedia.org/wiki/Closed_monoidal_category 

 这个文件是一个正在进行中的“闭类”存根，按照 Eilenberg 和 Kelly 的定义：一个类别 C 配备了一个内部 Hom 双函子

 [-, -]  : C^op ∏ C ⟶ C,

 一个单位对象 I，一个自然同构 x ≅  [I, x] ，一个单位元素 I ~>  [x, x] ，以及一个组合态射  [y, z]  ~>  [[x, y] ,  [x, z] ],
 遵循相干公理。与闭*幺半*范畴不同，闭类不必携带张量积；内部 Hom 是原始的，并且不假定张量-Hom 的伴随关系 Hom(x ⊗ y, z) ≅ Hom(x,  [y, z] )。捕获此结构的 [Closed] 类在下面已被勾画但被注释掉（参见 jww TODO）；只有两个辅助函子 [Curry] 和 [Flip] 是活动的。完全构建的闭*单体*范畴，带有张量、一个评估态射 eval [a, b] : (a ⇒ b) ⊗ a ~> b，以及柯里化的普遍性质，则存在于 [Structure.Monoidal.Closed] 中。
*)

(*
 Where closed categories come from, and why the hom is primitive

 nLab (La Jolla proceedings):
 https://ncatlab.org/nlab/show/Proceedings+of+the+Conference+on+Categorical+Algebra+-+La+Jolla+1965
 Wikipedia:
 https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence
 Wikipedia: https://en.wikipedia.org/wiki/Currying
 Paper: Eilenberg, Kelly, "Closed Categories", in Proceedings of the
 Conference on Categorical Algebra — La Jolla 1965, Springer 1966,
 421–562
 Paper: Kelly, "Basic Concepts of Enriched Category Theory", LMS Lecture
 Note Series 64, Cambridge University Press 1982

 The definition sketched above opens Eilenberg and Kelly's La Jolla
 paper, a 142-page work that also treated monoidal categories — the
 very name "monoidal category" is, Mac Lane later wrote, due to
 Eilenberg, and it is used there — and introduced strict 2-categories
 under the name "hypercategories".  Their original axioms differ from
 the modern nLab presentation in one respect: rather than asking that
 the map from morphisms x ~> y to global elements I ~> [x, y] be a
 bijection, the paper carried an underlying-set functor sending the
 internal hom strictly to the external hom-set.  Closed categories
 serve as a base for enrichment — the nLab observes that a closed
 structure on V is already an enrichment context in which V is
 self-enriched — a subject given its textbook consolidation in Kelly's
 1982 book; enrichment over a monoidal base is realized in-tree in
 Construction/Enriched.v.

 The point of declining the tensor is that in many categories the hom is
 the obvious datum and the tensor is not.  Abelian groups internalize
 their homs by pointwise addition; so do the algebras of any commutative
 algebraic theory, and strict 2-categories with lax transformations.  In
 each case, the nLab notes, there is a corresponding tensor product,
 "but its construction is much less intuitive, being essentially defined
 by a sort of adjoint functor theorem" — the Gray tensor product and the
 projective tensor product of Banach spaces were originally defined as
 left adjoints to their homs.  The asymmetry is genuine: a closed
 monoidal category yields a closed category by forgetting the tensor,
 yet recovering a monoidal structure demands C-natural representability
 of [a, [b, ─]], stronger than the Set-natural isomorphisms needed in
 the other direction (for symmetric closed categories ordinary
 naturality suffices; Day–LaPlaza, Prop. 2.3, per the nLab).  LaPlaza's
 embedding theorem (1977) nevertheless places every closed category
 fully and faithfully inside a closed monoidal one.

 Lambek carried closed structure into logic in his deductive-systems
 trilogy (Lambek, "Deductive Systems and Categories I–III", Mathematical
 Systems Theory 2 1968; Springer LNM 86 1969; LNM 274 1972), whose third
 part exhibits cartesian closed categories as the equational theory
 shared by intuitionistic propositional proofs and typed combinators —
 the categorical leg of Curry–Howard, "abstracting away from dynamics of
 computation such as beta reduction" (Wikipedia, "Curry–Howard
 correspondence"; book form in Lambek and Scott, "Introduction to Higher
 Order Categorical Logic", Cambridge University Press 1986).
 Theory/Category.v cites that reading as the bridge behind this file and
 Instance/Lambda/: Instance/Lambda.v builds the syntactic cartesian
 closed category of the simply typed lambda calculus, and [Coq_Closed]
 in Instance/Coq.v interprets exponentials as Coq's own arrow types.

 The live content of this file is itself a currying statement one level
 up.  [Curry] transposes a bifunctor C^op ∏ D ⟶ E into a functor-valued
 functor C^op ⟶ [D, E] — the cartesian closure of Cat, used to present
 the partial applications of an internal hom — and [Curry] after [Flip]
 yields the contravariant section; the transposition device itself
 predates category theory (Frege 1893, Schönfinkel 1924; Curry wrote in
 1980 that "Schönfinkel had the idea some 6 years before I did" —
 Wikipedia, "Currying").  The library's operative closed interfaces are
 Structure/Cartesian/Closed.v (exponentials via [exp_iso], with curry,
 uncurry and eval) and Structure/Monoidal/Closed.v ([ClosedMonoidal],
 the tensor-hom adjunction); Functor/Hom/Internal.v derives the internal
 hom bifunctor [InternalHomFunctor] from cartesian closure;
 Structure/Monoidal/StarAutonomous.v declines this file as a base, a
 placeholder carrying no tensor-hom adjunction, and works over its own
 [SymMonClosed]; and Construction/Funny/Closed.v presents the only other
 monoidal biclosed structure on Cat (Foltz, Lair, Kelly, JPAA 17(2),
 1980). 

 --------
 封闭范畴的来源，以及为什么 Hom 是原始的

 nLab（拉霍亚会议论文集）：
 https://ncatlab.org/nlab/show/Proceedings+of+the+Conference+on+Categorical+Algebra+-+La+Jolla+1965
 Wikipedia：
 https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence
 Wikipedia：https://en.wikipedia.org/wiki/Currying
 论文：Eilenberg, Kelly，《Closed Categories》，发表于 1965 年 La Jolla 范畴代数会议论文集，Springer 1966，421–562
 论文：Kelly，《Basic Concepts of Enriched Category Theory》，LMS Lecture Note Series 64，剑桥大学出版社 1982上述定义开篇于 Eilenberg 和 Kelly 的 La Jolla 论文，这是一篇 142 页的作品，也讨论了单范畴——正如 Mac Lane 后来所写，‘单范畴’这个名字正是由于 Eilenberg，其在论文中使用——并在‘超范畴’的名称下引入了严格 2 范畴。他们的原始公理在一个方面与现代 nLab 的表述有所不同：该论文不是要求从态射 x ~> y 到全局元素 I ~> [x, y] 的映射是双射，而是提出了一个底层集合函子，将内部 Hom 严格地映射到外部 Hom 集。封闭范畴作为丰富化的基础——nLab 观察到 V 上的封闭结构已经是一个丰富化的上下文，其中 V 自我丰富化——这是在 Kelly 1982 年的书中对教科书式巩固下的主题；在单体基础上的丰富化在 Construction/Enriched.v 中以树内实现。拒绝张量的关键在于，在许多范畴中，同态（hom）是显而易见的资料，而张量则不是。阿贝尔群通过逐点相加内化它们的同态；任何交换代数理论的代数以及具有松变换的严格2-范畴也是如此。在每种情况下，nLab指出，都有一个相应的张量积，“但它的构造不那么直观，本质上是通过一种伴随函子定理来定义的”——Gray张量积和Banach空间的投影张量积最初就是作为它们同态的左伴随来定义的。这种不对称是真实的：一个闭单体范畴通过忽略张量可以产生一个闭范畴，但要恢复单体结构则需要  [a, [b, ─] ] 的 C-自然可表示性，这比另一方向所需的 Set-自然同构更强（对于对称闭范畴，普通的自然性就足够；Day–LaPlaza，命题 2.3，根据 nLab）。然而，LaPlaza 的嵌入定理（1977）将每个闭范畴完全且忠实地嵌入到一个闭单体范畴中。兰贝克在他的演绎系统三部曲中将闭合结构引入逻辑（Lambek, “Deductive Systems and Categories I–III”, Mathematical Systems Theory 2 1968; Springer LNM 86 1969; LNM 274 1972），其中第三部分展示了笛卡尔闭合范畴，作为直觉主义命题证明与类型组合子的公理理论——柯里-霍华德对应的范畴方面，“抽象掉计算动态，如β归约”（维基百科, “Curry–Howard correspondence”；书籍形式见 Lambek 和 Scott, “Introduction to Higher Order Categorical Logic”, Cambridge University Press 1986）。Theory/Category.v 引用该读物作为本文件背后的桥梁，Instance/Lambda/: Instance/Lambda.v 构建了简单类型 lambda 演算的句法笛卡尔闭类别，而 Instance/Coq.v 中的 [Coq_Closed] 将指数解释为 Coq 自身的箭头类型。该文件的实时内容本身是一个高一级的柯里化语句。[Curry] 将一个双函子 C^op ∏ D ⟶ E 转置为一个函子值函子 C^op ⟶ [D, E] —— Cat 的笛卡尔闭包，用于表示内部函子的部分应用 —— 并且 [Curry] 在 [Flip] 之后产生逆变截面；该转置装置本身早于范畴理论（Frege 1893，Schönfinkel 1924；Curry 在1980年写道“Schönfinkel 比我早大约6年有这个想法” —— 维基百科，“Currying”）。该库的闭合操作接口是
 Structure/Cartesian/Closed.v（通过 [exp_iso] 的指数，有 curry、uncurry 和 eval）和 Structure/Monoidal/Closed.v（[ClosedMonoidal]，张量-同函子伴随）；Functor/Hom/Internal.v 从笛卡尔闭包派生内部同函子双函子 [InternalHomFunctor]；Structure/Monoidal/StarAutonomous.v 拒绝将此文件作为基础，这是一个占位符，不包含张量-同函子伴随，并在它自己的 [SymMonClosed] 上工作；Construction/Funny/Closed.v 展示了 Cat 上唯一的其他单体双闭结构（Foltz、Lair、Kelly，JPAA 17(2), 1980）。
*)

Section Closed.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.

#[local] Set Transparent Obligations.

(*
 [Curry] partially applies a bifunctor in its first argument: it sends a
 functor of two variables F : C^op ∏ D ⟶ E to the functor-valued functor
 x ↦ (y ↦ F (x, y)), of type C^op ⟶ [D, E]. On objects the inner functor
 acts by F (x, -); the outer fmap of f : x ~> y yields the natural
 transformation z ↦ fmap[F] (f, id[z]). This is the section [F x, ─] of a
 bifunctor, and is what makes the [ X , ─ ] / [ ─ , X ] notations below
 denote genuine functors. 

 --------
 [Curry] 部分地应用了一个双函子于其第一个参数：它将一个双变量函子 F : C^op ∏ D ⟶ E 发送到函子值函子 x ↦ (y ↦ F (x, y))，其类型为 C^op ⟶ [D, E]。在对象上，内层函子的作用是 F (x, -)；外层 f : x ~> y 的 fmap 产生自然变换 z ↦ fmap [F] (f, id [z])。这是双函子 [F x, ─] 的截面，并且这使得下面的 [ X , ─ ] / [ ─ , X ] 符号表示真正的函子。
*)
Program Definition Curry (F : C^op ∏ D ⟶ E) : C^op ⟶ [D, E] := {|
  fobj := fun x => {|
    fobj := fun y => F (x, y);
    fmap := fun y z (f : y ~{D}~> z) => fmap[F] (id[x], f)
  |};
  fmap := fun x y (f : x ~{C^op}~> y) => {|
    transform := fun z => fmap[F] (f, id[z])
  |}
|}.
Next Obligation. now proper; simpl_eq; rewrite X. Qed.
Next Obligation. now rewrite <- fmap_comp; simpl; cat. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.
Next Obligation. now proper; rewrite X. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.

(*
 [Flip] swaps the two arguments of a bifunctor, sending
 F : C^op ∏ D ⟶ E to (x, y) ↦ F (y, x) of type D ∏ C^op ⟶ E. Composing
 [Curry] with [Flip] partially applies the *second* argument, giving the
 contravariant section [ ─ , X ]. 

 --------
 [Flip] 交换双函子的两个参数，将
 F : C^op ∏ D ⟶ E 发送为 (x, y) ↦ F (y, x)，类型为 D ∏ C^op ⟶ E。将
 [Curry] 与 [Flip] 组合会部分应用*第二个*参数，得到
 逆变截面 [ ─ , X ]。
*)
Program Definition Flip (F : C^op ∏ D ⟶ E) : D ∏ C^op ⟶ E := {|
  fobj := fun x => F (snd x, fst x);
  fmap := fun _ _ f => fmap[F] (snd f, fst f)
|}.
Next Obligation. now proper; simpl_eq; simpl in *; rewrite X, H. Qed.
Next Obligation. now rewrite <- fmap_comp. Qed.

Reserved Notation "[ X , Y ]"
  (at level 90, right associativity, format "[ X ,  Y ]").

(*
 jww (2018-10-05): TODO

 The class below sketches the Eilenberg-Kelly data: the internal hom
 bifunctor, the unit object I (= unit_object), the unit isomorphism
 i : x ≅ [I, x] (hom_id_iso), the identity element j : I ~> [x, x]
 (hom_id), and the composition morphism L : [y, z] ~> [[x, y], [x, z]]
 (hom_compose). The two coherence fields are still incomplete: hom_id_right
 and the unnamed hom_ field both contain underscores standing for morphisms
 that have not yet been pinned down, so the class does not yet typecheck.
 Completing it means stating the five Eilenberg-Kelly axioms relating i, j
 and L; until then the whole block is left commented out.

 Class Closed := {
 internal_hom_functor : C^op ∏ C ⟶ C       ( * [-, -] internal hom * )
 where "[ X , Y ]" := (@internal_hom_functor (X, Y));
 unit_object : C;                          ( * the unit object I * )

 ( * hom_id_iso  : Id[C] ≅[Fun] Curry internal_hom_functor unit_object; * )
 hom_id_iso {x} : x ≅ [unit_object, x];    ( * unit iso i : x ≅ [I, x] * )

 hom_id {x} : unit_object ~> [x, x];                 ( * identity j : I ~> [x, x] * )
 hom_compose {x y z} : [y, z] ~> [[x, y], [x, z]];   ( * composition L * )

 hom_id_right {x y} :
 @hom_compose x y y ∘ hom_id << unit_object ~~> [[x, y], [x, y]] >> hom_id;

 hom_ {x y} :
 _ ∘ @hom_compose x x y
 << [x, y] ~~> [unit_object, [x, y]] >>
 to (hom_id_iso ([x, y]))
 }.

 Notation "[ X , Y ]" := (internal_hom_functor (X, Y))
 (at level 90, right associativity, format "[ X ,  Y ]") : object_scope.

 Notation "[ X , ─ ]" := (Curry internal_hom_functor X)
 (at level 90, right associativity, format "[ X ,  ─ ]") : object_scope.

 Notation "[ ─ , X ]" := (Curry (Flip internal_hom_functor) X)
 (at level 90, right associativity, format "[ ─ ,  X ]") : object_scope.

 --------
 jww (2018-10-05): 待办事项

 下面的类勾画了Eilenberg-Kelly的数据：内部Hom双函子、单位对象I (= unit_object)、单位同构i : x ≅ [I, x] (hom_id_iso)、幺元元素j : I ~> [x, x] (hom_id)以及复合态射L : [y, z] ~> [[x, y], [x, z] (hom_compose)。两个相容性字段仍未完成：hom_id_right和未命名的hom_字段中都包含下划线，用于表示尚未确定的态射，因此该类尚不能进行类型检查。完成它意味着要陈述涉及i、j和L的五个Eilenberg-Kelly公理；在此之前，整个代码块保持注释状态。闭类 := {
 内部同态函子 : C^op ∏ C ⟶ C       ( *  [-, -]  内部同态 * )
 其中 "[ X , Y ]" := (@内部同态函子 (X, Y));
 单位对象 : C;                          ( * 单位对象 I * )

 ( * hom_id_iso  : Id [C]  ≅ [Fun]  Curry 内部同态函子 单位对象; * )
 hom_id_iso {x} : x ≅  [unit_object, x] ;    ( * 单位同构 i : x ≅  [I, x] * )

 hom_id {x} : 单位对象 ~>  [x, x] ;                 ( * 恒等 j : I ~>  [x, x] * )
 hom_组合 {x y z} :  [y, z]  ~>  [[x, y] ,  [x, z] ];   ( * 组合 L * )

 hom_右单位 {x y} :
 @hom_组合 x y y ∘ hom_id << 单位对象 ~~>  [[x, y] ,  [x, y] ] >> hom_id;

 hom_ {x y} :
 _ ∘ @hom_组合 x x y
 <<  [x, y]  ~~>  [unit_object, [x, y] ] >>
 到 (hom_id_iso ( [x, y] ))
 }.符号 “[ X , Y ]” := (internal_hom_functor (X, Y))
 (在级别 90，右结合，格式 “[ X ,  Y ]”) : object_scope。

 符号 “[ X , ─ ]” := (Curry internal_hom_functor X)
 (在级别 90，右结合，格式 “[ X ,  ─ ]”) : object_scope。

 符号 “[ ─ , X ]” := (Curry (Flip internal_hom_functor) X)
 (在级别 90，右结合，格式 “[ ─ ,  X ]”) : object_scope。
*)

End Closed.
