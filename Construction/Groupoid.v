Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(*
   * The core groupoid of a category C: its maximal sub-groupoid. 

   --------
   * 范畴 C 的核心群：它的最大子群。
*)

(*
 nLab: https://ncatlab.org/nlab/show/core
 nLab: https://ncatlab.org/nlab/show/groupoid
 Wikipedia: https://en.wikipedia.org/wiki/Groupoid

 A groupoid is a category in which every morphism is an isomorphism
 (invertible). Given a category C, its core is the maximal sub-groupoid:
 the same objects as C, but with only the isomorphisms of C as morphisms.
 Here [Groupoid C] realises that core. Its objects are @obj C; a morphism
 x ~> y is an isomorphism x ≅ y in C (hom := @Isomorphism C); the identity
 is iso_id and composition is iso_compose. Morphism equivalence is equivalence
 of isomorphisms (homset := @iso_setoid C), i.e. two isos agree when their
 `to` and `from` components agree under `≈` (see Theory.Isomorphism).

 The core construction is the underlying-groupoid functor and is right adjoint
 to the inclusion Grpd ↪ Cat: a functor out of a groupoid into C must send
 every morphism to an isomorphism, so it factors through the core. 

 --------
 nLab:  https://ncatlab.org/nlab/show/core 
 nLab:  https://ncatlab.org/nlab/show/groupoid 
 维基百科:  https://en.wikipedia.org/wiki/Groupoid 

 群族是一个范畴，其中每个态射都是同构（可逆）的。给定一个范畴 C，它的核心是最大子群族：
 对象与 C 相同，但态射仅为 C 的同构。在这里 [Groupoid C] 实现了该核心。其对象为 @obj C；一个态射 x ~> y 是 C 中的同构 x ≅ y（hom := @Isomorphism C）；恒等态射为 iso_id，结合为 iso_compose。态射等价是同构的等价（homset := @iso_setoid C），即当 `to` 和 `from` 组件在 `≈` 下相同时，两个同构相等（参见 Theory.Isomorphism）。核心构造是基础群范畴函子，并且是包含函子 Grpd ↪ Cat 的右伴随：从群范畴到 C 的函子必须将每个态射映射为同构，因此它会通过核心进行分解。
*)

(*
 Groupoids before categories, and the core at work

 nLab:  https://ncatlab.org/nlab/show/groupoid
 Paper: Brandt, "Über eine Verallgemeinerung des Gruppenbegriffes",
 Mathematische Annalen 96, 1927
 Paper: Brown, "From groups to groupoids: a brief survey", Bulletin of
 the London Mathematical Society 19, 1987
 Paper: Weinstein, "Groupoids: Unifying Internal and External Symmetry",
 Notices of the American Mathematical Society 43, 1996

 Groupoids predate categories by nearly two decades.  Heinrich Brandt
 introduced and named them in a 1926/27 paper in the Mathematische
 Annalen, the outcome of over thirteen years spent extending Gauss's
 composition of binary quadratic forms to quaternary forms; the same
 circle of ideas let him carry ideal arithmetic over to quaternion
 algebras, a finite groupoid standing in for the classical finite
 abelian class group (Brown 1987).  Brandt in fact required an arrow
 between every pair of objects — the connected case, still called a
 Brandt groupoid — and the modern definition, a category in which
 every morphism is invertible, is the later relaxation.  Brown also
 records the remark that Brandt's axioms influenced Eilenberg and Mac
 Lane's definition of a category, together with Eilenberg's denial of
 it: had they thought of groupoids, they would have used them as an
 example.

 What a groupoid offers beyond a group is symmetry between objects
 rather than of a single object.  Weinstein's survey opens from the
 observation that many objects exhibit what is plainly recognized as
 symmetry yet possess few or no nontrivial automorphisms: a finite
 bathroom tiling has a four-element symmetry group, while its visible
 repetitive pattern is recovered by restricting the transformation
 groupoid of the ambient group action (Weinstein 1996).  The same
 relocation of structure drives the fundamental groupoid π₁(X, A) on
 a set A of base points: for a union with disconnected intersection
 there is no good single choice of base point, and Brown's
 formulation of the van Kampen theorem — one base point per
 component, the result an amalgamated free product of groupoids,
 following Higgins — proves a stronger theorem more simply (Brown
 1987).  Ehresmann, from 1950, added topological and differentiable
 structure and made groupoids a working tool of differential
 geometry; Grothendieck used them to tame the equivalence relations
 arising in moduli problems, and Connes replaced function algebras on
 intractable quotients by groupoid convolution algebras (Brown 1987;
 Weinstein 1996).

 Type theory rediscovered the notion from the inside.  In intensional
 Martin-Löf type theory the identity proofs of a type compose, invert,
 and associate up to higher identity, so each type carries groupoid
 structure rather than a mere equivalence relation; interpreting types
 as groupoids yields a model in which uniqueness of identity proofs is
 not derivable (Hofmann and Streicher, "The groupoid model refutes
 uniqueness of identity proofs", LICS 1994), and the full tower of
 iterated identity types is a weak ω-groupoid (Lumsdaine, "Weak
 ω-categories from intensional type theory", TLCA 2009; van den Berg
 and Garner, "Types are weak ω-groupoids", Proc. London Math. Soc.
 102, 2011).  Groupoids likewise model homotopy 1-types, the first
 rung of the homotopy hypothesis (nLab: groupoid).

 Within this library the core is the setoid of isomorphisms made
 compositional.  Because [Groupoid C] is an honest category, the
 generic rewriting lemmas — [id_left], [comp_assoc],
 [compose_respects] — apply verbatim to chains of isomorphisms, and
 Structure/UniversalProperty.v relies on exactly this, discharging the
 uniqueness leg of a universal property by computing inside [Groupoid]
 of a functor category into Sets.  Theory/Isomorphism.v supplies each
 morphism-level field of the construction, and its [iso_sym] provides
 the inverses that make the result a groupoid rather than merely a
 category.  The file constructs the core of a given C.  An earlier
 revision of this paragraph continued that no standalone category of
 groupoids existed in-tree, so the adjunction remark in the header
 above remained prose rather than a theorem.  That is now a
 correction to make, because both halves have since been built.
 Instance/Grpd.v defines [Grpd] as the full subcategory of [Cat] cut
 out by [IsGroupoid], with [Grpd_Incl] its full and faithful
 inclusion, and Construction/Groupoid/Core.v makes THIS file's
 [Groupoid] the object part of a functor [Core : Cat ⟶ Grpd] and
 proves [Incl_Core_Adjunction : Adjunction Grpd_Incl Core].  The
 other adjoint to the same inclusion — localization, which
 universally inverts every morphism rather than discarding the
 non-invertible ones (nLab: core) — is built in
 Construction/Fractions.v, by generators and relations, with its
 universal property at STRICT strength; that file's header records
 what still stands between it and a packaged [Adjunction], and it is
 NOT Construction/Localization.v, which builds the reflective
 orthogonal-subcategory localization and is a different construction.
 Theory/Category/Semi.v records the complementary weakening of the
 category axioms, dropping identities where the groupoid demands
 inverses. 

 --------
 在范畴之前的群群，以及核心的作用

 nLab: https://ncatlab.org/nlab/show/groupoid
 论文: Brandt, 《Über eine Verallgemeinerung des Gruppenbegriffes》，数学年刊 96, 1927
 论文: Brown, 《从群到群群：简要综述》，伦敦数学学会公报 19, 1987
 论文: Weinstein, 《群群：统一内在与外在对称性》，美国数学学会通告 43, 1996群oid比范畴早近二十年。Heinrich Brandt 在 1926/27 年发表在《Mathematische Annalen》上的一篇论文中引入并命名了它们，这篇论文是他在扩展高斯的二元二次型的复合到四元型过程中花费超过十三年的成果；同一思想体系使他能够将理想算术推广到四元数代数，有限群oid代替了经典的有限阿贝尔类群（Brown 1987）。实际上，Brandt 要求每对对象之间都有一条箭头——连通情况，仍称为 Brandt 群oid——而现代的定义，即每个态射都可逆的范畴，则是后来的一种放宽。布朗还记录了这样的评论，即布兰特的公理影响了埃伦贝格和麦克莱恩对范畴的定义，同时也记录了埃伦贝格对此的否认：如果他们考虑过群类，他们就会用它们作为示例。群族相比群提供的是对象之间的对称性，而不是单个对象的对称性。韦恩斯坦的综述从一个观察开始：许多对象表现出明显可以识别的对称性，但几乎没有或根本没有非平凡的自同构：一个有限的浴室瓷砖具有一个四元素的对称群，而其可见的重复图案是通过限制环境群作用的变换群族来恢复的（韦恩斯坦 1996）。同样，结构的重新定位驱动了集合 A 上的基本群范畴 π₁(X, A)：对于交集不连通的并集，没有一个好的单一基点选择，而 Brown 对 van Kampen 定理的表述——每个分支一个基点，结果是群范畴的合并自由积，遵循 Higgins——更简单地证明了一个更强的定理（Brown 1987）。Ehresmann 从 1950 年起，加入了拓扑和可微分结构，使群范畴成为微分几何的工作工具；Grothendieck 用它们来驯服模问题中出现的等价关系，Connes 则用群范畴卷积代替了难以处理的商上的函数代数（Brown 1987；Weinstein 1996）。类型理论从内部重新发现了这个概念。在内涵型马丁-洛夫类型理论中，一个类型的等同性证明可以组合、逆转，并且在高阶等同性下满足结合律，因此每个类型具有群oid结构，而不仅仅是等价关系；将类型解释为群oid可以得到一个模型，其中等同性证明的唯一性不可导出（Hofmann 和 Streicher，《群oid模型反驳等同性证明的唯一性》，LICS 1994），而完整的迭代等同性类型的层级是弱 ω-群oid（Lumsdaine，《从内涵型理论得到弱 ω-范畴》，TLCA 2009；van den Berg 和 Garner，《类型是弱 ω-群oid》，伦敦数学学会会刊 102, 2011）。群oid同样能够模拟同伦 1 型，这是同伦假设的第一阶梯（nLab: groupoid）。在这个库中，核心是由同构构成的集合，并且是可组合的。因为  [Groupoid C] 是一个真实的范畴，所以通用的重写引理——[id_left]、[comp_assoc]、[compose_respects]——可以逐字应用于同构链，而 Structure/UniversalProperty.v 正是依赖于这一点，通过在 [Groupoid] 中计算函子范畴到 Sets 的过程来完成一个泛性质的唯一性部分。Theory/Isomorphism.v 提供了构造中的每一个态射级字段，其 [iso_sym] 提供了逆，使结果成为一个群oid而不仅仅是一个范畴。该文件构造了给定 C 的核心。本段早期的修订版本继续说明树中不存在独立的群oid范畴，因此上面标题中的伴随性评论仍然是文字说明，而非定理。现在需要进行一个修正，因为两个部分自那以后都已经建成。Instance/Grpd.v 将 [Grpd] 定义为由 [IsGroupoid] 切出的 [Cat] 的完全子范畴，并且 [Grpd_Incl] 是它的全忠实包含，而 Construction/Groupoid/Core.v 将该文件的 [Groupoid] 作为函子 [Core : Cat ⟶ Grpd] 的对象部分，并证明 [Incl_Core_Adjunction : Adjunction Grpd_Incl Core]。同一个包含的另一伴随——局部化，它普遍地把每个态射取逆，而不是舍弃非可逆的态射（nLab: core）——是在 Construction/Fractions.v 中构建的，通过生成元和关系，并且其普遍性质具有严格强度；该文件的头部记录了它与封装的 [Adjunction] 之间还存在的内容，并且它不是 Construction/Localization.v，后者构建反射正交子范畴的局部化，是一个不同的构造。Theory/Category/Semi.v 记录了范畴公理的互补弱化，在群范畴要求逆元的情况下舍弃恒等态射。
*)

Program Definition Groupoid (C : Category) : Category := {|
  obj     := @obj C;
  hom     := @Isomorphism C;
  homset  := @iso_setoid C;
  id      := @iso_id C;
  compose := @iso_compose C
|}.
