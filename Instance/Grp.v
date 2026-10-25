Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Monoid.
Require Import Category.Structure.Group.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** * The category of groups / * 群的范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/Grp
 nLab:      https://ncatlab.org/nlab/show/group
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_groups

 [Grp] is the category of groups over [Sets]: an object is a setoid whose
 `≈` is PROPOSITIONAL ([grp_prop]), carrying an associative binary
 operation [grp_mul] with unit [grp_unit] and an inversion [grp_inv]; a
 morphism is a setoid map preserving the unit and the operation; two
 morphisms are equivalent when their underlying maps agree pointwise.  The
 file is modelled directly on Instance/CMon.v, whose [CMonObject] /
 [CMonHom] / [CMon] triple it mirrors at the hom record and the category;
 the object records differ by design (commutativity there, inversion here).

 Since the PR "algebraic carriers are sets" (2026-09-17) the record carries
 the field [grp_prop] of Lib/Setoid/Propositional.v's class [PropEquiv]: a
 [Prop]-valued relation on the carrier that holds exactly when `≈` does.  A
 group in this library is therefore a group on a SET in Bishop's sense, not
 on an arbitrary proof-relevant setoid; Lib/Setoid/Propositional.v's header
 says why -- a type of congruences on a carrier is carrier-sized exactly
 when the congruences are [Prop]-valued, which is what the solution-set
 condition of Mac Lane's general adjoint functor theorem needs at a
 concrete algebraic category.

 An earlier revision of this paragraph added "including the universe
 discipline: nothing here is annotated, so [Grp] is universe-polymorphic
 exactly as [CMon] is".  The SHAPE of that claim survives, but neither is
 inferred any more: [Grp] and [CMon] are both pinned by hand, for the
 reason recorded at the definition of [Grp] below.

 AXIOM ECONOMY.  The record below carries the SMALLEST law set that
 still presents a group, and every omission is discharged as a lemma
 rather than assumed:

 - Only the LEFT unit law [grp_mul_unit_l] and the LEFT inverse law
 [grp_mul_inv_l] are fields.  The right-handed forms are derived
 ([grp_mul_inv_r], [grp_mul_unit_r]) by the classical argument that
 runs left inverse + associativity into right inverse and then into
 the right unit law.  This is the group-theoretic strengthening of
 what Instance/CMon.v does with commutativity, where only
 [cmon_plus_zero_r] is derivable.

 - [grp_inv] carries NO respectfulness field.  Congruence of inversion
 for `≈` is a THEOREM ([grp_inv_respects_law], exported as the
 instance [grp_inv_Proper]): from a ≈ b one gets
 grp_inv a * b ≈ grp_inv a * a ≈ grp_unit, and uniqueness of
 one-sided inverses ([grp_inv_unique_l]) then forces
 grp_inv a ≈ grp_inv b.  Only [grp_mul_respects] is a field.  A
 constructor of a [GrpObject] therefore owes four proofs, not seven.
 (Since [grp_prop] landed there is a fifth obligation, but it is a
 DATUM about the carrier rather than a group law, and at the
 constructions below it is discharged by a transport of
 Lib/Setoid/Propositional.v rather than proved by hand.)

 [GrpHom] does keep unit preservation as a field alongside
 multiplication preservation, matching [CMonHom] (Instance/CMon.v)
 and the issue's stated shape.  That field is REDUNDANT, and the file
 says so constructively rather than in prose: [grp_map_unit_from_mul]
 derives it from multiplication preservation alone by cancelling
 f(e) from f(e) * f(e) ≈ f(e) * e, and [Build_GrpHom'] is the resulting
 smart constructor that asks only for the multiplication law.
 Inverse preservation is not a field either: [grp_map_inv] derives it.

 WHAT THIS FILE ESTABLISHES BEYOND THE CATEGORY.  The forgetful functor
 [Grp_Forget] to [Sets] with its faithfulness ([Grp_Forget_Faithful]);
 the one-element group as a zero object ([Grp_Zero], packaged for
 Structure/ZeroObject.v, whose [ZeroObject] class wants a [Terminal],
 an [Initial] and a coincidence isomorphism -- here the identity, since
 one record plays both roles, exactly as at Instance/CMon/Biproduct.v);
 binary direct products as a [Cartesian] structure ([Grp_Cartesian],
 against the class at Structure/Cartesian.v); the characterization
 of monomorphisms as the injections ([Grp_injectivity_is_monic]); the
 reconciliation with the internal [GroupObject] of Structure/Group.v
 in both directions; and Riehl's opposite-group endofunctor with its
 inversion natural isomorphism. 

 --------
 nLab：       https://ncatlab.org/nlab/show/Grp 
 nLab：       https://ncatlab.org/nlab/show/group 
 维基百科：  https://en.wikipedia.org/wiki/Category_of_groups 

 [Grp] 是 [Sets] 上的群的范畴：一个对象是一个集合类，其 `≈` 是命题性的（[grp_prop]），带有一个结合二元运算 [grp_mul]，具有单位 [grp_unit] 和逆元 [grp_inv]；一个态射是保持单位和运算的集合类映射；当两个态射的底层映射在每一点上相同时，它们等价。该文件直接基于 Instance/CMon.v 建模，其 [CMonObject] / [CMonHom] / [CMon] 三元组在同态记录和范畴中被镜像；对象记录因设计而异（那里是交换性，这里是逆元）。自从 PR “代数载体是集合”（2026-09-17）以来，该记录携带了 Lib/Setoid/Propositional.v 中类 [PropEquiv] 的字段 [grp_prop]：在载体上的一个 [Prop] 值关系，当且仅当 `≈` 发生时成立。因此，该库中的群是在 Bishop 意义上的 SET 上的群，而不是任意与证明相关的等价类；Lib/Setoid/Propositional.v 的标题说明了原因——当同余是 [Prop] 值时，载体上的同余类型恰好是载体大小，这正是 Mac Lane 的一般伴随函子定理在具体代数范畴中所需要的解集条件。该段的早期修订版添加了“包括宇宙
 学科：这里没有任何注解，因此 [Grp] 和 [CMon] 一样是宇宙多态的”。该声明的形状仍然保留，但现在两者都不再被推断：[Grp] 和 [CMon] 都是手动固定的，原因记录在下面 [Grp] 的定义中。

 公理经济性。下面的记录包含了仍然呈现群的最小定律集，每个遗漏都作为引理处理，而不是假设：- 只有左单位律 [grp_mul_unit_l] 和左逆元律 [grp_mul_inv_l] 是域。右手形式（[grp_mul_inv_r], [grp_mul_unit_r]）是通过经典论证得出的，该论证将左逆元律 + 结合律推导出右逆元律，再推导出右单位律。这是对 Instance/CMon.v 使用交换律所做工作的群论强化，其中只有 [cmon_plus_zero_r] 是可推导的。- [grp_inv] 不包含尊重性字段。`≈` 的反元素一致性是一个定理（[grp_inv_respects_law]，导出为实例 [grp_inv_Proper]）：从 a ≈ b 可以得到 grp_inv a * b ≈ grp_inv a * a ≈ grp_unit，并且单侧逆元的唯一性（[grp_inv_unique_l]）随后迫使 grp_inv a ≈ grp_inv b。只有 [grp_mul_respects] 是一个字段。因此，[GrpObject] 的构造函数需要四个证明，而不是七个。（由于 [grp_prop] 在那里出现，这是第五个义务，但它是关于载体的一个 DATUM，而不是群律，在下面的构造中，它通过 Lib/Setoid/Propositional.v 的传输而解决，而不是手工证明。）[GrpHom] 确实将单位保持作为一个字段与乘法保持一起保存，匹配 [CMonHom]（Instance/CMon.v）和该问题所述的形式。该字段是多余的，而且文件以建设性的方式说明了这一点，而不是通过文字描述：[grp_map_unit_from_mul] 仅通过从 f(e) * f(e) ≈ f(e) * e 中消去 f(e) 就从乘法保持中导出了它，而 [Build_GrpHom'] 是由此产生的智能构造器，它只需要乘法律。逆元保持也不是一个字段：[grp_map_inv] 导出了它。本文件在范畴之外建立的内容。 忘记函子 [Grp_Forget] 到 [Sets] 及其忠实性（[Grp_Forget_Faithful]）；作为零对象的一元素群（[Grp_Zero]，为 Structure/ZeroObject.v 打包，其 [ZeroObject] 类需要一个 [Terminal]，一个 [Initial] 和一个一致同构——这里是恒等同构，因为一个记录扮演两个角色，正如 Instance/CMon/Biproduct.v 中一样）；二元直积作为 [Cartesian] 结构（[Grp_Cartesian]，与 Structure/Cartesian.v 中的类对应）；将单射表征为单态射（[Grp_injectivity_is_monic]）；以及与 Structure/Group.v 中的内部 [GroupObject] 双向协调；还有 Riehl 的对偶群自函子及其逆转自然同构。
*)

(*
 Where the category of groups comes from, and what it is for

 Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, Sections I.5 (Monics, Epis, and Zeros,
 p. 19) and I.6 (Foundations, p. 21)
 Book:  Riehl, "Category Theory in Context", Dover, 2016, Section 1.4
 (Naturality)
 Paper: Eilenberg, Mac Lane, "General theory of natural equivalences",
 Trans. AMS 58, 1945
 Paper: Mac Lane, "Duality for groups", Bulletin of the AMS 56, 1950

 Groups are the founding example of the subject.  Eilenberg and Mac
 Lane's 1945 paper reaches categories and functors from group theory
 and topology, and Mac Lane's "Duality for groups" (1950) is the
 deliberate exercise of recasting group theory so that only
 homomorphisms and composition appear, in order that reversing every
 arrow should carry each notion to its dual -- the direct product to
 the free product, and so on.  The library already collects that
 dividend structurally (Structure/Cocartesian.v is Structure/Cartesian.v
 read in the opposite category), so it is fitting that the concrete
 category the programme was written about should exist in the tree.

 Two of Mac Lane's Chapter I sections bear directly on what is proved
 below.  Section I.5 is titled "Monics, Epis, and Zeros" and is where
 the three notions this file instantiates for groups are introduced;
 Section I.6, "Foundations", is where the size question raised by
 speaking of THE category of all groups is settled by restricting to
 small groups.  This formalization sidesteps that question the way the
 rest of the library does: [Grp] is universe-polymorphic, and the
 universe level of the carriers is a parameter rather than a decision.

 The zero object is where groups part company with sets.  In [Sets] the
 empty setoid is initial and the singleton is terminal, and they are
 different objects; in [Grp] the one-element group is BOTH, because
 there is no empty group (a group must contain a unit) and because a
 homomorphism out of the trivial group is pinned by [grp_map_unit].
 [Grp_Zero] records the coincidence.  Instance/CMon/Biproduct.v
 makes the same observation for commutative monoids, where it is the
 first step of a semiadditive structure; groups go further -- [Grp] is
 not semiadditive, since the direct product is not a biproduct unless
 the groups are abelian, so no biproduct claim is made here.

 Monomorphisms in [Grp] are exactly the injective homomorphisms, and
 this is genuinely a theorem rather than a definition -- the same
 statement is false for epimorphisms in many algebraic categories (the
 inclusion of the integers into the rationals is epic in rings without
 being surjective, Riehl's Exercises 1.2.iv and 1.6.v(ii)).  One direction is soft:
 an injection is monic in any concrete category, and it is proved here
 directly, by evaluating the two competing maps at a point.  Riehl's
 Exercise 1.6.iv is the abstract route to the same direction -- any
 faithful functor reflects monomorphisms, and [Grp_Forget_Faithful]
 supplies the faithful functor.  The other direction needs a PROBE
 group, an object with
 enough maps into the source to detect a difference, and the literature
 offers two standard choices.  One is the free group on one generator,
 the integers, whose homomorphisms into G are in bijection with the
 elements of G; the other is the kernel, mapped into G twice, once by
 inclusion and once trivially.  This file takes the kernel route
 ([Grp_kernel], [Grp_kernel_incl], [Grp_kernel_triv]): it is the
 cheaper of the two in a setoid library, because the kernel is a
 sub-setoid of a carrier already in hand, whereas the integers would
 have to be built along with an integer-power homomorphism and its
 sign-case analysis.  The two probes prove the same statement, and the
 statement proved here is the full biconditional at full strength.

 The last construction is Riehl's.  Category Theory in Context,
 Section 1.4 (Naturality), Example 1.4.4(vi) observes that the opposite
 group is a COVARIANT endofunctor of the category of groups, that it is
 naturally isomorphic to the identity, and that the component at G is
 the map sending g to its inverse -- which "does not define an
 automorphism of G, ... but it does define a homomorphism
 eta_G : G -> G^op, indeed an isomorphism", the elided clause being that
 inversion does not commute with the multiplication of G.
 That sentence is the whole content of [Grp_inv_to] below: inversion is
 an antihomomorphism ([grp_inv_mul]), which is precisely what makes it
 a homomorphism into the opposite group.  Naturality is then
 [grp_map_inv], the derived fact that homomorphisms commute with
 inversion.  [Grp_op_Isomorphism] assembles the two directions into an
 isomorphism in the functor category [[Grp, Grp]].

 Three earlier in-tree treatments of groups are superseded or
 complemented by this file, none of which built the category.
 Structure/Group.v defines [GroupObject], a group internal to a
 cartesian monoidal category -- the right notion for topological
 groups, group schemes and Hopf algebras, but internal-only.
 [Grp_GroupObject] and [GroupObject_GrpObject] below show that at
 C = [Sets] with the cartesian monoidal structure of
 Structure/Monoidal/Internal/Product.v the two notions carry the
 same data, in both directions and with the round trip on the
 operations checked by computation.  Instance/Comp.v defines
 [Group] as a universal-algebra structure (an algebra for a signature
 with equations) with no category attached and, unlike this file,
 at the cost of [functional_extensionality].  Theory/Algebra/Monoid.v
 and Instance/CMon.v supply the unit-and-multiplication half of the
 structure without inverses. 

 --------
 群的范畴来源以及其用途

 书籍：Mac Lane，《为工作数学家而作的范畴论》，第2版，Springer GTM 5, 1998，第I.5节（单射、满射及零元，p.19）和I.6节（基础，p.21）
 书籍：Riehl，《语境中的范畴论》，Dover, 2016，第1.4节（自然性）
 论文：Eilenberg, Mac Lane，《自然等价的一般理论》，美国数学会学报 58, 1945
 论文：Mac Lane，《群的对偶性》，美国数学会通报 56, 1950群是该学科的奠基范例。Eilenberg 和 Mac Lane 在 1945 年的论文中从群论和拓扑学出发，提出了范畴和函子，而 Mac Lane 的《群的对偶性》(1950) 则是有意将群论重新表述，使得只出现同态和复合操作，从而反转每一条箭头时可以将每个概念映射到其对偶——直积映射到自由积，依此类推。该库已经在结构上收集了这一份红利（Structure/Cocartesian.v 就是 Structure/Cartesian.v 在对偶范畴中的解读），因此由该程序所编写的具体范畴出现在树中是很合适的。麦克莱恩第一章的两个部分与下面的证明直接相关。第一章第I.5节标题为“单态、映射和零”，这是引入本文件针对群体实例化的三个概念的地方；第I.6节“基础”，是通过限制到小群体来解决谈论所有群体的‘THE’范畴所引起的大小问题。这个形式化像库的其他部分一样回避了这个问题：[Grp] 是宇宙多态的，并且承载者的宇宙层级是一个参数，而不是固定的决定。零对象是群与集合分道扬镳的地方。在  [Sets] 中，空集合是初始对象，单元素集合是终对象，并且它们是不同的对象；在  [Grp] 中，单元素群同时是初始对象和终对象，因为不存在空群（一个群必须包含单位元），并且从平凡群出发的同态被 [grp_map_unit] 所固定。[Grp_Zero] 记录了这种巧合。Instance/CMon/Biproduct.v 对交换幺半群做了同样的观察，这是半加性结构的第一步；群更进一步——[Grp] 不是半加性的，因为直积只有在群是阿贝尔群时才是双积，因此这里没有提出双积的主张。在  [Grp]  中，单态（Monomorphisms）正好是单射同态，这是一个真正的定理而不是定义——在许多代数范畴中，这一陈述对于满态（epimorphisms）是错误的（整数嵌入有理数在环中是满射但并非全射，见 Riehl 的练习 1.2.iv 和 1.6.v(ii)）。一个方向比较简单：在任何具体范畴中，注入映射是单态，这里通过在一点处评估两个竞争映射直接证明了这一点。Riehl 的练习 1.6.iv 是通向同一方向的抽象途径——任何忠实函子都会反映单态，而  [Grp_Forget_Faithful]  提供了这样的忠实函子。另一个方向则需要一个探测（PROBE）群，即一个具有足够映射到源对象以检测差异的对象，文献中提供了两个标准选择。一个是一个生成元的自由群，即整数，它们映射到 G 的同态与 G 的元素之间存在一一对应关系；另一个是核，通过两次映射到 G，一次通过包含映射，一次通过平凡映射。该文件采用核的方式（[Grp_kernel]，[Grp_kernel_incl]，[Grp_kernel_triv]）：在集合体库中这是两者中较便宜的一种，因为核是已有承载对象的子集合体，而整数则必须与整数幂同态及其符号情况分析一同构建。两个探针证明的是相同的陈述，这里证明的陈述是在完全强度下的完整双条件命题。最后的构造是Riehl的。《情境中的范畴论》，第1.4节（自然性），例1.4.4(vi)指出，对立群是群范畴的一个协变端函子，它自然同构于恒等函子，并且在G处的分量是将g映射到其逆元的映射——这“并不定义G的自同构，……但它确实定义了一个同态 eta_G : G -> G^op，实际上是一个同构”，省略的部分是指取逆运算与G的乘法不交换。该句就是下面[Grp_inv_to]的全部内容：取逆是一个反同态（[grp_inv_mul]），这恰恰使它成为到对立群的同态。自然性然后是[grp_map_inv]，即同态与取逆运算交换的派生事实。[Grp_op_Isomorphism] 将两个方向组装成函子范畴 [[Grp, Grp] 中的同构。三个早先关于群的树内处理已被此文件取代或补充，但它们都没有构建类别。Structure/Group.v 定义了 [GroupObject]，这是一个在笛卡尔幺半群范畴内部的群——这是拓扑群、群方案和霍普夫代数的正确概念，但仅限于内部。下面的 [Grp_GroupObject] 和 [GroupObject_GrpObject] 显示，在 C = [Sets] 并使用 Structure/Monoidal/Internal/Product.v 的笛卡尔幺半群结构时，这两种概念携带相同的数据，在两个方向上都是如此，并且通过计算检查了操作的往返。Instance/Comp.v 将 [Group] 定义为一个通用代数结构（带有方程的签名的代数），没有附加类别，并且与此文件不同，这需要付出 [functional_extensionality] 的代价。Theory/Algebra/Monoid.v 和 Instance/CMon.v 提供了没有逆元的结构的单位与乘法部分。
*)

(*
 A group: a setoid together with a unit element, a binary operation and
 an inversion, where only the operation is required to respect `≈` and
 only the left-handed unit and inverse laws are required to hold.  The
 right-handed laws and the respectfulness of inversion are derived
 below.

 [grp_prop] is the LAST field deliberately, for the reason Instance/CMon.v
 gives for [cmon_prop]: every construction site in the tree writes the
 record with named fields under [Program] or [unshelve notypeclasses
 refine], both of which emit obligations in field order, so a field at the
 end leaves the numbering of every existing obligation alone and adds one
 at the end. 

 --------
 群：一个带有单位元素、二元运算和逆元的集体，在这里只有运算需要遵守 `≈`，并且只要求左单位和左逆律成立。右律和逆元的顺从性将在下面推导。

 [grp_prop] 故意放在最后一个字段，其原因与 Instance/CMon.v 给 [cmon_prop] 的原因相同：树中的每个构造点都在 [Program] 下或使用 [unshelve notypeclasses refine] 写带命名字段的记录，这两种方式都会按字段顺序生成义务，因此将字段放在末尾可以保持所有现有义务的编号不变，并在末尾添加一个新的。
*)
Record GrpObject := {
  grp_setoid :> SetoidObject;

  grp_unit : carrier grp_setoid;
  grp_mul  : carrier grp_setoid → carrier grp_setoid → carrier grp_setoid;
  grp_inv  : carrier grp_setoid → carrier grp_setoid;

  grp_mul_respects : Proper (equiv ==> equiv ==> equiv) grp_mul;

  grp_mul_assoc : ∀ a b c,
    grp_mul (grp_mul a b) c ≈ grp_mul a (grp_mul b c);
  grp_mul_unit_l : ∀ a, grp_mul grp_unit a ≈ a;
  grp_mul_inv_l  : ∀ a, grp_mul (grp_inv a) a ≈ grp_unit;

  (*
 The carrier is a SET: its `≈` is logically equivalent to a [Prop]-valued
 relation.  See Lib/Setoid/Propositional.v. 

 --------
 载体是一个集合：它的 `≈` 在逻辑上等价于一个取值为 [Prop] 的关系。请参见 Lib/Setoid/Propositional.v。
*)
  grp_prop : PropEquiv (is_setoid grp_setoid)
}.

#[export] Existing Instance grp_mul_respects.
#[export] Existing Instance grp_prop.

Section GrpFacts.

Context (G : GrpObject).

(*
 The right inverse law, from the left one.  The classical argument:
 a * a⁻¹ is dragged through a⁻¹⁻¹ * (a⁻¹ * (a * a⁻¹)), whose inner
 bracket collapses to a⁻¹ by the left laws, leaving a⁻¹⁻¹ * a⁻¹. 

 --------
 由左逆律得到右逆律。经典的论证：
 a * a⁻¹ 被拖到 a⁻¹⁻¹ * (a⁻¹ * (a * a⁻¹)) 中，其内部括号根据左律化简为 a⁻¹，剩下 a⁻¹⁻¹ * a⁻¹。
*)
Lemma grp_mul_inv_r (a : carrier G) : grp_mul G a (grp_inv G a) ≈ grp_unit G.
Proof.
  assert (Hinner : grp_mul G (grp_inv G a) (grp_mul G a (grp_inv G a))
                     ≈ grp_inv G a).
  { rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_l.
    apply grp_mul_unit_l. }
  transitivity (grp_mul G (grp_inv G (grp_inv G a))
                  (grp_mul G (grp_inv G a) (grp_mul G a (grp_inv G a)))).
  - rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_l.
    symmetry; apply grp_mul_unit_l.
  - rewrite Hinner.
    apply grp_mul_inv_l.
Qed.

(* The right unit law, from the left one and the right inverse law. / 由左单位律和右逆律得出的右单位律。 *)
Lemma grp_mul_unit_r (a : carrier G) : grp_mul G a (grp_unit G) ≈ a.
Proof.
  transitivity (grp_mul G a (grp_mul G (grp_inv G a) a)).
  - rewrite grp_mul_inv_l.
    reflexivity.
  - rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_r.
    apply grp_mul_unit_l.
Qed.

(* Uniqueness of inverses, right-handed form: anything absorbing a on the right is the chosen inverse of a. / 逆元的唯一性，右手形式：任何在右侧吸收 a 的元素都是 a 的选定逆元。 *)
Lemma grp_inv_unique_r (a b : carrier G) :
  grp_mul G a b ≈ grp_unit G → b ≈ grp_inv G a.
Proof.
  intro Hab.
  transitivity (grp_mul G (grp_unit G) b).
  - symmetry; apply grp_mul_unit_l.
  - rewrite <- (grp_mul_inv_l G a).
    rewrite grp_mul_assoc.
    rewrite Hab.
    apply grp_mul_unit_r.
Qed.

(* Uniqueness of inverses, left-handed form. / 逆元的唯一性，左手形式。 *)
Lemma grp_inv_unique_l (a b : carrier G) :
  grp_mul G b a ≈ grp_unit G → b ≈ grp_inv G a.
Proof.
  intro Hba.
  transitivity (grp_mul G b (grp_unit G)).
  - symmetry; apply grp_mul_unit_r.
  - rewrite <- (grp_mul_inv_r a).
    rewrite <- grp_mul_assoc.
    rewrite Hba.
    apply grp_mul_unit_l.
Qed.

(* Inversion respects `≈`. This is the field the record does not carry: from a ≈ b, the element grp_inv a is a left inverse of b, and left inverses are unique. / 逆运算遵守 `≈`。 这是记录未包含的字段： 从 a ≈ b，元素 grp_inv a 是 b 的左逆，并且左逆是唯一的。 *)
Lemma grp_inv_respects_law (a b : carrier G) :
  a ≈ b → grp_inv G a ≈ grp_inv G b.
Proof.
  intro Hab.
  apply grp_inv_unique_l.
  rewrite <- Hab.
  apply grp_mul_inv_l.
Qed.

End GrpFacts.

#[export] Instance grp_inv_Proper (G : GrpObject) :
  Proper (equiv ==> equiv) (grp_inv G) := grp_inv_respects_law G.

Section GrpFacts2.

Context (G : GrpObject).

Lemma grp_inv_unit : grp_inv G (grp_unit G) ≈ grp_unit G.
Proof.
  symmetry.
  apply grp_inv_unique_l.
  apply grp_mul_unit_l.
Qed.

Lemma grp_inv_inv (a : carrier G) : grp_inv G (grp_inv G a) ≈ a.
Proof.
  symmetry.
  apply grp_inv_unique_l.
  apply grp_mul_inv_r.
Qed.

(*
 Inversion is an ANTIhomomorphism: it reverses the order of a product.
 This is the fact that makes inversion a homomorphism into the opposite
 group rather than an automorphism (Riehl, Example 1.4.4(vi)). 

 --------
 取逆是一个反同态：它会反转乘积的顺序。这一事实使得取逆成为一个到对立群的同态，而不是自同构（Riehl，例 1.4.4(vi)）。
*)
Lemma grp_inv_mul (a b : carrier G) :
  grp_inv G (grp_mul G a b) ≈ grp_mul G (grp_inv G b) (grp_inv G a).
Proof.
  symmetry.
  apply grp_inv_unique_l.
  rewrite grp_mul_assoc.
  rewrite <- (grp_mul_assoc G (grp_inv G a) a b).
  rewrite grp_mul_inv_l.
  rewrite grp_mul_unit_l.
  apply grp_mul_inv_l.
Qed.

Lemma grp_cancel_l (a b c : carrier G) :
  grp_mul G a b ≈ grp_mul G a c → b ≈ c.
Proof.
  intro Habc.
  transitivity (grp_mul G (grp_mul G (grp_inv G a) a) b).
  - rewrite grp_mul_inv_l.
    symmetry; apply grp_mul_unit_l.
  - rewrite grp_mul_assoc.
    rewrite Habc.
    rewrite <- grp_mul_assoc.
    rewrite grp_mul_inv_l.
    apply grp_mul_unit_l.
Qed.

Lemma grp_cancel_r (a b c : carrier G) :
  grp_mul G b a ≈ grp_mul G c a → b ≈ c.
Proof.
  intro Habc.
  transitivity (grp_mul G b (grp_mul G a (grp_inv G a))).
  - rewrite grp_mul_inv_r.
    symmetry; apply grp_mul_unit_r.
  - rewrite <- grp_mul_assoc.
    rewrite Habc.
    rewrite grp_mul_assoc.
    rewrite grp_mul_inv_r.
    apply grp_mul_unit_r.
Qed.

End GrpFacts2.

(* A homomorphism of groups: a setoid map on the carriers preserving the unit and the operation. Preservation of inversion is NOT a field; it is [grp_map_inv] below. / 群的同态：在承载集合上的一个集合映射，保持单位元和运算。 保持逆元不是一个域；它在下面是 [grp_map_inv]。 *)
Record GrpHom (G H : GrpObject) := {
  grp_map :> SetoidMorphism (grp_setoid G) (grp_setoid H);

  grp_map_unit : grp_map (grp_unit G) ≈ grp_unit H;
  grp_map_mul : ∀ a b,
    grp_map (grp_mul G a b) ≈ grp_mul H (grp_map a) (grp_map b)
}.

Arguments grp_map {G H} _.
Arguments grp_map_unit {G H} _.
Arguments grp_map_mul {G H} _ _ _.

(*
 Homomorphisms preserve inversion.  f (a⁻¹) is a left inverse of f a,
 because f carries a⁻¹ * a ≈ e to f(a⁻¹) * f(a) ≈ e; uniqueness of left
 inverses finishes. 

 --------
 同态保留逆元。f(a⁻¹) 是 f(a) 的左逆元，因为 f 将 a⁻¹ * a ≈ e 映射为 f(a⁻¹) * f(a) ≈ e；左逆元的唯一性完成证明。
*)
Lemma grp_map_inv {G H : GrpObject} (f : GrpHom G H) (a : carrier G) :
  grp_map f (grp_inv G a) ≈ grp_inv H (grp_map f a).
Proof.
  apply grp_inv_unique_l.
  rewrite <- grp_map_mul.
  rewrite grp_mul_inv_l.
  apply grp_map_unit.
Qed.

(*
 The unit-preservation FIELD of [GrpHom] is redundant: it follows from
 multiplication preservation by cancelling f e from
 f e * f e ≈ f (e * e) ≈ f e ≈ f e * e.  The field is retained anyway,
 to mirror [cmon_map_zero] at Instance/CMon.v and to keep the
 projection available without a detour; [Build_GrpHom'] is the
 constructor that exploits the redundancy. 

 --------
 [GrpHom] 的单位保持字段是多余的：它可以通过取消 f e 从 f e * f e ≈ f (e * e) ≈ f e ≈ f e * e 来得出乘法保持性。无论如何，该字段仍然保留，以便在 Instance/CMon.v 中镜像 [cmon_map_zero]，并保持投影可用而无需绕道；[Build_GrpHom'] 是利用该冗余的构造函数。
*)
Lemma grp_map_unit_from_mul {G H : GrpObject}
      (f : SetoidMorphism (grp_setoid G) (grp_setoid H))
      (Hmul : ∀ a b, f (grp_mul G a b) ≈ grp_mul H (f a) (f b)) :
  f (grp_unit G) ≈ grp_unit H.
Proof.
  apply (grp_cancel_l H (f (grp_unit G))).
  rewrite <- Hmul.
  rewrite grp_mul_unit_l.
  symmetry; apply grp_mul_unit_r.
Qed.

(*
 Smart constructor: a setoid map preserving multiplication is already a
 group homomorphism. 

 --------
 智能构造函数：保持乘法的等价关系映射已经是一个群同态。
*)
Definition Build_GrpHom' {G H : GrpObject}
        (f : SetoidMorphism (grp_setoid G) (grp_setoid H))
        (Hmul : ∀ a b, f (grp_mul G a b) ≈ grp_mul H (f a) (f b)) :
  GrpHom G H :=
  {| grp_map      := f
   ; grp_map_unit := grp_map_unit_from_mul f Hmul
   ; grp_map_mul  := Hmul |}.

#[local] Obligation Tactic := idtac.

(* The hom-setoid: homomorphisms are compared by their underlying maps, pointwise up to the codomain's `≈` (as in [Sets]). / 同态集: 同态通过其底层映射进行比较，在值域的 `≈` 上逐点比较（如 [Sets] 所示）。 *)
#[export]
Program Instance GrpHom_Setoid {G H : GrpObject} : Setoid (GrpHom G H) := {|
  equiv := fun f g => ∀ a, grp_map f a ≈ grp_map g a
|}.
Next Obligation.
  intros G H.
  constructor.
  - intros f a.
    reflexivity.
  - intros f g Hfg a.
    symmetry.
    apply Hfg.
  - intros f g h Hfg Hgh a.
    transitivity (grp_map g a).
    + apply Hfg.
    + apply Hgh.
Qed.

(*
 G1: the hom-setoid is propositional, pointwise into the CODOMAIN's own
 [grp_prop].  The domain needs nothing -- the relation quantifies over its
 carrier but never compares two of its elements.  This is the same shape as
 [hom_PropEquiv] (Instance/Sets/Propositional.v) and as
 [CMonHom_PropEquiv] (Instance/CMon.v), restated here because
 [GrpHom_Setoid] is a setoid on [GrpHom G H] rather than on
 [SetoidMorphism]s, and the two records are not convertible. 

 --------
 G1: 同态集是命题性的，在值域自身的 [grp_prop] 中逐点定义。定义域不需要任何东西——这个关系量化其载体，但从不比较其两个元素。这与 [hom_PropEquiv]（Instance/Sets/Propositional.v）以及 [CMonHom_PropEquiv]（Instance/CMon.v）的形式相同，在此重述，因为 [GrpHom_Setoid] 是 [GrpHom G H] 上的集合而不是 [SetoidMorphism] 上的集合，并且这两个记录不可转换。
*)
#[export] Instance GrpHom_PropEquiv {G H : GrpObject} :
  PropEquiv (@GrpHom_Setoid G H).
Proof.
  unshelve refine
    {| pequiv := fun f g : GrpHom G H =>
                   forall a : carrier (grp_setoid G),
                     @pequiv _ _ (grp_prop H) (grp_map f a) (grp_map g a) |}.
  - intros f g Hfg a; exact (pequiv_to _ _ (Hfg a)).
  - intros f g Hfg a; exact (pequiv_from _ _ (Hfg a)).
Defined.

(*
 The identity homomorphism: the identity setoid map, which preserves the
 unit and the operation on the nose. 

 --------
 恒等同态：恒等集合商映射，严格保持单位元和运算。
*)
Program Definition grp_hom_id {G : GrpObject} : GrpHom G G := {|
  grp_map := setoid_morphism_id
|}.
Next Obligation.
  intros G; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros G a b; simpl.
  reflexivity.
Qed.

(*
 Composition of homomorphisms: composition of the underlying setoid maps;
 preservation of unit and operation composes. 

 --------
 同态的复合：底层集合等价映射的复合；单位和运算的保持性质也会复合。
*)
Program Definition grp_hom_compose {G H K : GrpObject}
        (f : GrpHom H K) (g : GrpHom G H) : GrpHom G K := {|
  grp_map := setoid_morphism_compose (grp_map f) (grp_map g)
|}.
Next Obligation.
  intros G H K f g; simpl.
  unfold Basics.compose.
  rewrite (grp_map_unit g).
  apply (grp_map_unit f).
Qed.
Next Obligation.
  intros G H K f g a b; simpl.
  unfold Basics.compose.
  rewrite (grp_map_mul g).
  apply (grp_map_mul f).
Qed.

Lemma grp_hom_compose_respects {G H K : GrpObject} :
  Proper (equiv ==> equiv ==> equiv) (@grp_hom_compose G H K).
Proof.
  intros f f' Hf g g' Hg a; simpl.
  unfold Basics.compose.
  rewrite (Hg a).
  apply Hf.
Qed.

(*
 The category of groups.

 objects: groups over setoids
 arrows: unit- and operation-preserving setoid maps
 identity: the identity setoid map
 composition: composition of setoid maps 

 --------
 群的范畴。

 对象：在集合子上面的群
 箭头：保持单位元和运算的集合子映射
 恒等：恒等集合子映射
 组合：集合子映射的组合
*)
(*
 The universes are pinned by hand, exactly as Instance/CMon.v pins [CMon]
 and for the same reason.  [GrpObject]'s sort is
 [Type@{max(Set+1,s,o+1,p+1)}] once [grp_prop] is a field -- the [Set+1] is
 the sort of [Prop] and enters through [PropEquiv] -- and left to itself the
 elaborator will not identify the record's own sort variable [s] with the
 category's object universe, so [Grp] acquires a third, redundant universe
 and every `Grp@{u o}` annotation in the tree is refused for arity.  Naming
 [Category@{u p p}] and every field's instance keeps the arity at two,
 exactly as before the field landed.  An earlier revision of the header said
 "nothing here is annotated, so [Grp] is universe-polymorphic exactly as
 [CMon] is"; that is still true of the SHAPE, but both are now pinned rather
 than inferred.  Measured baseline, before the field:
 [Grp@{u u0} : Category@{u u0 u0}] with [u0 < u]; after, [Grp@{u p} :
 Category@{u p p}] with the one new constraint [Set < u], which the baseline
 already implied through [u0 < u] for any [u0] at or above [Set]. 

 --------
 这些宇宙是手动固定的，正如 Instance/CMon.v 固定 [CMon] 一样，并且原因相同。[GrpObject] 的类型是 [Type@{max(Set+1,s,o+1,p+1)}]，一旦 [grp_prop] 是一个字段——[Set+1] 是 [Prop] 的类型，并通过 [PropEquiv] 进入——如果让它自生自灭，展开器不会将记录自身的类型变量 [s] 与类别的对象宇宙识别，所以 [Grp] 会获得第三个、多余的宇宙，并且树中的每个 `Grp@{u o}` 注解因元数不符而被拒。命名 [Category@{u p p}] 及每个字段的实例可以保持元数为二，完全像字段落地之前一样。标题的早期版本写道“这里没有注解，因此 [Grp] 是宇宙多态的，正如 [CMon] 一样”；SHAPE 仍然如此，但现在两者都是固定的，而不是推断的。在现场之前测量的基线：[Grp@{u u0} : Category@{u u0 u0}] 与 [u0 < u]；之后，[Grp@{u p} : Category@{u p p}] 带有一个新的约束 [Set < u]，该基线通过 [u0 < u] 已经暗示了对于任何在 [Set] 或以上的 [u0]。
*)
Program Definition Grp@{u p} : Category@{u p p} := {|
  obj     := GrpObject@{p p p};
  hom     := GrpHom@{p};
  homset  := @GrpHom_Setoid@{p};
  id      := @grp_hom_id@{p};
  compose := @grp_hom_compose@{u p};

  compose_respects := @grp_hom_compose_respects@{u p}
|}.
Next Obligation.
  intros x y f a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y f a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y z w f g h a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y z w f g h a; simpl.
  reflexivity.
Qed.

(*
 G2: [Grp] is therefore locally propositional -- its hom-setoid IS
 [GrpHom_Setoid].  This is what lets the functor-of-points constructions of
 Structure/Group/Representable.v, which since the PR "algebraic carriers are
 sets" (2026-09-17) ask their ambient category for a [Prop] equality on
 homs, be applied at [Grp] itself with no manual hypothesis. 

 --------
 G2：因此 [Grp] 在局部上是命题的——它的同态集合（hom-setoid）是 [GrpHom_Setoid]。这正是允许 Structure/Group/Representable.v 的点函子构造生效的原因，自从 PR “代数载体是集合”（2026-09-17）之后，它们在同态上要求一个 [Prop] 等式，可以直接在 [Grp] 本身上应用，而无需手动假设。
*)
#[export] Instance Grp_LocallyPropositional : LocallyPropositional Grp.
Proof.
  constructor.
  intros G H.
  exact (@GrpHom_PropEquiv G H).
Defined.

(* The forgetful functor to [Sets], dropping the group structure. / 将群结构丢弃的到 [Sets] 的忘记函子。 *)
Program Definition Grp_Forget : Grp ⟶ Sets := {|
  fobj := fun G => grp_setoid G;
  fmap := fun _ _ f => grp_map f
|}.
Next Obligation.
  intros G H f g Hfg a.
  exact (Hfg a).
Qed.
Next Obligation.
  intros G a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros G H K f g a; simpl.
  reflexivity.
Qed.

(*
 [Grp_Forget] is faithful by construction, since equivalence of
 homomorphisms in [Grp] IS equivalence of the underlying setoid maps. 

 --------
 [Grp_Forget] 通过构造是忠实的，因为在 [Grp] 中同态的等价就是底层集合范畴映射的等价。
*)
#[export] Program Instance Grp_Forget_Faithful : Faithful Grp_Forget.
Next Obligation.
  intros G H f g Hfg a.
  exact (Hfg a).
Qed.

(* * ** The zero object: the trivial group / * ** 零对象：平凡群 *)

(*
 The one-element group on [poly_unit]: unit, operation and inversion are
 all the point, and every law holds by computation.

 THE UNIVERSES ARE WRITTEN OUT, and that is a correction.  Before #450 the
 eight constants of this section carried no binders, and minimization put
 [unit_setoid]'s relation universe at the literal [Set]: [About] under
 [Set Printing Universes] read [Grp_trivial@{u} : GrpObject@{u u Set}],
 [Grp_zero_hom@{u} : ∀ G : GrpObject@{Set Set Set}, …] and
 [Grp_Zero@{u} : ZeroObject@{u Set} Grp@{u Set}], so the zero object of
 [Grp] existed only at [Set] carriers.  The headers of
 Instance/Grp/Quotient/Colimit.v, Instance/Grp/Pushout.v,
 Instance/Grp/EckmannHilton.v, Instance/Grp/Completion.v,
 Instance/Grp/Abelianize.v, Instance/Rg.v and Instance/Top/Pushout.v,
 and the probes Test/ProbePushoutGrpTop.v and Test/ProbeGrpQuotient.v,
 recorded that pin (each now carries a correction), and the
 constructions of Instance/Grp/Colimit.v, whose carriers sit strictly
 above [Set], could not use it.  With the binders below the readbacks
 are [Grp_trivial@{p} : GrpObject@{p p p}] and
 [Grp_Zero@{u p} : ZeroObject@{u p} Grp@{u p}], whose constraint blocks
 are [Grp@{u p}]'s own ([Set < u], [p < u] and stdlib bounds on [p])
 plus the bound [p <= Logic_lemmas.equality.u0] that [unit_setoid]
 brings; the instance [iso_id@{u p p u}] reuses [Grp]'s object universe
 for the one extra level [iso_id] asks for.  The source bodies are
 unchanged apart from those annotations; the elaborated terms are not
 quite: [Print] under [Set Printing All], before and after #450, shows
 [Grp_trivial]'s reflexivity witnesses as [eq_Reflexive] before and as
 [Equivalence_Reflexive (setoid_equiv unit_setoid)] after. 

 --------
 [poly_unit] 上的单元素群：单位元、运算和逆元都是该点，并且每条规律都通过计算成立。宇宙已经写出，这是一个修正。在 #450 之前，本节的八个常数没有绑定器，并且最小化将 [unit_setoid] 的关系宇宙放在字面上的 [Set] : [About] 下 [Set Printing Universes] 阅读 [Grp_trivial@{u} : GrpObject@{u u Set}]，[Grp_zero_hom@{u} : ∀ G : GrpObject@{Set Set Set}, …] 和 [Grp_Zero@{u} : ZeroObject@{u Set} Grp@{u Set}]，因此 [Grp] 的零对象仅存在于 [Set] 承载体上。Instance/Grp/Quotient/Colimit.v、Instance/Grp/Pushout.v、Instance/Grp/EckmannHilton.v、Instance/Grp/Completion.v、Instance/Grp/Abelianize.v、Instance/Rg.v 和 Instance/Top/Pushout.v 的头文件，以及 Test/ProbePushoutGrpTop.v 和 Test/ProbeGrpQuotient.v 的探针，都记录了 pin（现在每个都带有修正），而 Instance/Grp/Colimit.v 的构造，其承载体严格位于 [Set] 之上，则无法使用它。在下面的绑定器中，回读是 [Grp_trivial@{p} : GrpObject@{p p p}] 和 [Grp_Zero@{u p} : ZeroObject@{u p} Grp@{u p}]，其约束块是 [Grp@{u p}] 自身的（[Set < u]、[p < u] 和 [p] 的标准库边界）加上 [unit_setoid] 带来的边界 [p <= Logic_lemmas.equality.u0]；实例 [iso_id@{u p p u}] 对 [Grp] 的对象宇宙进行了重用，以满足 [iso_id] 要求的额外一级。源主体除了这些注释没有变化；展开的项则不完全相同：[Print] 在 [Set Printing All] 下，在 #450 之前和之后，显示 [Grp_trivial] 的自反性证人，在之前是 [eq_Reflexive]，之后是 [Equivalence_Reflexive (setoid_equiv unit_setoid)]。
*)
Definition Grp_trivial@{p} : GrpObject@{p p p}.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := poly_unit@{p}; is_setoid := unit_setoid@{p p} |};
    grp_unit := ttt;
    grp_mul := fun _ _ => ttt;
    grp_inv := fun _ => ttt;
    grp_prop := unit_PropEquiv@{p p}
  |}.
  - intros x y Hxy u v Huv.
    reflexivity.
  - intros a b c.
    reflexivity.
  - intros a.
    destruct a.
    reflexivity.
  - intros a.
    reflexivity.
Defined.

(*
 The unique homomorphism into the trivial group: everything to the
 point. 

 --------
 到平凡群的唯一同态：把一切映射到单位元。
*)
Definition Grp_one@{u p} (G : GrpObject@{p p p}) :
  G ~{Grp@{u p}}~> Grp_trivial@{p}.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom G Grp_trivial {| morphism := fun _ => ttt |} _ _).
  - intros a b Hab.
    reflexivity.
  - reflexivity.
  - intros a b.
    reflexivity.
Defined.

(* Uniqueness into the trivial group: both images live in [poly_unit]. / 唯一性映入平凡群：两个像都位于 [poly_unit] 中。 *)
Lemma Grp_one_unique@{u p} (G : GrpObject@{p p p})
  (f g : G ~{Grp@{u p}}~> Grp_trivial@{p}) : f ≈ g.
Proof.
  intro a.
  destruct (grp_map f a), (grp_map g a).
  reflexivity.
Qed.

Definition Grp_Terminal@{u p} : @Terminal Grp@{u p} :=
  @Build_Terminal Grp@{u p} Grp_trivial@{p} Grp_one@{u p} Grp_one_unique@{u p}.

(* The unique homomorphism out of the trivial group: the point goes to the unit -- the only unit-preserving choice. / 从平凡群出的唯一同态：点映射到单位——唯一保持单位的选择。 *)
Definition Grp_zero_hom@{u p} (G : GrpObject@{p p p}) :
  Grp_trivial@{p} ~{Grp@{u p}}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom Grp_trivial G {| morphism := fun _ => grp_unit G |} _ _).
  - intros a b Hab.
    reflexivity.
  - reflexivity.
  - intros a b.
    symmetry.
    apply grp_mul_unit_l.
Defined.

(*
 Uniqueness out of the trivial group: the point IS the unit, and any
 homomorphism sends units to units ([grp_map_unit]).  Note the contrast
 with [Sets], where the initial object is the EMPTY setoid: there is no
 empty group, and this is what makes the trivial group a zero object. 

 --------
 从平凡群中的唯一性：该点就是单位元素，并且任何同态都将单位元素映射到单位元素（[grp_map_unit]）。请注意与[Sets]的对比，在那里初始对象是空集合：不存在空群，这正是使平凡群成为零对象的原因。
*)
Lemma Grp_zero_hom_unique@{u p} (G : GrpObject@{p p p})
  (f g : Grp_trivial@{p} ~{Grp@{u p}}~> G) : f ≈ g.
Proof.
  intro a.
  destruct a.
  transitivity (grp_unit G).
  - exact (grp_map_unit f).
  - symmetry.
    exact (grp_map_unit g).
Qed.

Definition Grp_Initial@{u p} : @Initial Grp@{u p} :=
  @Build_Terminal (Grp@{u p}^op) Grp_trivial@{p} Grp_zero_hom@{u p}
    Grp_zero_hom_unique@{u p}.

(*
 The trivial group is a zero object.  The same record [Grp_trivial]
 carries both the terminal and the initial structure, so the coincidence
 isomorphism of Structure/ZeroObject.v is the identity. 

 --------
 平凡群是一个零对象。相同的记录 [Grp_trivial] 同时具有终对象和始对象结构，因此 Structure/ZeroObject.v 中的同构恰好是恒等映射。
*)
#[export] Instance Grp_Zero@{u p} : ZeroObject Grp@{u p} :=
  @Build_ZeroObject Grp@{u p} Grp_Terminal@{u p} Grp_Initial@{u p}
    iso_id@{u p p u}.

(** ** Binary direct products / ** 二元直积 *)

(* The direct product G × H: the product setoid with componentwise unit, operation and inversion. / 直积 G × H：具有分量单位、运算和逆运算的乘积集合。 *)
Definition Grp_product (G H : GrpObject) : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := (carrier G * carrier H)%type
                   ; is_setoid := @prod_setoid _ _
                       (is_setoid (grp_setoid G))
                       (is_setoid (grp_setoid H)) |};
    grp_unit := (grp_unit G, grp_unit H);
    grp_mul := fun p q =>
      (grp_mul G (fst p) (fst q), grp_mul H (snd p) (snd q));
    grp_inv := fun p => (grp_inv G (fst p), grp_inv H (snd p));
    grp_prop := prod_PropEquiv (grp_prop G) (grp_prop H)
  |}.
  - intros p p' Hp q q' Hq.
    destruct Hp as [Hp1 Hp2], Hq as [Hq1 Hq2].
    split; simpl.
    + now rewrite Hp1, Hq1.
    + now rewrite Hp2, Hq2.
  - intros a b c.
    split; simpl; apply grp_mul_assoc.
  - intros a.
    split; simpl; apply grp_mul_unit_l.
  - intros a.
    split; simpl; apply grp_mul_inv_l.
Defined.

(* Left projection [fst]: a homomorphism on the nose. / 左投影 [fst]：一个严格同态。 *)
Definition Grp_exl {G H : GrpObject} : Grp_product G H ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_product G H) G {| morphism := fun p => fst p |} _ _).
  - intros p q Hpq.
    exact (fst Hpq).
  - reflexivity.
  - intros p q.
    reflexivity.
Defined.

(* Right projection [snd]. / 右投影 [snd] 。 *)
Definition Grp_exr {G H : GrpObject} : Grp_product G H ~{Grp}~> H.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_product G H) H {| morphism := fun p => snd p |} _ _).
  - intros p q Hpq.
    exact (snd Hpq).
  - reflexivity.
  - intros p q.
    reflexivity.
Defined.

(* The mediating morphism a ↦ (f a, g a): componentwise a homomorphism. / 中介态射 a ↦ (f a, g a)：逐分量同态。 *)
Definition Grp_fork {K G H : GrpObject}
  (f : K ~{Grp}~> G) (g : K ~{Grp}~> H) : K ~{Grp}~> Grp_product G H.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom K (Grp_product G H)
       {| morphism := fun a => (grp_map f a, grp_map g a) |} _ _).
  - intros a b Hab.
    split; simpl; now rewrite Hab.
  - split; simpl.
    + apply (grp_map_unit f).
    + apply (grp_map_unit g).
  - intros a b.
    split; simpl.
    + apply (grp_map_mul f).
    + apply (grp_map_mul g).
Defined.

(*
 The universal property holds because equivalence of pairs in the
 product setoid IS componentwise equivalence, so both halves of
 [ump_products] are projections of that. 

 --------
 这个普遍性性质成立，因为积集合等价类中的对的等价性是按分量的等价性，因此 [ump_products] 的两半都是它的投影。
*)
#[export] Program Instance Grp_Cartesian : @Cartesian Grp := {
  product_obj := Grp_product;
  fork := @Grp_fork;
  exl := @Grp_exl;
  exr := @Grp_exr
}.
Next Obligation.
  intros K G H f f' Hf g g' Hg a.
  split; simpl.
  - exact (Hf a).
  - exact (Hg a).
Qed.
Next Obligation.
  intros K G H f g h.
  split.
  - intro Hh.
    split; intro a.
    + exact (fst (Hh a)).
    + exact (snd (Hh a)).
  - intros [H1 H2] a.
    split; simpl.
    + exact (H1 a).
    + exact (H2 a).
Qed.

(* * ** Monomorphisms are exactly the injections / * ** 单射正好是注入映射 *)

(*
 The kernel of f, as a group: the sub-setoid of elements sent to the
 unit, with the operations inherited from the source.  Closure is where
 the derived facts pay off -- the product of two kernel elements lands
 in the unit by [grp_map_mul] and [grp_mul_unit_l], the inverse by
 [grp_map_inv] and [grp_inv_unit]. 

 --------
 f 的核，作为一个群：被映射到单位元的元素的子集合，运算从源继承。封闭性体现在由此推导出的事实——两个核元素的乘积根据 [grp_map_mul] 和 [grp_mul_unit_l] 落在单位元上，逆元根据 [grp_map_inv] 和 [grp_inv_unit] 得到。
*)
Definition grp_kernel_carrier {G H : GrpObject} (f : G ~{Grp}~> H) : Type :=
  { a : carrier G & grp_map f a ≈ grp_unit H }.

(*
 Two kernel elements are equivalent when their underlying elements are;
 the membership witness is ignored, so no proof irrelevance is needed. 

 --------
 当两个核元素的底层元素相同时，它们是等价的；成员资格证明被忽略，因此不需要证明无关性。
*)
Program Definition grp_kernel_setoid {G H : GrpObject} (f : G ~{Grp}~> H) :
  Setoid (grp_kernel_carrier f) := {|
  equiv := fun p q => projT1 p ≈ projT1 q
|}.
Next Obligation.
  intros G H f.
  constructor.
  - intro p.
    reflexivity.
  - intros p q Hpq.
    now symmetry.
  - intros p q r Hpq Hqr.
    now transitivity (projT1 q).
Qed.

Definition Grp_kernel {G H : GrpObject} (f : G ~{Grp}~> H) : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := grp_kernel_carrier f
                   ; is_setoid := grp_kernel_setoid f |};
    grp_unit := existT _ (grp_unit G) (grp_map_unit f);
    grp_mul := fun p q =>
      existT _ (grp_mul G (projT1 p) (projT1 q)) _;
    grp_inv := fun p => existT _ (grp_inv G (projT1 p)) _
  |}.
  - (* the product of two kernel elements is a kernel element / 两个核元素的乘积是一个核元素 *)
    rewrite grp_map_mul, (projT2 p), (projT2 q).
    apply grp_mul_unit_l.
  - (* the inverse of a kernel element is a kernel element / 一个核元素的逆元是一个核元素 *)
    rewrite grp_map_inv, (projT2 p).
    apply grp_inv_unit.
  - intros p p' Hp q q' Hq.
    simpl in *.
    now rewrite Hp, Hq.
  - intros a b c.
    simpl.
    apply grp_mul_assoc.
  - intros a.
    simpl.
    apply grp_mul_unit_l.
  - intros a.
    simpl.
    apply grp_mul_inv_l.
  - (* The kernel's `≈` compares only the first projection, so the membership witness -- itself a [Type] -- is never inspected and [sigma_first_PropEquiv] applies. It has to be applied in the TACTIC spelling: the term form is refused, since Coq will not see through the [projT1]/[`1] difference in the ascribed type. / 内核的 `≈` 只比较第一个投影，因此成员见证本身是一个 [Type]，永远不会被检查，并且 [sigma_first_PropEquiv] 会适用。它必须以 TACTIC 的拼写方式应用：术语形式被拒绝，因为 Coq 将无法看穿 [projT1] / [`1] 在指定类型上的差异。 *)
    unshelve refine (sigma_first_PropEquiv _ _ _ (grp_prop G)).
    + intros p q Hpq; exact Hpq.
    + intros p q Hpq; exact Hpq.
Defined.

(* The two probe maps out of the kernel: the inclusion ... / 两个探针从内核映射出：包含 ... *)
Definition Grp_kernel_incl {G H : GrpObject} (f : G ~{Grp}~> H) :
  Grp_kernel f ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_kernel f) G {| morphism := fun p => projT1 p |} _ _).
  - intros p q Hpq.
    exact Hpq.
  - reflexivity.
  - intros p q.
    reflexivity.
Defined.

(* ... and the constant map at the unit. / ... 以及单位处的恒等映射。 *)
Definition Grp_kernel_triv {G H : GrpObject} (f : G ~{Grp}~> H) :
  Grp_kernel f ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_kernel f) G
       {| morphism := fun _ => grp_unit G |} _ _).
  - intros p q Hpq.
    reflexivity.
  - reflexivity.
  - intros p q.
    symmetry.
    apply grp_mul_unit_l.
Defined.

(*
 f cannot tell the two probe maps apart: it sends every kernel element
 to the unit by definition of the kernel, and the unit to the unit by
 [grp_map_unit]. 

 --------
 f 无法分辨两个探针映射：根据核的定义，它将每个核元素发送到单位元，并将单位元通过 [grp_map_unit] 发送到单位元。
*)
Lemma Grp_kernel_probe {G H : GrpObject} (f : G ~{Grp}~> H) :
  f ∘ Grp_kernel_incl f ≈ f ∘ Grp_kernel_triv f.
Proof.
  intro p.
  simpl.
  unfold Basics.compose.
  transitivity (grp_unit H).
  - exact (projT2 p).
  - symmetry.
    apply (grp_map_unit f).
Qed.

(*
 In [Grp] the monomorphisms are exactly the injections (up to `≈`),
 mirroring [injectivity_is_monic] at Instance/Sets.v.  The forward
 direction is soft.  The reverse direction probes f with the kernel:
 monicity collapses the inclusion to the constant map, so the kernel is
 trivial, and f a ≈ f b then puts a * b⁻¹ in the kernel. 

 --------
 在 [Grp] 中，单态正是注入（在 `≈` 意义下），类似于 Instance/Sets.v 中的 [injectivity_is_monic]。正向是直接的。反向通过使用核来探测 f：单态性将包含映射压缩为常值映射，因此核是平凡的，而 f a ≈ f b 则将 a * b⁻¹ 放入核中。
*)
Theorem Grp_injectivity_is_monic {G H : GrpObject} (f : G ~{Grp}~> H) :
  (∀ a b : carrier G, grp_map f a ≈ grp_map f b → a ≈ b) ↔ Monic f.
Proof.
  split.
  - intro Hinj.
    constructor.
    intros K g1 g2 Hg a.
    apply Hinj.
    exact (Hg a).
  - intros [Hmonic] a b Hab.
    assert (Hker : grp_map f (grp_mul G a (grp_inv G b)) ≈ grp_unit H).
    { rewrite grp_map_mul, grp_map_inv, Hab.
      apply grp_mul_inv_r. }
    pose proof (Hmonic (Grp_kernel f) (Grp_kernel_incl f) (Grp_kernel_triv f)
                  (Grp_kernel_probe f)) as Htriv.
    specialize (Htriv (existT _ (grp_mul G a (grp_inv G b)) Hker)).
    simpl in Htriv.
    apply (grp_cancel_r G (grp_inv G b)).
    rewrite grp_mul_inv_r.
    exact Htriv.
Qed.

(* * ** The opposite-group functor and inversion (Riehl, Example 1.4.4(vi)) / * ** 对立群函子与反转 (Riehl, 示例 1.4.4(vi)) *)

(* G^op: the same setoid with the multiplication reversed. The unit and the inversion are unchanged, since the left laws of G^op are the right laws of G. / G^op：具有反向乘法的相同集合。单位和逆元保持不变，因为 G^op 的左律就是 G 的右律。 *)
Definition Grp_op_obj (G : GrpObject) : GrpObject.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := grp_setoid G;
    grp_prop := grp_prop G;
    grp_unit := grp_unit G;
    grp_mul := fun a b => grp_mul G b a;
    grp_inv := grp_inv G
  |}.
  - intros a a' Ha b b' Hb.
    now rewrite Ha, Hb.
  - intros a b c.
    symmetry.
    apply grp_mul_assoc.
  - intros a.
    apply grp_mul_unit_r.
  - intros a.
    apply grp_mul_inv_r.
Defined.

(*
 On morphisms the functor is the identity: a homomorphism f already
 satisfies f (b * a) ≈ f b * f a, which is the multiplication law read
 in the opposite groups.  This is why (-)^op is COVARIANT on Grp. 

 --------
 在态射上，函子是恒等的：一个同态 f 已经满足 f(b * a) ≈ f b * f a，这就是在对立群中读取的乘法律。这就是为什么 (-)^op 在 Grp 上是协变的。
*)
Definition Grp_op_map {G H : GrpObject} (f : G ~{Grp}~> H) :
  Grp_op_obj G ~{Grp}~> Grp_op_obj H.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_op_obj G) (Grp_op_obj H) (grp_map f) _ _).
  - apply (grp_map_unit f).
  - intros a b.
    apply (grp_map_mul f).
Defined.

Program Definition Grp_Op : Grp ⟶ Grp := {|
  fobj := Grp_op_obj;
  fmap := @Grp_op_map
|}.
Next Obligation.
  intros G H f g Hfg a.
  exact (Hfg a).
Qed.
Next Obligation.
  intros G a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros G H K f g a; simpl.
  reflexivity.
Qed.

(* Inversion as a homomorphism G ~> G^op. It is NOT an endomorphism of G: the multiplication law it satisfies is (a * b)⁻¹ ≈ b⁻¹ * a⁻¹, which is the law of G^op read at the images. / 作为同态的取逆 G ~> G^op。 它不是 G 的自同态：它满足的乘法法则是 (a * b)⁻¹ ≈ b⁻¹ * a⁻¹，这就是在像上读取的 G^op 的法则。 *)
Definition Grp_inv_to (G : GrpObject) : G ~{Grp}~> Grp_op_obj G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom G (Grp_op_obj G) {| morphism := grp_inv G |} _ _).
  - intros a b Hab.
    now rewrite Hab.
  - exact (grp_inv_unit G).
  - intros a b.
    exact (grp_inv_mul G a b).
Defined.

(* The same map read backwards, a homomorphism G^op ~> G. / 相同的映射倒过来读，是一个同态 G^op ~> G。 *)
Definition Grp_inv_from (G : GrpObject) : Grp_op_obj G ~{Grp}~> G.
Proof.
  unshelve notypeclasses refine
    (Build_GrpHom (Grp_op_obj G) G {| morphism := grp_inv G |} _ _).
  - intros a b Hab.
    now rewrite Hab.
  - exact (grp_inv_unit G).
  - intros a b.
    exact (grp_inv_mul G b a).
Defined.

(*
 Naturality in both orientations is [grp_map_inv]: homomorphisms commute
 with inversion. 

 --------
 两种取向下的自然性均为[grp_map_inv]：同态交换
 带有倒置。
*)
Program Definition Grp_inv_Transform : @Id Grp ⟹ Grp_Op := {|
  transform := Grp_inv_to
|}.
Next Obligation.
  intros G H f a; simpl.
  unfold Basics.compose.
  apply grp_map_inv.
Qed.
Next Obligation.
  intros G H f a; simpl.
  unfold Basics.compose.
  symmetry.
  apply grp_map_inv.
Qed.

Program Definition Grp_inv_Transform_inv : Grp_Op ⟹ @Id Grp := {|
  transform := Grp_inv_from
|}.
Next Obligation.
  intros G H f a; simpl.
  unfold Basics.compose.
  apply grp_map_inv.
Qed.
Next Obligation.
  intros G H f a; simpl.
  unfold Basics.compose.
  symmetry.
  apply grp_map_inv.
Qed.

(*
 The identity functor on [Grp] is naturally isomorphic to the
 opposite-group functor, the component at G being inversion.  Both round
 trips are [grp_inv_inv]. 

 --------
 在  [Grp]  上的身份函子自然同构于对偶群函子，其在 G 处的分量是取逆。两次往返都是  [grp_inv_inv] 。
*)
Program Definition Grp_op_Isomorphism :
  @Isomorphism ([Grp, Grp]) (@Id Grp) Grp_Op := {|
  to   := Grp_inv_Transform;
  from := Grp_inv_Transform_inv
|}.
Next Obligation.
  intros G a; simpl.
  unfold Basics.compose.
  apply grp_inv_inv.
Qed.
Next Obligation.
  intros G a; simpl.
  unfold Basics.compose.
  apply grp_inv_inv.
Qed.

(* * ** Reconciliation with the internal [GroupObject] of Structure/Group.v / * ** 与 Structure/Group.v 的内部 [GroupObject] 的和解 *)

(*
 A NOTE ON DUPLICATION, for the reader who greps.  The tree already carries
 a monoidal structure with the same underlying data at Instance/Sets.v,
 the exported instance [Sets_Product_Monoidal].  The definition below is a
 DISTINCT, NON-CONVERTIBLE term (their units agree by reflexivity; their
 tensors do not -- one is a Program-built bifunctor, the other the CC_
 composite), assembled through CC_Monoidal because [GroupObject] needs a
 [CartesianMonoidal], which the tree does not otherwise provide for [Sets].
 It is deliberately a plain Definition, not an instance: registering a
 second [@Monoidal Sets] path would change typeclass resolution elsewhere.
 No comparison isomorphism between the two structures is proved here; a
 consumer needing one should build it or unify the two upstream. 

 --------
 关于复制的说明，供使用 grep 的读者参考。该树已经携带了一个单幺半群结构，其在 Instance/Sets.v 中的数据是相同的，导出的实例为 [Sets_Product_Monoidal]。下面的定义是一个不同的、不可转换的项（它们的单位通过自反性一致；它们的张量则不一致——一个是通过 Program 构建的双范畴，另一个是 CC_ 复合构造），通过 CC_Monoidal 组装，因为 [GroupObject] 需要一个 [CartesianMonoidal]，而树本身并未为 [Sets] 提供。它故意被定义为一个普通的 Definition，而不是实例：注册第二个 [@Monoidal Sets] 路径会改变其他地方的类型类解析。这里未证明两个结构之间的比较同构；需要此类同构的使用者应自己构建它，或在上游统一两者。
*)
Definition Sets_prod_Monoidal : @Monoidal Sets :=
  @CC_Monoidal Sets Sets_Cartesian Sets_Terminal.

Definition Sets_CartesianMonoidal : @CartesianMonoidal Sets :=
  @CC_CartesianMonoidal Sets Sets_Cartesian Sets_Terminal.

Program Definition Grp_unit_map (G : GrpObject) :
  @terminal_obj Sets Sets_Terminal ~{Sets}~> grp_setoid G :=
  {| morphism := fun _ => grp_unit G |}.

Program Definition Grp_mul_map (G : GrpObject) :
  @product_obj Sets Sets_Cartesian (grp_setoid G) (grp_setoid G)
    ~{Sets}~> grp_setoid G :=
  {| morphism := fun p => grp_mul G (fst p) (snd p) |}.
Next Obligation.
  intros G p q Hpq.
  destruct Hpq as [H1 H2].
  simpl in *.
  now rewrite H1, H2.
Qed.

(*
 Every law of [MonoidObject] is the corresponding law of [GrpObject]
 read at a point, because in [Sets] the tensor is the product setoid,
 the unitors are the projections and the associator is reassociation of
 pairs -- all of which compute. 

 --------
 [MonoidObject] 的每一条定律都是在某一点读取时 [GrpObject] 的相应定律，因为在 [Sets] 中，张量是积集，幺元子是投影，结合子是对的重新结合——所有这些都是可计算的。
*)
Definition Grp_MonoidObject (G : GrpObject) :
  @MonoidObject Sets Sets_prod_Monoidal (grp_setoid G).
Proof.
  unshelve notypeclasses refine
    (@Build_MonoidObject Sets Sets_prod_Monoidal (grp_setoid G)
       (Grp_unit_map G) (Grp_mul_map G) _ _ _).
  - intro p; simpl.
    apply grp_mul_unit_l.
  - intro p; simpl.
    apply grp_mul_unit_r.
  - intro p; simpl.
    apply grp_mul_assoc.
Defined.

Program Definition Grp_inverse_map (G : GrpObject) :
  grp_setoid G ~{Sets}~> grp_setoid G := {| morphism := grp_inv G |}.

(*
 A [GrpObject] IS a group object in [Sets]: the inverse laws of
 Structure/Group.v, whose right-hand side is the constant-at-the-unit
 endomorphism mempty ∘ eliminate, evaluate at a point to
 [grp_mul_inv_l] and [grp_mul_inv_r]. 

 --------
 [GrpObject] 是 [Sets] 中的一个群对象：Structure/Group.v 的逆律，其右侧是常数在单位端的自同态 mempty ∘ eliminate，在某一点处求值为 [grp_mul_inv_l] 和 [grp_mul_inv_r]。
*)
Definition Grp_GroupObject (G : GrpObject) :
  @GroupObject Sets Sets_CartesianMonoidal (grp_setoid G).
Proof.
  unshelve notypeclasses refine
    (@Build_GroupObject Sets Sets_CartesianMonoidal (grp_setoid G)
       (Grp_MonoidObject G) (Grp_inverse_map G) _ _).
  - intro a; simpl.
    apply grp_mul_inv_l.
  - intro a; simpl.
    apply grp_mul_inv_r.
Defined.

(*
 And conversely: a group object in [Sets] whose carrier setoid is
 propositional is a [GrpObject].  The record is destructured rather than
 projected because Structure/Group.v reserves the token [inverse] for its
 notation, so the field cannot be named in a term.

 An earlier revision of this comment said "at full strength", and the
 construction then took only [X] and [GO].  Since the PR "algebraic carriers
 are sets" (2026-09-17) it takes a third argument [PX : PropEquiv (is_setoid
 X)].  That is a RECORDED STRENGTH CHANGE: a group object in [Sets] over a
 proof-relevant setoid is no longer translated.  Nothing in tree is lost --
 the only partner, [Grp_GroupObject], goes the other way and the round-trip
 [Example]s below take [PX] as a parameter -- and the direction that matters
 for the internal/concrete dictionary, [Grp_GroupObject], is unconditional
 because a [GrpObject] carries [grp_prop] already. 

 --------
 反之：在 [Sets] 中，其载体集合是命题的群对象是一个 [GrpObject]。该记录是被解构而不是投影，因为 Structure/Group.v 为其符号保留了 [inverse]，所以该字段不能在项中命名。这条评论的早期版本写道“全强度”，那时这个构造只接受 [X] 和 [GO]。由于 PR “代数载体是集合”（2026-09-17），它现在接受第三个参数 [PX : PropEquiv (is_setoid X)]。这是一个记录的强度变化：在 [Sets] 上的一个群对象（位于证明相关的集合上）不再被翻译。树中的内容没有丢失——唯一的对应对象 [Grp_GroupObject] 是相反方向的，并且以下 [Example] 的往返操作以 [PX] 作为参数——而对内部/具体字典 [Grp_GroupObject] 有关的方向是无条件的，因为一个 [GrpObject] 已经携带了 [grp_prop]。
*)
Definition GroupObject_GrpObject (X : Sets)
  (PX : PropEquiv (is_setoid X))
  (GO : @GroupObject Sets Sets_CartesianMonoidal X) : GrpObject.
Proof.
  destruct GO as [mon inv Hleft Hright].
  destruct mon as [me ma Hunitl Hunitr Hassoc].
  unshelve notypeclasses refine {|
    grp_setoid := X;
    grp_unit := me ttt;
    grp_mul := fun a b => ma (a, b);
    grp_inv := fun a => inv a;
    grp_prop := PX
  |}.
  - intros a a' Ha b b' Hb.
    apply proper_morphism.
    split; assumption.
  - intros a b c.
    exact (Hassoc ((a, b), c)).
  - intros a.
    exact (Hunitl (ttt, a)).
  - intros a.
    exact (Hleft a).
Defined.

(* The two translations are mutually inverse on the operations, by computation: the round trip changes no data at all. / 这两种翻译在操作上是相互逆的，通过计算：往返转换根本不会改变任何数据。 *)
Example Grp_GroupObject_roundtrip_unit (G : GrpObject) :
  grp_unit (GroupObject_GrpObject (grp_setoid G) (grp_prop G) (Grp_GroupObject G))
    ≈ grp_unit G.
Proof. reflexivity. Qed.

Example Grp_GroupObject_roundtrip_mul (G : GrpObject) (a b : carrier G) :
  grp_mul (GroupObject_GrpObject (grp_setoid G) (grp_prop G) (Grp_GroupObject G)) a b
    ≈ grp_mul G a b.
Proof. reflexivity. Qed.

Example Grp_GroupObject_roundtrip_inv (G : GrpObject) (a : carrier G) :
  grp_inv (GroupObject_GrpObject (grp_setoid G) (grp_prop G) (Grp_GroupObject G)) a
    ≈ grp_inv G a.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** A nontrivial witness: Z/2, and non-vacuity of the machinery / * ** 一个非平凡的例子：Z/2，以及该机制的非空性 *)

(*
 Everything above is proved for all groups but, before this section, the
 file constructed only the one-element group -- so nothing in the tree
 DEMONSTRATED the biconditional, the products, or the opposite functor on a
 non-degenerate object.  Z/2 on bool closes that gap (the construction and
 the non-vacuity corollaries below were supplied by the audit of the
 previous commit).  The second reconciliation round trip is recorded here
 as well. 

 --------
 以上所有内容都已对所有群体进行了证明，但在本节之前，该文件仅构造了单元素群——因此树中的内容并没有在非退化对象上演示双条件关系、乘积或对偶函子。布尔值上的 Z/2 填补了这一空白（下文构造及非空推论由对上一次提交的审核提供）。第二次调和往返也在此记录。
*)

(*
 THE UNIVERSES ARE WRITTEN OUT, and that is a correction.  Before #450
 [bool_setoid] and [Z2] carried no binders, and minimization put the
 relation universe at the literal [Set]: [About] read
 [bool_setoid@{u} : Setoid@{u Set} bool] and [Z2@{u} : GrpObject@{u Set
 Set}], so [Z2] inhabited [Grp] only at [Set] carriers, and
 Instance/Grp/Galois.v, Instance/Grp/Epi.v and Test/ProbeGalois381.v
 recorded that pin.  With the binders the readbacks are
 [bool_setoid@{u} : Setoid@{u u} bool] and [Z2@{p} : GrpObject@{p p p}],
 each with the single bound [_ <= Logic_lemmas.equality.u0].  The
 equivalence field is named ([eq_equivalence@{u u}], the proof
 [eq_Setoid] uses) because under this file's [idtac] obligation tactic
 the annotated [Program Definition] otherwise leaves it as an open
 obligation.  The carrier, relation and operations are unchanged; the
 equivalence proof is Lib/Setoid.v's [eq_equivalence] now, where
 [Print] under [Set Printing All] read the stdlib's
 [CRelationClasses.eq_equivalence] before #450. 

 --------
 宇宙被列出，这是一个更正。在 #450 之前，[bool_setoid] 和 [Z2] 没有携带绑定器，并且最小化将关系宇宙放在文字 [Set] : [About] 读取 [bool_setoid@{u} : Setoid@{u Set} bool] 和 [Z2@{u} : GrpObject@{u 集合 集合}]，所以 [Z2] 仅在 [Set] 载体上居住于 [Grp]，并且 Instance/Grp/Galois.v、Instance/Grp/Epi.v 和 Test/ProbeGalois381.v 记录了该引脚。使用绑定器后，回读为 [bool_setoid@{u} : Setoid@{u u} bool] 和 [Z2@{p} : GrpObject@{p p p}]，每个都带有单一绑定 [_ <= Logic_lemmas.equality.u0]。等价字段命名为 ( [eq_equivalence@{u u}]，证明 [eq_Setoid] 使用) 因为在该文件的 [idtac] 义务策略下，注释的 [Program Definition] 否则会将其保留为未解决的义务。载体、关系和操作保持不变；等价性证明现在是 Lib/Setoid.v 的 [eq_equivalence]，其中 [Print] 在 [Set Printing All] 下读作 stdlib 的 [CRelationClasses.eq_equivalence]（在 #450 之前）。
*)
Program Definition bool_setoid@{u} : Setoid@{u u} bool :=
  {| equiv := @eq bool; setoid_equiv := eq_equivalence@{u u} |}.

Definition Z2@{p} : GrpObject@{p p p}.
Proof.
  unshelve notypeclasses refine {|
    grp_setoid := {| carrier := bool ; is_setoid := bool_setoid@{p} |};
    grp_unit := false;
    grp_mul  := xorb;
    grp_inv  := fun b => b;
    (*
 [bool_setoid]'s `≈` is [@eq bool], already a [Prop]; instance
 resolution sees through the hand [Program Definition] to
 [eq_PropEquiv]. 

 --------
 [bool_setoid] 的 `≈` 是 [@eq bool]，已经是一个 [Prop]；实例解析透过手 [Program Definition] 看向 [eq_PropEquiv]。
*)
    grp_prop := eq_PropEquiv bool
  |}.
  - intros x y Hxy u v Huv; simpl in *; subst; reflexivity.
  - intros a b c; simpl; now destruct a, b, c.
  - intros a; simpl; now destruct a.
  - intros a; simpl; now destruct a.
Defined.

(* Z2 is genuinely nontrivial. / Z2 真的是非平凡的。 *)
Lemma Z2_nontrivial : (@equiv _ (grp_setoid Z2) true false) -> False.
Proof. simpl. discriminate. Qed.

(* The unique hom Z2 ~> 1 is NOT injective ... / 唯一的同态 Z2 ~> 1 不是单射... *)
Lemma Z2_to_one_not_injective :
  (forall a b : carrier Z2, grp_map (Grp_one Z2) a ≈ grp_map (Grp_one Z2) b -> a ≈ b) -> False.
Proof.
  intro Hinj.
  apply Z2_nontrivial.
  apply Hinj.
  simpl. reflexivity.
Qed.

(* ... hence NOT monic. So `Monic` in Grp is a non-vacuous predicate. / ... 因此不是首一的。所以 Grp 中的 `Monic` 是一个非空谓词。 *)
Theorem Monic_in_Grp_is_not_vacuous : Monic (Grp_one Z2) -> False.
Proof.
  intro Hm.
  apply Z2_to_one_not_injective.
  destruct (Grp_injectivity_is_monic (Grp_one Z2)) as [_ Hback].
  exact (Hback Hm).
Qed.

(* And some map IS monic: the identity on Z2. / 并且某些映射是单一的：在 Z2 上的恒等映射。 *)
Theorem Monic_in_Grp_is_inhabited : @Monic Grp Z2 Z2 (@id Grp Z2).
Proof. apply (@id_monic Grp Z2). Qed.

(* The kernel probe is non-degenerate: the kernel of Z2 ~> 1 contains a non-unit element. / 核探针是非退化的：Z2 ~> 1 的核包含一个非单位元。 *)
Definition ker_true : carrier (Grp_kernel (Grp_one Z2)).
Proof. exists true. simpl. reflexivity. Defined.

Lemma Grp_kernel_nondegenerate :
  (@equiv _ (grp_setoid (Grp_kernel (Grp_one Z2)))
        ker_true (grp_unit (Grp_kernel (Grp_one Z2)))) -> False.
Proof. simpl. discriminate. Qed.

(* ===================================================================== *)
(* E: the OTHER round trip, GroupObject -> GrpObject -> GroupObject. / E：另一次往返，GroupObject -> GrpObject -> GroupObject。 *)
(* Is it provable? (It is NOT stated in Instance/Grp.v.) / 这是可证明的吗？（在 Instance/Grp.v 中没有说明。） *)
(* ===================================================================== *)

(* Each of the three takes the carrier's [PropEquiv] as a parameter, since [GroupObject_GrpObject] does; see its comment for the strength change. / 三者中的每一个都将承载者的 [PropEquiv] 作为参数，因为 [GroupObject_GrpObject] 也这样做；有关强度变化，请参阅其注释。 *)
Example rt_back_unit (X : Sets) (PX : PropEquiv (is_setoid X))
  (GO : @GroupObject Sets Sets_CartesianMonoidal X) :
  @mempty Sets Sets_prod_Monoidal X
     (Grp_MonoidObject (GroupObject_GrpObject X PX GO))
  ≈ @mempty Sets Sets_prod_Monoidal X GO.
Proof. intro u; destruct u; destruct GO as [mon inv Hl Hr]; destruct mon; reflexivity. Qed.

Example rt_back_mul (X : Sets) (PX : PropEquiv (is_setoid X))
  (GO : @GroupObject Sets Sets_CartesianMonoidal X) :
  @mappend Sets Sets_prod_Monoidal X
     (Grp_MonoidObject (GroupObject_GrpObject X PX GO))
  ≈ @mappend Sets Sets_prod_Monoidal X GO.
Proof. intro p; destruct p; destruct GO as [mon inv Hl Hr]; destruct mon; reflexivity. Qed.

Section RTInv.
#[local] Existing Instance Sets_CartesianMonoidal.
Context (X : Sets).
Context (PX : PropEquiv (is_setoid X)).
Context `{GO : @GroupObject Sets Sets_CartesianMonoidal X}.
Example rt_back_inv : Grp_inverse_map (GroupObject_GrpObject X PX GO) ≈ inverse[X].
Proof. intro a; destruct GO as [mon inv Hl Hr]; destruct mon; reflexivity. Qed.
End RTInv.

(* ===================================================================== *)
(* Is Grp_Op an involution on the nose? / Grp_Op 是不是严格的自反运算？ *)
(* ===================================================================== *)

