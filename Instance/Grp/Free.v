Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Free.Groupoid.
Require Import Category.Instance.Sets.

(*
 [Instance/Grp.v] is imported LAST on purpose.  [Construction/Deloop.v]
 also declares a record called [GrpObject] — layered on [MonObject], with
 both unit laws and both inverse laws as fields — and the two names would
 otherwise collide.  With this order, the unqualified [GrpObject],
 [grp_unit], [grp_mul] and [grp_inv] below are always [Instance/Grp.v]'s,
 which is the record [Grp] is the category of and hence the one the
 adjunction must be stated over. 

 --------
 [Instance/Grp.v] 是故意最后导入的。[Construction/Deloop.v] 也声明了一个名为 [GrpObject] 的记录 —— 它是基于 [MonObject] 的分层记录，包含单位律和逆元律作为字段 —— 否则这两个名字会冲突。按照这个顺序，下面未限定的 [GrpObject]、[grp_unit]、[grp_mul] 和 [grp_inv] 始终是 [Instance/Grp.v] 的，它是记录 [Grp] 的范畴，因此也是需要在其上陈述伴随的对象。
*)
Require Import Category.Instance.Grp.

Generalizable All Variables.

#[local] Existing Instance edgeset.

(*
 The global obligation tactic is [cat_simpl], which would run wide proof
 searches on the group obligations below and has already introduced the
 parameters by the time an obligation is opened.  Switched off here, the
 [Instance/Grp.v] idiom, so every obligation starts with an explicit
 [intros]. 

 --------
 全球义务策略是 [cat_simpl]，它将在下面的群体义务上运行广泛的证明搜索，并且在义务被开启时已经引入了参数。在此处关闭，采用 [Instance/Grp.v] 习语，因此每个义务都以明确的 [intros] 开始。
*)
#[local] Obligation Tactic := idtac.

(*
   * * The free group on a set, and the free-forgetful adjunction

   nLab:      https://ncatlab.org/nlab/show/free+group
   nLab:      https://ncatlab.org/nlab/show/free+groupoid
   nLab:      https://ncatlab.org/nlab/show/free+construction
   Wikipedia: https://en.wikipedia.org/wiki/Free_group
   Wikipedia: https://en.wikipedia.org/wiki/Nielsen%E2%80%93Schreier_theorem
   Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
   GTM 5, §II.7, printed p. 51 (Exercise 3, whose closing clause is
   the free group as the one-object free groupoid)
   Book: Riehl, Category Theory in Context, §4.2, printed p. 139 (free ⊣
   forgetful; the unit is the insertion of generators and the counit
   evaluates a word)
   Book: Awodey, Category Theory, §1.7 (the universal mapping property of a
   free structure, worked for monoids) and §9.1 (the adjunction)

   THE POINT OF THE EXERCISE.  A free group on a set S is a group F(S) with
   a map S → |F(S)| through which every map from S into the underlying set
   of a group factors uniquely by a homomorphism.  Nielsen (1921) and
   Schreier (1927) put free groups at the centre of combinatorial group
   theory; the categorical reading — that F is left adjoint to the
   forgetful functor — is the motivating example of an adjunction in
   essentially every textbook, and is the reason “free” is a technical word
   at all.  Mac Lane's §II.7 exercise reaches it the economical way, via
   groupoids: build the free groupoid on a graph, then read the free group
   off the one-node case.  That is what this file does.

   HOW IT IS BUILT.  [Construction/Free/Groupoid.v] supplies the free
   groupoid; this file instantiates it at a quiver with ONE node whose
   edge set is the generating setoid, and reads the endomorphism group of
   that node.  Every group law is then a CATEGORY law by projection —
   associativity is [comp_assoc_sym], the unit law is [id_left], the
   inverse law is [fginv_left] — exactly as [hom_monoid]
   (Construction/Deloop.v) reads a monoid off an endomorphism hom-set, and
   three [eq_refl] Examples below record that the underlying monoid IS
   [hom_monoid] of the free groupoid on all three data fields.  Since the PR
   “algebraic carriers are sets” (2026-09-17) each of those three laws is
   that category law under one [inhabits], because the group's `≈` is the
   hom-equality's propositional truncation; see [fg_equiv] below for why, and
   note that the three [eq_refl] Examples are about the OPERATIONS and are
   unaffected.

   THE FREE GROUP ON A SETOID, NOT ON A TYPE.  [Grp_Forget] lands in
   [Sets], whose objects are setoids, so the left adjoint is a functor
   [Sets ⟶ Grp] and the generators carry their own [≈], which the word
   relation must respect.  This is the one place where the free-monoid
   precedent does not transfer: in [Instance/Coq/Monoid/Free.v] the
   generators are a bare [Type] and [list X] under Leibniz [=] is already
   free, with no quotient at all.  Here the one-node quiver cannot be
   [Construction/Free/Quiver/Presented.v]'s [OneNodeQuiver], which puts
   Leibniz [=] on its edges; [PointQuiver] is built by hand with the
   generating setoid's own equivalence as the edge setoid, and
   respectfulness of the insertion is then not a new obligation but the
   [fedgemap_respects] field of [FreeGroupoidUnit] (since the PR “algebraic
   carriers are sets” it is that field under one [inhabits]).

   TWO RECORDS NAMED [GrpObject].  Construction/Deloop.v's is layered on
   [MonObject] and carries both unit laws and both inverse laws as fields;
   Instance/Grp.v's is flat and carries only the left-handed ones, the
   right-handed laws and respectfulness of inversion being derived.  [Grp]
   is the category of the LATTER, so that is the record this adjunction
   must be stated over, and it is why the import order at the top of this
   file is deliberate.  The only bridge between them when this file was
   written was [Instance/Rep.v]'s [grp_mon], which reads Instance/Grp.v's
   record as a [MonObject] (Instance/Grp/Congruence.v later supplies the
   record-to-record converter [grp_deloop_GrpObject]); it drops the inverse, so it does NOT supply
   [Deloop_IsGroupoid]'s hypothesis (that lemma is stated over Deloop's
   [GrpObject]), and its file in any case sits on top of the module and
   matrix stack, which nothing here needs.  [grp_deloop_monoid] and
   [grp_deloop_IsGroupoid] therefore rebuild the two-line bridge directly
   over Instance/Grp.v's record.  Routing the free GROUP through
   [vertex_group] (Structure/Groupoid.v) would have produced a
   Deloop-flavoured record and so would have landed in the wrong category;
   the group is therefore assembled directly from the word quotient.

   MULTIPLICATION IS COMPOSITION, hence right to left: the product of the
   one-letter words a and b is the word “b then a”.  That is the house
   convention ([hom_monoid]'s [mon_op] is [fun f g => f ∘ g]) and it is
   what lets [fmap_comp] discharge [grp_map_mul] with no massaging;
   [free_group_mul_is_compose] pins it by [eq_refl].

   STRENGTHS, MEASURED.

   - [eq_refl]: the free functor's object part is the word group
   ([FreeGrp_obj]); the universal arrow is the insertion of generators
   ([free_group_arrow_is_insert]); the UNIT is the one-letter word
   ([free_group_unit_is_insert], [free_group_unit_is_generator]);
   multiplication is composition, the group unit is the identity arrow,
   inversion is word reversal, and the underlying monoid is
   [hom_monoid] on all three data fields.
   - [≈] only: the COUNIT.  It is the other transpose, i.e.
   [unique_obj (ump_universal_arrows …)], and [ump_universal_arrows]
   (Theory/Universal/Arrow.v) is [Qed]-opaque, so it does not compute
   and no [eq_refl] is claimed on that side.  What is proved is that it
   agrees with word evaluation up to [≈]
   ([free_group_counit_evaluates]), which is the content;
   Test/ProbeFreeGroupoid.v pins the negative side with a [Fail] probe.
   - The triangle identities are [Theory/Adjunction.v]'s derived
   [counit_fmap_unit] and [fmap_counit_unit] instantiated, and are
   named here because the issue asks for them by name.  They are
   derived and not fields, so instantiating them is a genuine check
   that the adjunction is the intended one, not a restatement.

   NON-VACUITY.  A free group on the empty or a one-element generating set
   is abelian and would demonstrate nothing.  The witness therefore has TWO
   generators and is separated by a functor into the delooping of the
   symmetric group on three letters (Structure/Groupoid.v's [S3_Grp], a
   nonabelian group already in tree):
   [free_group_two_generators_nonabelian] and
   [free_group_two_generators_distinct].  Because the delooping of a group
   is a groupoid, the free-GROUPOID universal property applies directly and
   no bridge between the two [GrpObject] records is needed for the witness.

   THIS IS NOT THE ONLY FREE-GROUP ADJUNCTION THE TREE SHOULD HAVE.  Issue
   #442 (maclane:V.6:construction-free-group) reaches a free-group left
   adjoint over [Grp] by the adjoint-functor-theorem route, with no word
   normal form anywhere; Mac Lane presents both routes deliberately, and
   the two are complementary rather than competing — one exhibits the
   object, the other proves it exists from completeness and a solution set.

   WHAT IS NOT DELIVERED.

   - No reduced-word normal form, hence no decision procedure for the
   word problem, no Nielsen-Schreier theorem, and no proof that
   [fg_insert] is injective for a GENERAL generating setoid.  What is
   proved is that it is injective on the two-letter witness
   ([free_group_two_generators_distinct]), by mapping into S3.  A
   general proof needs a separating family of groups, which in the
   constructive setting is essentially the normal-form theorem again.
   - No statement that [FreeGrp] is faithful, and no characterization of
   its image.
   - No free ABELIAN group, no free monoid over [Sets] (the free monoid
   in tree, [Instance/Coq/Monoid/Free.v], is over [Coq]), and no
   comparison functor between them. 

   --------
   * * 集上的自由群以及自由-遗忘伴随关系

   nLab:       https://ncatlab.org/nlab/show/free+group 
   nLab:       https://ncatlab.org/nlab/show/free+groupoid 
   nLab:       https://ncatlab.org/nlab/show/free+construction 
   维基百科:   https://en.wikipedia.org/wiki/Free_group 
   维基百科:   https://en.wikipedia.org/wiki/Nielsen%E2%80%93Schreier_theorem 
   书籍: 麦克莱恩，《为工作的数学家而写的范畴论》，第2版，GTM 5，第II.7节，印刷页51（练习3，其结尾条款是作为单对象自由群的自由群）
   书籍: Riehl，《上下文中的范畴论》，第4.2节，印刷页139（自由 ⊣ 遗忘；单位是生成元的插入，余单位评估一个字）
   书籍: Awodey，《范畴论》，第1.7节（自由结构的泛映射性质，对单子进行了论证）和第9.1节（伴随关系）练习的要点。给定一个集合 S 的自由群是一个群 F(S)，并带有一个映射 S → |F(S)|，通过该映射，每个从 S 到群的底集合的映射都可以唯一地通过一个同态进行分解。Nielsen（1921）和 Schreier（1927）将自由群置于组合群论的核心；范畴论的解读——即 F 是忘记函子（forgetful functor）的左伴随——是几乎每本教材中伴随例子的动力来源，也解释了“自由”一词为何成为一个技术术语。Mac Lane 的 §II.7 练习通过更经济的方法达到了这一点：通过群族（groupoids）来建立图上的自由群族，然后从单节点情况读出自由群。这就是该文件所做的事情。它是如何构建的。[Construction/Free/Groupoid.v] 提供自由群范畴；该文件在一个具有单个节点的箭图上实例化它，其边集合是生成的集合，并读取该节点的自同态群。然后，每个群律通过投影就是范畴律——结合律是 [comp_assoc_sym]，单位律是 [id_left]，逆律是 [fginv_left]——就像 [hom_monoid] (Construction/Deloop.v) 从自同态 Hom-集合中读取一个幺半群一样，下面三个 [eq_refl] 示例记录了自由群范畴在所有三个数据字段上的基础幺半群确实是 [hom_monoid]。自从 PR 提出 “代数载体是集合” (2026-09-17) 后，这三个定律中的每一个都是在某个 [inhabits] 下的范畴定律，因为群的 `≈` 是同态等式的命题截断；有关原因请参见下面的 [fg_equiv]，并注意，这三个 [eq_refl] 示例关于操作，且不受影响。集合等价类上的自由群，而不是类型上的自由群。[Grp_Forget] 落在 [Sets] 中，其对象是集合等价类，因此左伴随是一个函子 [Sets ⟶ Grp]，并且生成元携带它们自己的 [≈]，词语关系必须遵守。这是自由幺半群先例无法转移的唯一地方：在 [Instance/Coq/Monoid/Free.v] 中，生成元只是一个普通的 [Type]，并且在莱布尼茨下的 [list X] [=] 已经是自由的，完全没有任何商。这里的单节点箭袋不能是 [Construction/Free/Quiver/Presented.v] 的 [OneNodeQuiver]，它将 Leibniz [=] 放在它的边上；[PointQuiver] 是通过手工构建的，其生成的集合自身的等价关系作为边集合，然后插入的尊重性就不再是新的义务，而是 [FreeGroupoidUnit] 的 [fedgemap_respects] 字段（因为 PR “代数载体是集合”，所以在一个 [inhabits] 下它就是该字段）。两个名为 [GrpObject] 的记录。Construction/Deloop.v 是分层的，位于 [MonObject] 上，并携带单位律和逆元律作为字段；Instance/Grp.v 是扁平的，只携带左手律，右手律和逆元的可尊重性是推导出来的。[Grp] 是后者的范畴，因此这是必须在其上声明该伴随关系的记录，这也是本文件顶部导入顺序是故意安排的原因。在编写此文件时，它们之间的唯一桥梁是 [Instance/Rep.v] 的 [grp_mon]，它将 Instance/Grp.v 的记录读取为 [MonObject]（Instance/Grp/Congruence.v 后来提供了记录到记录的转换器 [grp_deloop_GrpObject]）；它丢弃了逆元，因此它不提供 [Deloop_IsGroupoid] 的假设（该引理是在 Deloop 的 [GrpObject] 上陈述的），而且它的文件无论如何位于模块和矩阵堆栈的顶部，这里没有任何东西需要它。因此 [grp_deloop_monoid] 和 [grp_deloop_IsGroupoid] 直接在 Instance/Grp.v 的记录上重建了两行的桥梁。通过 [vertex_group]（Structure/Groupoid.v）路由自由的 GROUP 会生成一个 Deloop 风格的记录，因此会落入错误的类别；因此，该群直接从词商组装而成。乘法是组合，因此从右到左：一个字母单词 a 和 b 的乘积是单词“b 然后 a”。这是内部约定（[hom_monoid] 的 [mon_op] 是 [fun f g => f ∘ g]），它使得 [fmap_comp] 可以在无需调节的情况下释放 [grp_map_mul]；[free_group_mul_is_compose] 通过 [eq_refl] 固定它。

   力量，已测量。- [eq_refl]：自由函子在对象上的部分是词群（[FreeGrp_obj]）；通用箭头是生成元的插入（[free_group_arrow_is_insert]）；单位是单字母词（[free_group_unit_is_insert], [free_group_unit_is_generator]）；乘法是组合，群单位是恒等箭头，取逆是词反转，底层幺半群是三个数据字段上的 [hom_monoid]。- 仅 [≈]：COUNIT。它是另一种转置，即 [unique_obj (ump_universal_arrows …)]，且 [ump_universal_arrows]（Theory/Universal/Arrow.v）是 [Qed]-不可见的，所以它不会计算，并且在那一边没有声明 [eq_refl]。所证明的是它与词评价在 [≈]（[free_group_counit_evaluates]）意义下是一致的，这就是内容；Test/ProbeFreeGroupoid.v 用一个 [Fail] 探针固定了负面的一边。- 三角恒等式是由 [Theory/Adjunction.v] 推导出的，[counit_fmap_unit] 和 [fmap_counit_unit] 实例化，并且在此处命名，因为问题要求按名称提出。它们是推导出来的，而不是域，因此对它们进行实例化是对伴随关系是否为预期的一种真实检查，而不是重述。非空性。一个在空集或单元素生成集合上的自由群是阿贝尔群，并且不会展示任何内容。因此，该实例具有两个生成元，并通过函子分离为三字母对称群的去环化（Structure/Groupoid.v 的 [S3_Grp]，一个已经在树中的非阿贝尔群）：
   [free_group_two_generators_nonabelian] 和
   [free_group_two_generators_distinct]。由于群的去环化是一个群族，自由群族的泛性质可以直接应用，因此不需要在两个 [GrpObject] 记录之间建立桥梁来支持该实例。这并不是该树应该拥有的唯一自由群伴随。问题#442（maclane:V.6:construction-free-group）通过伴随函子定理的途径到达 [Grp] 上的自由群左伴随，没有任何词的正规形式；Mac Lane 有意展示这两条路线，这两者是互补的而非竞争的——一条展示了该对象，另一条则从完备性和解集出发证明其存在。

   未提供的内容。- 没有简约词的正规形式，因此没有单词问题的判定程序，没有 Nielsen-Schreier 定理，也没有证明 [fg_insert] 对一般生成集合是单射。已证明的是它在两个字母的见证上（[free_group_two_generators_distinct]）是单射，通过映射到 S3。一般的证明需要一族可分离的群，在构造设置中本质上又是正规形式定理。
   - 没有声明 [FreeGrp] 是忠实的，也没有对其像的刻画。
   - 没有自由阿贝尔群，没有 [Sets] 上的自由幺半群（树上的自由幺半群 [Instance/Coq/Monoid/Free.v] 是在 [Coq] 上），也没有它们之间的比较函子。
*)

(*
   * ** The one-node quiver on a setoid

   [Construction/Free/Quiver/Presented.v]'s [OneNodeQuiver] uses
   [Build_Quiver_Standard_Eq], which puts Leibniz [=] on the edges.  That
   will not do here: [Grp_Forget] lands in [Sets], so the free group is the
   free group on a SETOID, and the generators carry their own [≈], which
   the word relation must respect.  Hence the quiver is built by hand, with
   the generating setoid's own equivalence as the edge setoid. 

   --------
   * ** 集合等价类上的单节点箭图

   [Construction/Free/Quiver/Presented.v] 的 [OneNodeQuiver] 使用 [Build_Quiver_Standard_Eq]，它将 Leibniz [=] 放在边上。这在这里行不通：[Grp_Forget] 落在 [Sets] 中，所以自由群是在集合等价类上的自由群，生成元具有它们自己的 [≈]，单词关系必须尊重这一点。因此，箭图是手工构建的，生成集合等价类自身的等价关系作为边的集合等价类。
*)
Definition PointQuiver (X : SetoidObject) : Quiver := {|
  nodes   := poly_unit;
  edges   := fun _ _ => carrier X;
  edgeset := fun _ _ => is_setoid X
|}.

(*
   * ** The word group

   Mac Lane's §II.7 Ex. 3 read at one object: the free group on [X] is the
   endomorphism group of the unique node of the free groupoid on the
   one-node quiver.  Every group law below is a CATEGORY law by projection
   — associativity is [comp_assoc_sym], the unit law is [id_left], the
   inverse law is [fginv_left] — exactly as [hom_monoid]
   ([Construction/Deloop.v]) reads a monoid off an endomorphism hom-set.

   Multiplication is composition, so it runs right to left: the product of
   the one-letter words [a] and [b] is the word “b then a”.  That is the
   house convention ([hom_monoid]'s [mon_op] is [fun f g => f ∘ g]) and it
   is what makes [fmap_comp] discharge [grp_map_mul] with no massaging;
   [free_group_mul_is_compose] pins it by [eq_refl]. 

   --------
   * ** 词组

   Mac Lane 的 §II.7 练习 3 从一个对象来理解：[X] 上的自由群是单节点上的自由群范畴的唯一节点的自同态群。下面的每个群律都是通过投影得到的范畴律——结合律是 [comp_assoc_sym]，单位律是 [id_left]，逆元律是 [fginv_left]——完全像 [hom_monoid]（[Construction/Deloop.v]）从自同态 Hom 集中读出一个幺半群。

   乘法即复合，因此它从右往左运行：单字 [a] 和 [b] 的乘积是词“先 b 后 a”。这是屋子 convention（[hom_monoid] 的 [mon_op] 是 [fun f g => f ∘ g]），并且它使得 [fmap_comp] 可以无需任何整理地应用 [grp_map_mul]；[free_group_mul_is_compose] 通过 [eq_refl] 将其固定。
*)

Definition FGWord (X : SetoidObject) : Type :=
  ttt ~{FreeGroupoid (PointQuiver X)}~> ttt.

(*
   * *** The word group's equality is a PROPOSITIONAL TRUNCATION

   An earlier revision set [is_setoid (FreeGrpSetoid X)] to the free
   groupoid's hom-setoid itself.  Since the PR “algebraic carriers are sets”
   (2026-09-17) a [GrpObject] carries [grp_prop], and the free groupoid's
   hom-equality is [Construction/Quotient.v]'s [CongClosure], a
   five-constructor [Type]-valued inductive for which NO [Prop] mirror with
   an elimination back into [Type] exists (measured: a truncation of it is refused
   with “Incorrect elimination of h in the inductive type inhabited”, and a
   hand [Prop] mirror inductive has no [_rect], so [pequiv_to] cannot be
   written).  The resolution is the one this library adopts for every
   quotient object: the free groupoid keeps its data-valued hom-equality AS A
   CATEGORY, and its one-object hom-monoid VIEWED AS A GROUP IN SET carries
   the truncation.

   What this costs and does not cost.  It costs one [inhabits] on each group
   law and one [destruct] wherever a word equation is consumed.  It does NOT
   cost the domain of the universal property: [FreeGrpObject],
   [free_group_universal], [free_group_universal_arrow], [FreeGrp],
   [free_group_adjunction] and Instance/Grp/FreeAFT.v's totality statements
   all still quantify over ALL of [Sets], with no [PropEquiv] hypothesis on
   the generating setoid anywhere in this file.  Nor does it weaken the two
   non-vacuity theorems below, whose conclusion is [False] and whose
   hypothesis is therefore unwrapped for free. 

   --------
   * *** 词组“equality”是一个命题截断早期的修订将 [is_setoid (FreeGrpSetoid X)] 设置为自由群oid的同态集自身。自从 PR “代数载体是集合”（2026-09-17）以来，一个 [GrpObject] 携带 [grp_prop]，并且自由群oid的同态相等是 [Construction/Quotient.v] 的 [CongClosure]，一个五构造器的 [Type] 值归纳类型，对于它没有 [Prop] 的镜像可消除回到 [Type]（衡量：它的截断被拒绝，显示“在所居住的归纳类型中对 h 的消除不正确”，且手动 [Prop] 镜像归纳没有 [_rect]，因此无法编写 [pequiv_to]）。解决方案是该库对每个商对象采用的方法：自由群oid 保持其数据值的同态相等作为一个类别，而其单一对象的同态单子视为集合中的群，携带其截断。这将花费什么以及不花费什么。它在每个群上花费一个 [inhabits] 在每个群律上，并且在每次使用字方程时花费一个 [destruct]。它不花费普适性质的域：[FreeGrpObject]、[free_group_universal]、[free_group_universal_arrow]、[FreeGrp]、[free_group_adjunction] 以及 Instance/Grp/FreeAFT.v 的全体陈述仍然量化覆盖 [Sets] 的全部，在本文件的任何地方都没有 [PropEquiv] 对生成的等值类的假设。它也不会削弱下面的两个非空性定理，它们的结论是 [False]，因此其假设是免费的。
*)
Definition fg_equiv (X : SetoidObject) (a b : FGWord X) : Prop :=
  inhabited (@equiv _ (@homset (FreeGroupoid (PointQuiver X)) ttt ttt) a b).

Lemma fg_equiv_equivalence (X : SetoidObject) : Equivalence (fg_equiv X).
Proof.
  constructor.
  - intro a; constructor; reflexivity.
  - intros a b [Hab]; constructor; now symmetry.
  - intros a b c [Hab] [Hbc]; constructor; now transitivity b.
Qed.

Definition FreeGrpSetoid (X : SetoidObject) : SetoidObject := {|
  carrier   := FGWord X;
  is_setoid := {| equiv        := fg_equiv X
                ; setoid_equiv := fg_equiv_equivalence X |}
|}.

Lemma fg_mul_respects (X : SetoidObject) :
  Proper (fg_equiv X ==> fg_equiv X ==> fg_equiv X)
    (fun a b : FGWord X => a ∘ b).
Proof.
  (*
 Every argument is introduced BEFORE either truncation is opened: the
 intermediate goal of a [respectful] chain is ascribed sort [Type], so an
 elimination there is refused even though the final goal is a [Prop]. 

 --------
 每个参数都在打开任何截断之前引入：[respectful] 链的中间目标被归类为 [Type]，所以即使最终目标是 [Prop]，也会拒绝那里的消去。
*)
  intros a a' Ha b b' Hb.
  destruct Ha as [Ha], Hb as [Hb]; constructor.
  exact (@compose_respects (FreeGroupoid (PointQuiver X)) ttt ttt ttt
           a a' Ha b b' Hb).
Qed.

Definition FreeGrpObject (X : SetoidObject) : GrpObject := {|
  grp_setoid := FreeGrpSetoid X;

  grp_unit := @id (FreeGroupoid (PointQuiver X)) ttt;
  grp_mul  := fun a b => a ∘ b;
  grp_inv  := fun a => fginv a;

  grp_mul_respects := fg_mul_respects X;

  grp_mul_assoc := fun a b c =>
    inhabits (@comp_assoc_sym (FreeGroupoid (PointQuiver X))
                ttt ttt ttt ttt a b c);
  grp_mul_unit_l := fun a =>
    inhabits (@id_left (FreeGroupoid (PointQuiver X)) ttt ttt a);
  grp_mul_inv_l  := fun a => inhabits (fginv_left a);

  grp_prop :=
    @PropEquiv_of_relation _ (is_setoid (FreeGrpSetoid X)) (fg_equiv X)
      (fun _ _ h => h) (fun _ _ h => h)
|}.

(*
   * The multiplication IS composition and the unit IS the identity arrow,
   definitionally. 

   --------
   * 乘法在定义上就是组合，单位在定义上就是恒等箭头。
*)
Example free_group_mul_is_compose (X : SetoidObject) (a b : FGWord X) :
  grp_mul (FreeGrpObject X) a b
    = @compose (FreeGroupoid (PointQuiver X)) ttt ttt ttt a b := eq_refl.

Example free_group_unit_is_id (X : SetoidObject) :
  grp_unit (FreeGrpObject X) = @id (FreeGroupoid (PointQuiver X)) ttt
  := eq_refl.

(*
   * Inversion IS word reversal — [Lib/TList.v]'s [tlist_rev] at the sign
   swap — and it is the chosen inverse of the groupoid structure. 

   --------
   * 逆转就是单词反转——在符号处，[Lib/TList.v] 的 [tlist_rev] 交换——并且它是群的结构中选定的逆元素。
*)
Example free_group_inv_is_reversal (X : SetoidObject) (a : FGWord X) :
  grp_inv (FreeGrpObject X) a
    = ginv (FreeGroupoid_IsGroupoid (PointQuiver X)) a := eq_refl.

(*
   * The underlying monoid is literally [hom_monoid] of the free groupoid:
   all three data fields agree on the nose. 

   --------
   * 底层幺半群实际上是自由群族的 [hom_monoid]：
   所有三个数据字段完全一致。
*)
Example free_group_monoid_carrier (X : SetoidObject) :
  carrier (grp_setoid (FreeGrpObject X))
    = carrier (hom_monoid (FreeGroupoid (PointQuiver X)) ttt) := eq_refl.

Example free_group_monoid_op (X : SetoidObject) :
  grp_mul (FreeGrpObject X)
    = @mon_op (hom_monoid (FreeGroupoid (PointQuiver X)) ttt) := eq_refl.

Example free_group_monoid_unit (X : SetoidObject) :
  grp_unit (FreeGrpObject X)
    = @mon_unit (hom_monoid (FreeGroupoid (PointQuiver X)) ttt) := eq_refl.

(*
   * ** The insertion of generators

   A letter becomes the one-letter positive word.  Respectfulness is not
   reproved: it is the [fedgemap_respects] field of
   [Construction/Free/Groupoid.v]'s [FreeGroupoidUnit], read at the single
   node. 

   --------
   * ** 发电机的插入

   一个字母变成了一个字母的积极词。尊重并不被责备：它是 [fedgemap_respects] 的 [Construction/Free/Groupoid.v] 的 [FreeGroupoidUnit] 字段，在单个节点读取。
*)
(* The codomain's `≈` is now the truncation, so the groupoid-level respectfulness is wrapped rather than reproved. / 余域的 `≈` 现在是截断，因此群类层级的尊重性是被包装的，而不是重新证明的。 *)
Definition fg_insert (X : SetoidObject)
  : X ~{Sets}~> Grp_Forget (FreeGrpObject X).
Proof.
  unshelve refine
    {| morphism :=
         @fedgemap _ _ (FreeGroupoidUnit (PointQuiver X)) ttt ttt |}.
  intros a b Hab.
  constructor.
  exact (@fedgemap_respects _ _
           (FreeGroupoidUnit (PointQuiver X)) ttt ttt a b Hab).
Defined.

Example fg_insert_is_generator (X : SetoidObject) (a : carrier X) :
  fg_insert X a = @fgpos (PointQuiver X) ttt ttt a := eq_refl.

(*
   * ** Delooping an [Instance/Grp.v] group

   [Construction/Deloop.v]'s [Deloop_IsGroupoid] is stated over THAT file's
   [GrpObject], and there is no converter in tree from it to this one.
   Both halves are one line each here, so the delooping is rebuilt directly
   over [Instance/Grp.v]'s record rather than routed through a record
   conversion.  ([Instance/Rep.v]'s [grp_mon] is the same monoid bridge,
   but that file sits on top of the module and matrix stack, which nothing
   here needs.) 

   --------
   * ** 去环一个 [Instance/Grp.v] 组

   [Construction/Deloop.v] 的 [Deloop_IsGroupoid] 声明在 THAT 文件的
   [GrpObject] 上，并且在树中没有从它到这个的转换器。
   这里的两个半部分各占一行，因此去环直接
   在 [Instance/Grp.v] 的记录上重建，而不是通过记录
   转换路由。 ([Instance/Rep.v] 的 [grp_mon] 是相同的幺半群桥，
   但该文件位于模块和矩阵堆栈之上，而这里没有任何
   需要。)
*)

Definition grp_deloop_monoid (H : GrpObject) : MonObject := {|
  mon_setoid := grp_setoid H;

  mon_unit := grp_unit H;
  mon_op   := grp_mul H;

  mon_op_respects := grp_mul_respects H;

  mon_op_assoc  := fun a b c => symmetry (grp_mul_assoc H a b c);
  mon_op_unit_l := grp_mul_unit_l H;
  mon_op_unit_r := grp_mul_unit_r H
|}.

Definition grp_deloop (H : GrpObject) : Category :=
  Deloop (grp_deloop_monoid H).

(*
   * The delooping of a group is a groupoid: the inverse of an arrow is the
   group inverse of the element, and the two [IsIsomorphism] fields are the
   two inverse laws — the left one a field of [GrpObject], the right one
   [Instance/Grp.v]'s derived [grp_mul_inv_r]. 

   --------
   * 一个群的去环化是一个群oid：箭头的逆是元素的群逆，而两个 [IsIsomorphism] 场是两个逆律——左边的是 [GrpObject] 的场，右边的是 [Instance/Grp.v] 衍生的 [grp_mul_inv_r] 。
*)
Definition grp_deloop_IsGroupoid (H : GrpObject) : IsGroupoid (grp_deloop H) :=
  fun x y a =>
    @Build_IsIsomorphism (grp_deloop H) x y a (grp_inv H a)
      (grp_mul_inv_r H a) (grp_mul_inv_l H a).

(* * ** Deliverable 3: the universal property of the free group / * ** 可自由群的普遍性质 *)

Section Extension.

Context (X : SetoidObject) (H : GrpObject).
Context (h : X ~{Sets}~> Grp_Forget H).

(** [h], read as a quiver homomorphism into the delooping of [H]. / [h]，读作一个箭袋同态，进入 [H] 的去环化。 *)
Definition point_hom
  : QuiverHomomorphism (PointQuiver X) (QuiverOfCat (grp_deloop H)) :=
  @Build_QuiverHomomorphism (PointQuiver X) (QuiverOfCat (grp_deloop H))
    (fun _ => ttt)
    (fun _ _ a => h a)
    (fun _ _ => proper_morphism h).

Definition extend_functor : FreeGroupoid (PointQuiver X) ⟶ grp_deloop H :=
  FreeGroupoidFunctor (PointQuiver X) (grp_deloop_IsGroupoid H) point_hom.

(*
   * The extension of [h] to the free group.  Its action is [fmap] of the
   functor just built; the [Build_GrpHom'] smart constructor derives unit
   preservation, and multiplication preservation IS [fmap_comp] — the free
   group's multiplication being composition and the delooping's being the
   group operation, both definitionally. 

   --------
   * [h] 对自由群的扩展。它的作用是刚构建的函子 [fmap]；[Build_GrpHom'] 智能构造函数推导出单位保持性，并且乘法保持性是 [fmap_comp] ——自由群的乘法是复合，而去环化的乘法是群运算，两者在定义上都是如此。
*)
(*
 The underlying setoid map.  Its respectfulness used to BE
 [fmap_respects], because the free group's `≈` was the free groupoid's
 hom-equality on the nose.  Since the PR “algebraic carriers are sets”
 (2026-09-17) the source equality is that hom-equality's TRUNCATION, so the
 elimination is routed through the TARGET group's own [Prop] equality:
 [pequiv_to] opens it, the truncation is destructed there, [pequiv_from]
 closes it, and [fmap_respects] finishes unchanged.  Note what is NOT
 needed: nothing is asked of [X].  The witness comes from [H], which
 carries [grp_prop] as a field. 

 --------
 基础的集合等价映射。它的尊重以前是 [fmap_respects]，因为自由群的 `≈` 就是自由群oid 上严格的同态等式。自从 PR “代数承载是集合” (2026-09-17) 后，源等式变成了同态等式的截断，因此消解通过目标群自身的 [Prop] 等式进行：[pequiv_to] 打开它，截断在那里被析出，[pequiv_from] 关闭它，[fmap_respects] 完成而不变。注意不需要的内容：[X] 没有要求。证明来自 [H]，它作为字段承载 [grp_prop]。
*)
Definition free_grp_extend_map
  : SetoidMorphism (grp_setoid (FreeGrpObject X)) (grp_setoid H).
Proof using X H h.
  unshelve refine {| morphism := fun w => fmap[extend_functor] w |}.
  intros u v Huv.
  apply (@pequiv_to _ _ (grp_prop H)).
  destruct Huv as [Huv].
  apply (@pequiv_from _ _ (grp_prop H)).
  exact (@fmap_respects _ _ extend_functor ttt ttt u v Huv).
Defined.

Definition free_grp_extend : FreeGrpObject X ~{Grp}~> H :=
  @Build_GrpHom' (FreeGrpObject X) H free_grp_extend_map
    (fun a b => @fmap_comp _ _ extend_functor ttt ttt ttt a b).

(** It agrees with [h] on the generators. / 它在生成器上的表现与 [h] 一致。 *)
Lemma free_grp_extend_generators (a : carrier X) :
  free_grp_extend (fg_insert X a) ≈ h a.
Proof using X H h.
  exact (FreeGroupoidFunctor_gen (PointQuiver X) (grp_deloop_IsGroupoid H)
           point_hom (x:=ttt) (y:=ttt) a).
Qed.

(*
   * ...and it evaluates a word: the two structural clauses that pin down
   what “evaluate a word in the group” means, both instances of the
   homomorphism laws. 

   --------
   * …并且它会评估一个词：两个结构子句确定了“在群中评估一个词”的含义，以及同态定律的两个实例。
*)
Lemma free_grp_extend_mul (u v : FGWord X) :
  free_grp_extend (grp_mul (FreeGrpObject X) u v)
    ≈ grp_mul H (free_grp_extend u) (free_grp_extend v).
Proof using X H h. exact (grp_map_mul free_grp_extend u v). Qed.

Lemma free_grp_extend_inv (u : FGWord X) :
  free_grp_extend (grp_inv (FreeGrpObject X) u)
    ≈ grp_inv H (free_grp_extend u).
Proof using X H h. exact (grp_map_inv free_grp_extend u). Qed.

(*
   * *** Uniqueness

   Any homomorphism out of the free group agreeing with [h] on the
   generators IS the extension.  The argument is not a fresh induction: the
   competitor is repackaged as a functor into the delooping (its
   [fmap_id] is unit preservation and its [fmap_comp] is multiplication
   preservation, both definitionally), and
   [Construction/Free/Groupoid.v]'s [FreeGroupoidFunctor_unique] finishes.
   In particular the value on an INVERTED letter is never constrained by
   hypothesis — it is forced, which is the whole content of freeness for
   groups as opposed to monoids. 

   --------
   * *** 唯一性

   任何从自由群出发的同态，如果在生成元上与 [h] 一致，就是该扩展。同态的论证不是新的归纳：竞争者被重新包装为到去环化的函子（它的 [fmap_id] 是单位保持，它的 [fmap_comp] 是乘法保持，两者都是定义上的），而 [Construction/Free/Groupoid.v] 的 [FreeGroupoidFunctor_unique] 完成了证明。
   特别地，对一个倒置字母的值从来不受假设约束——它是被迫确定的，这正是群的自由性相比于幺半群的全部内容。
*)

Definition functor_of_hom (g : FreeGrpObject X ~{Grp}~> H)
  : FreeGroupoid (PointQuiver X) ⟶ grp_deloop H.
Proof.
  unshelve eapply Build_Functor.
  - exact (fun _ => ttt).
  - intros [] [] w; exact (grp_map g w).
  (*
 The free group's `≈` is the truncation of the groupoid's since the PR
 “algebraic carriers are sets” (2026-09-17), so the groupoid-level
 hypothesis is wrapped on the way in. 

 --------
 自由群的 `≈` 是群类的截断，因为 PR “代数载体是集合”（2026-09-17），所以群类级别的假设在输入时已经被封装了。
*)
  - intros [] [] u v Huv;
      exact (proper_morphism (grp_map g) u v (inhabits Huv)).
  - intros []; exact (grp_map_unit g).
  - intros [] [] [] u v; exact (grp_map_mul g u v).
Defined.

Lemma free_grp_extend_unique (g : FreeGrpObject X ~{Grp}~> H)
  (Hg : ∀ a : carrier X, g (fg_insert X a) ≈ h a) (w : FGWord X) :
  g w ≈ free_grp_extend w.
Proof using X H h.
  refine (FreeGroupoidFunctor_unique (PointQuiver X)
            (grp_deloop_IsGroupoid H) point_hom (functor_of_hom g)
            (fun _ => eq_refl) _ ttt ttt w).
  intros [] [] a; exact (Hg a).
Qed.

End Extension.

Arguments free_grp_extend {X H} h.
Arguments extend_functor {X H} h.

(*
   * The universal property, in the shape [Theory/Universal/Arrow.v]'s
   [universal_arrow_from_UMP] consumes. 

   --------
   * 通用属性，在形状 [Theory/Universal/Arrow.v] 的 [universal_arrow_from_UMP] 中使用。
*)
Theorem free_group_universal (X : SetoidObject) :
  ∀ (H : GrpObject) (h : X ~{Sets}~> Grp_Forget H),
    ∃! g : FreeGrpObject X ~{Grp}~> H,
      h ≈ fmap[Grp_Forget] g ∘ fg_insert X.
Proof.
  intros H h.
  unshelve eexists.
  - exact (free_grp_extend h).
  - intro a; simpl.
    symmetry; exact (free_grp_extend_generators X H h a).
  - intros g Hg w; simpl.
    symmetry; apply (free_grp_extend_unique X H h g).
    intro a; symmetry; exact (Hg a).
Qed.

(*
   * The free group packaged as a universal arrow.  By
   [Theory/Universal/Arrow.v] this IS an initial object of the comma
   category [=(X) ↓ Grp_Forget]. 

   --------
   * 作为一个通用箭头的自由群。由 [Theory/Universal/Arrow.v] 给出，这确实是逗号范畴 [=(X) ↓ Grp_Forget] 的初始对象。
*)
Definition free_group_universal_arrow (X : Sets)
  : UniversalArrow X Grp_Forget :=
  universal_arrow_from_UMP X Grp_Forget (FreeGrpObject X) (fg_insert X)
    (free_group_universal X).

(*
   * The same content in the direct encoding, where the universal object is
   named rather than projected out of a comma category. 

   --------
   * 直接编码中的相同内容，其中通用对象被命名，而不是从逗号类别中投射出来。
*)
Program Definition free_group_AUniversalArrow (X : Sets)
  : AUniversalArrow X Grp_Forget (FreeGrpObject X) := {|
  universal_arrow := fg_insert X
|}.
Next Obligation.
  intros X H h.
  unshelve eexists.
  - exact (free_grp_extend h).
  - intro a; simpl.
    exact (free_grp_extend_generators X H h a).
  - intros g Hg w; simpl.
    symmetry; apply (free_grp_extend_unique X H h g).
    intro a; exact (Hg a).
Qed.

(*
   * ** Deliverable 4: the free-forgetful adjunction

   The functor, the adjunction and both triangle identities come out of the
   generic machinery of [Theory/Universal/Arrow.v] with no further proof —
   the same route [Construction/Free/Quiver.v] and
   [Instance/Coq/Monoid/Free.v] take. 

   --------
   * ** 可交付成果 4：自由-健忘伴随

   函子、伴随以及两个三角恒等式都直接来自 [Theory/Universal/Arrow.v] 的通用机制，无需进一步证明——
   这是 [Construction/Free/Quiver.v] 和 [Instance/Coq/Monoid/Free.v] 采用的相同路径。
*)

Definition FreeGrp : Sets ⟶ Grp :=
  LeftAdjointFunctorFromUniversalArrows Grp_Forget free_group_universal_arrow.

Definition free_group_adjunction : FreeGrp ⊣ Grp_Forget :=
  AdjunctionFromUniversalArrows Grp_Forget free_group_universal_arrow.

(** The free functor's object part is the word group, definitionally. / 自由函子在对象部分定义上就是单词群。 *)
Example FreeGrp_obj (X : Sets) : FreeGrp X = FreeGrpObject X := eq_refl.

(*
   * The universal arrow is the insertion of generators on the nose:
   [universal_arrow_from_UMP] stores the supplied morphism as the second
   projection of the comma object it builds, so no proof is involved. 

   --------
   * 通用箭头是在鼻子上插入生成元：
   [universal_arrow_from_UMP] 将提供的态射存储为它构建的逗号对象的第二投影，因此不涉及证明。
*)
Example free_group_arrow_is_insert (X : Sets) :
  @arrow _ _ X Grp_Forget (free_group_universal_arrow X) = fg_insert X
  := eq_refl.

(*
   * ** The unit is the one-letter word

   [unit] is DERIVED in [Theory/Adjunction.v] (it is the transpose of the
   identity), not a field, so what it computes to has to be checked.  It is
   [fmap[U] id ∘ arrow], and [fmap[Grp_Forget] id] is the identity setoid
   map, so the unit is [fg_insert] itself. 

   --------
   * ** 单位是那个单字母词

   [unit] 在 [Theory/Adjunction.v] 中被导出（它是恒等映射的转置），不是一个域，因此计算结果需要检查。它是 [fmap[U] id ∘ arrow]，而 [fmap[Grp_Forget] id] 是恒等集合同态映射，因此单位是 [fg_insert] 本身。
*)

Definition free_group_unit (X : Sets)
  : X ~{Sets}~> Grp_Forget (FreeGrp X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_group_adjunction X.

Example free_group_unit_is_insert (X : Sets) (a : carrier X) :
  free_group_unit X a = fg_insert X a := eq_refl.

Example free_group_unit_is_generator (X : Sets) (a : carrier X) :
  free_group_unit X a = @fgpos (PointQuiver X) ttt ttt a := eq_refl.

(*
   * ** The counit evaluates a word

   The counit is the OTHER transpose, and it does not compute: it is
   [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows] is
   [Qed]-opaque, so no [eq_refl] is available on this side and none is
   claimed.  What is available — and is the actual content — is that it
   agrees with word evaluation up to [≈], which the uniqueness half of the
   universal property delivers. 

   --------
   * ** 协单位对一个词进行求值

   协单位是另一个转置，它不进行计算：它是 [unique_obj (ump_universal_arrows …)]，而 [ump_universal_arrows] 是 [Qed] 不透明的，因此在这一侧没有 [eq_refl] 可用，也没有声明可用。 可用的 — 也是实际内容 — 是它与词求值在 [≈] 之前保持一致，这由普遍性质的唯一性部分提供。
*)

Definition free_group_counit (H : Grp)
  : FreeGrp (Grp_Forget H) ~{Grp}~> H :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_group_adjunction H.

(** On a generator the counit is the letter itself. / 在一个生成元上，余单位就是字母本身。 *)
Lemma free_group_counit_generator (H : Grp) (a : carrier (Grp_Forget H)) :
  free_group_counit H (fg_insert (Grp_Forget H) a) ≈ a.
Proof.
  exact (@to_adj_counit _ _ _ _ free_group_adjunction H a).
Qed.

(*
   * ...and on an arbitrary word it is the evaluation of that word in [H],
   i.e. the extension of the identity map on [H]'s carrier. 

   --------
   * …并且对于任意一个词，它是在  [H] 上对该词的评估，即  [H] 的承载集合上的恒等映射的扩展。
*)
Theorem free_group_counit_evaluates (H : Grp) (w : FGWord (Grp_Forget H)) :
  free_group_counit H w
    ≈ free_grp_extend (@id Sets (Grp_Forget H)) w.
Proof.
  apply (free_grp_extend_unique (Grp_Forget H) H (@id Sets (Grp_Forget H))
           (free_group_counit H)).
  intro a; exact (free_group_counit_generator H a).
Qed.

(* * ** The triangle identities Both are instances of [Theory/Adjunction.v]'s derived corollaries; they are named here because the issue asks for them by name. / * ** 三角恒等式 两者都是 [Theory/Adjunction.v] 推导的推论的实例； 它们在这里被命名，因为问题要求使用它们的名称。 *)

Corollary free_group_triangle_left (X : Sets) :
  free_group_counit (FreeGrp X) ∘ fmap[FreeGrp] (free_group_unit X)
    ≈ @id Grp (FreeGrp X).
Proof. exact (@counit_fmap_unit _ _ _ _ free_group_adjunction X). Qed.

Corollary free_group_triangle_right (H : Grp) :
  fmap[Grp_Forget] (free_group_counit H)
    ∘ free_group_unit (Grp_Forget H)
    ≈ @id Sets (Grp_Forget H).
Proof. exact (@fmap_counit_unit _ _ _ _ free_group_adjunction H). Qed.

(*
   * ** The free functor relabels letters

   [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
   factorization, not by a formula, so what the functor does to a word has
   to be proved.  On generators it renames the letter. 

   --------
   * ** 自由函子重新标记字母

   [LeftAdjointFunctorFromUniversalArrows] 通过普遍分解定义了 [fmap]，而不是通过公式，因此必须证明函子对一个单词的作用。在生成元上，它重命名字母。
*)
Lemma free_group_fmap_generators {X Y : Sets} (f : X ~{Sets}~> Y)
  (a : carrier X) :
  fmap[FreeGrp] f (fg_insert X a) ≈ fg_insert Y (f a).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_group_universal_arrow X)
              (@arrow _ _ Y Grp_Forget (free_group_universal_arrow Y) ∘ f)) a).
Qed.

(*
   * ** Non-vacuity: the free group on two generators is nonabelian

   A free group on the empty or a one-element generating set is abelian and
   would demonstrate nothing.  The witness therefore has TWO generators,
   and it is separated by a functor into the delooping of the symmetric
   group on three letters ([Structure/Groupoid.v]'s [S3_Grp], a nonabelian
   group already in tree) — which is a groupoid, so the free-groupoid
   universal property applies directly and no bridge between the two
   [GrpObject] records is needed. 

   --------
   * ** 非虚空性：两个生成元的自由群是非交换的

   空生成集或只有一个元素的生成集上的自由群是交换群，
   并不会展示任何内容。因此，证据需要有两个生成元，
   并且它通过一个函子被分离到三个字母的对称群的去环化中
   （[Structure/Groupoid.v] 的 [S3_Grp]，一个已经在树中的非交换群）——它是一个群族，
   因此自由群族的广义性质可以直接应用，不需要在两个
   [GrpObject] 记录之间建立桥梁。
*)

Definition TwoLetters : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := eq; setoid_equiv := eq_equivalence |}
|}.

Definition two_to_S3
  : QuiverHomomorphism (PointQuiver TwoLetters)
      (QuiverOfCat (Deloop S3_Grp)).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact (fun _ => ttt).
  - exact (fun _ _ b => if b then S3_r else S3_a).
  - intros u v b b' Hb; simpl in Hb; now rewrite Hb.
Defined.

(* A local abbreviation, purely syntactic, so that the witness proofs below fit on a line without disturbing any [rewrite]'s matching. / 本地缩写，纯粹是句法上的，因此下面的证人证明可以在一行上显示，而不会干扰任何 [rewrite] 的匹配。 *)
Local Notation FreeTwo := (FreeGroupoid (PointQuiver TwoLetters)).

Definition two_S3 : FreeTwo ⟶ Deloop S3_Grp :=
  FreeGroupoidFunctor (PointQuiver TwoLetters) deloop_S3_groupoid two_to_S3.

Theorem free_group_two_generators_nonabelian :
  grp_mul (FreeGrpObject TwoLetters)
    (fg_insert TwoLetters true) (fg_insert TwoLetters false)
  ≈ grp_mul (FreeGrpObject TwoLetters)
      (fg_insert TwoLetters false) (fg_insert TwoLetters true) → False.
Proof.
  (*
 The free group's `≈` is the truncation of the free groupoid's since the
 PR “algebraic carriers are sets” (2026-09-17).  The conclusion here is
 [False], a [Prop], so the hypothesis is unwrapped at no cost and the rest
 of the argument is unchanged. 

 --------
 自由群的 `≈` 是自由群族的 截断，因为 PR“代数承载是集合”（2026-09-17）。这里的结论是 [False]，一个 [Prop]，所以假设被无成本地展开，其余的论证保持不变。
*)
  intros [Hcomm].
  apply S3_not_abelian.
  assert (Hs : @equiv _ (@homset (Deloop S3_Grp) ttt ttt)
                 (fmap[two_S3] (@compose FreeTwo ttt ttt ttt
                    (fg_insert TwoLetters true)
                    (fg_insert TwoLetters false)))
                 (fmap[two_S3] (@compose FreeTwo ttt ttt ttt
                    (fg_insert TwoLetters false)
                    (fg_insert TwoLetters true))))
    by (now rewrite Hcomm).
  rewrite !fmap_comp in Hs.
  rewrite !(FreeGroupoidFunctor_gen (PointQuiver TwoLetters)
              deloop_S3_groupoid two_to_S3 (x:=ttt) (y:=ttt)) in Hs.
  exact Hs.
Qed.

(*
   * The two generators are themselves distinct in the free group — the free
   group on two letters does not collapse them. 

   --------
   * 在自由群中，这两个生成元本身是不同的——两个字母的自由群不会将它们合并。
*)
Theorem free_group_two_generators_distinct :
  fg_insert TwoLetters true ≈ fg_insert TwoLetters false → False.
Proof.
  (* Same unwrapping as above, and for the same reason: the goal is [False]. / 与上面相同的拆包，原因也相同：目标是 [False]。 *)
  intros [Hab].
  pose proof (@fmap_respects _ _ two_S3 ttt ttt _ _ Hab) as Hs.
  rewrite !(FreeGroupoidFunctor_gen (PointQuiver TwoLetters)
              deloop_S3_groupoid two_to_S3 (x:=ttt) (y:=ttt)) in Hs.
  discriminate.
Qed.
