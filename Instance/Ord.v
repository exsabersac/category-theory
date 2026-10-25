(*
   * * Ord, the category of all preorders (Mac Lane's Preord)

   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Springer GTM 5, §IV.3, printed p. 92, Exercise 4.  Read from
   the page image rather than from memory: "4. Show the following
   subcategories to be reflective: (a) The full subcategory of all
   partial orders in the category Preord of all preorders, with
   arrows all monotone functions.  (b) The full subcategory of
   T_0-spaces in Top."  Catalog id: maclane:IV.3:ex4.

   This file and Instance/Ord/Poset.v are half (a).  Half (b) is
   Instance/Top/Kolmogorov.v, written in parallel against the same
   brief; nothing here depends on it and nothing there depends on this.

   ** What is delivered here

   Mac Lane's AMBIENT category, which the exercise cannot even be stated
   without: [Ord], whose objects are preordered setoids and whose
   morphisms are the monotone maps.  Around it, [OrdObject], [OrdHom],
   [OrdHom_Setoid], [ord_hom_id], [ord_hom_compose], the forgetful
   [Ord_Forget : Ord ⟶ Sets], the predicate [OrdAntisymmetric], the full
   subcategory [Pos_Sub]/[Posets] with its inclusion proved Full AND
   Faithful, the comparison with the pre-existing [Pos], and the bridge
   to the thin-category reading.  The REFLECTION itself -- the exercise's
   actual content -- is the sibling file Instance/Ord/Poset.v, whose
   pinned artifact is [Poset_Reflective_in_Ord].

   ** The name

   Mac Lane writes Preord.  This file writes [Ord], because issue #372
   pins the verification name [Poset_Reflective_in_Ord] and a category
   named [Preord] would make that name read wrongly.  The header of
   Instance/Proset.v anticipated exactly this object and called it "an
   Ord category", so the spelling is the tree's own.

   ** Reused, and what that saves

   [OrdObject] is Instance/Pos.v's [PosetObject] MINUS its last field
   [pos_antisym], field for field and name for name with an [ord_]
   prefix; [OrdHom] is that file's [MonoHom] likewise; [OrdHom_Setoid],
   [ord_hom_id], [ord_hom_compose], [ord_hom_compose_respects], [Ord]
   and [Ord_Forget] are its six corresponding declarations, with the
   same proofs.  That is deliberate and it is what makes the comparison
   below cheap: the two records differ in exactly one field, so
   [OrdObject_of_Poset] drops it and [Poset_of_antisym] supplies it, and
   BOTH object round trips close by [eq_refl] (record eta -- Lib.v
   sets [Set Primitive Projections], and [About] reports both records as
   having primitive projections with eta conversion).

   Also reused: Construction/Subcategory.v's [Subcategory], [Sub],
   [Incl], [Incl_Faithful], [Full] and
   [Full_Implies_Full_Functor], with the trivially-true [shom] of
   Instance/Ab/TorsionFree.v's [TorsionFree_Sub] and
   Instance/Rng.v's [CRng_Sub]; [Full] is written qualified as
   [Category.Construction.Subcategory.Full] for the reason that file
   gives -- it exports its OWN [Full], whose first argument is a
   Category.  Instance/Proset.v's [Proset] supplies the thin category.
   Instance/StrictCat.v's [StrictCat] hosts the comparison.

   NEW here: everything about the ANTISYMMETRY-FREE record, the
   subcategory of partial orders inside it, the two passages to and from
   [PosetObject] and the functors they induce, and [ord_le_of_equiv].

   ** Prior art, measured at d658518e (the issue's "Current state" is
   stale in one direction and right in another)

   Issue #372 says "both ambient categories are missing" and "there is no
   Instance/Top.v".  Both are false: Instance/Top.v declares [Top],
   and Instance/Pos.v declares [Pos], the category whose OBJECTS are
   posets.  What IS absent, and is supplied here, is a category of ALL
   preorders: [rg -i 'PreorderObject|ProsetObject|OrdObject|OrdHom'] over
   the .v files returns ZERO hits at d658518e, and the only in-tree
   reading of "preorder as a category" is Instance/Proset.v's
   [Proset P], which turns ONE preorder into a thin category.  A
   case-sensitive [rg -n '\bPreord\b'] returns three lines, all in
   Instance/Roster.v and all prose.

   Two pieces of that prose are made false by this file and are NOT
   edited here (they belong to their own files): Instance/Proset.v
   says the preorder analogue "does not exist yet", and
   Instance/Roster.v says Mac Lane's "Preord" is [Proset] -- which
   was never right, [Proset] being one preorder rather than the category
   of all of them.

   ** The reviewer's distinction, as constructions rather than prose

   The check on this issue is that [Ord] really is the category of ALL
   preorders and not a single preorder viewed as a thin category.  Both
   readings are built and both are pinned by computation:
   [Ord_obj_are_preorders] records [obj[Ord] = OrdObject] and
   [OrdAsCategory_obj_are_points] records
   [obj[OrdAsCategory P] = carrier (ord_setoid P)], each by [eq_refl];
   their IDENTIFICATION is refuted in Test/ProbeOrd372.v.  The passage
   between them runs one way only and is the one Instance/Pos.v
   already takes for posets: [OrdAsCategory] sends a preorder to its thin
   category and [OrdHomAsFunctor] sends a monotone map to the induced
   functor, whose three laws are equations between parallel morphisms in
   a thin target and hence [I].  There is no passage the other way, and
   none is claimed: an object of [Ord] carries a setoid and a relation,
   where a thin category carries neither.

   ** The comparison with [Pos], and its strength

   [Pos_Posets_strict_iso : @Isomorphism StrictCat Pos Posets] -- an
   ISOMORPHISM OF CATEGORIES, not merely an equivalence.  The weaker
   [≅[Cat]] reading is what [Cat]'s hom-setoid ([Functor_Setoid], natural
   isomorphism) would give; [StrictCat] compares functors by
   Theory/Functor.v's [Functor_StrictEq_Setoid], object equality on
   the nose plus a transported agreement of the arrow actions, and both
   round trips meet it.  One of the two [eq_on_obj] families is
   [fun P => eq_refl] outright; the other, [posets_pos_posets_obj], needs
   a [destruct] first, because an object of [Posets] is a stdlib [sigT]
   and stdlib [sigT] is not covered by Lib.v's [Set Primitive
   Projections], so [(`1 x; `2 x) = x] is not definitional.  That
   rejection is pinned as the probe's first negative, with
   [posets_pos_posets_obj] itself as its control -- the SAME statement
   proved, so the negative measures the missing eta and nothing else.

   ** Strengths, measured strict-first

   Eleven [eq_refl] occurrences, all outside any rejection:
   [poset_ord_poset_round] and [ord_poset_ord_round] (both object round
   trips, on the WHOLE record); [pos_to_posets_obj], [posets_to_pos_obj],
   [pos_roundtrip_obj] and [pos_roundtrip_map] (the two functors' actions
   and the [Pos]-side round trip on objects and on the underlying map);
   [ord_functor_fobj]; [Ord_obj_are_preorders] and
   [OrdAsCategory_obj_are_points]; and [monotone_functor_fobj]'s
   counterpart is Instance/Pos.v, not restated.

   ** Universes

   Measured with [Set Printing Universes] on all 66 constants of this
   module, reading BOTH the binder and the constraint block.  NO
   constraint block of any constant carries a universe EQUATION -- every
   entry is [<] or [<=].  The identifications live in BINDERS, and they
   are the donors':

   - [Ord@{u u0 u1 u2 u3 u4} : Category@{u u4 u4}] identifies hom with
   proof.  So does [Pos@{u u0 u1 u2 u3 u4} : Category@{u u4 u4}] --
   character for character the same binder and the same twelve-entry
   block, which is the measurement behind calling this INHERITED from
   the Instance/Pos.v template rather than introduced here.
   - [Subcategory@{u u0 u1 u2} : Category@{u u0 u0} -> Type] identifies
   hom with proof too, on an EMPTY constraint block; [Posets] is
   [Category@{u0 u u}] and [Pos_Sub] is
   [Subcategory@{u u0 u0 u1} Ord@{...}].  This is the one guarded
   rejection: the probe declares [uh < up] and finds [Subcategory C]
   refused with "Cannot enforce up = uh" while [x ~> y] and [id{C}] at
   those very levels are accepted.  [Reflective] cannot be tested apart
   from it -- [Reflective@{u u0 u1 u2 u3 u4 u5}] takes a
   [Subcategory@{u3 u5 u4 u5} C] over [Category@{u3 u5 u5}] -- so no
   second formability negative is stated, and whether [Reflective]
   identifies anything OF ITS OWN is not measured here.  Neither
   identification is claimed unavoidable.

   113 of the 122 constants of the two files carry a [Set] token in a
   universe instance or a constraint block (the nine that do not are the
   [MixPt] inductive family and [mix_le]), always as a BOUND ([Set < u])
   and never as an equation.  The cause is the
   [Prop]-valued order, and that is a discriminating measurement rather
   than a guess: a two-field record [{ s :> SetoidObject; le : carrier s
   -> carrier s -> Prop }] elaborates at [Type@{max(Set+1,u+1,u0+1)}]
   while the same record with [Type] in place of [Prop] elaborates at
   [Type@{max(u+1,u0+1,u1+1)}], with [Set] nowhere.  [Prop]-valuedness is
   Instance/Pos.v's choice, inherited here so that the two records
   differ in one field only.

   ** An engineering finding: [reverse_coercion] eats a negative

   A negative asserting that a thin category is not an object of [Ord]
   was drafted as a guarded [Example : obj[Ord] := OrdAsCategory P] and
   is a FALSE PASS: the guarded command SUCCEEDS.  [Set Printing All]
   shows why -- the elaborated term is
   [@reverse_coercion (obj[Ord]) Category P
   (OrdAsCategory P)], Coq's reverse-coercion mechanism silently
   accepting the ascription because [OrdObject] coerces to [Type].  The
   negative shipped in its place is a CONVERSION one on the two object
   TYPES, where no coercion can intervene.

   ** NOT delivered

   - No equivalence between [Posets] and [Pos] beyond the isomorphism
   measured above, and no claim that the two are equal as categories.
   - No passage from a thin category back to an [OrdObject], hence no
   comparison of [Ord] with any subcategory of [Cat], and nothing
   about thinness or skeletality as in-tree predicates.  Instance/
   Proset/Skeletal.v's [Proset_Skeletal_iff_Antisymmetric],
   [skeleton_of_proset_antisymmetric] and [Proset_Skeleton] are
   the thin-category shadow of the sibling file's reflection; they are
   CITED and no bridge to them is built.
   - No relation to Instance/Proset/Monotone.v's [MonotoneFun] (bare
   monotone functions between prosets, no setoid) or to
   Construction/Enriched/Two.v's [TwoPreorder] (a [Type]-valued
   relation carrying a decider).
   - No limits, colimits, monoidal structure, or completeness for [Ord];
   no [Ord]-analogue of Instance/Pos.v's [Pos_Forget] beyond
   [Ord_Forget] itself, and no adjoint to it.
   - Nothing about the specialization preorder of a topological space,
   which would be the natural bridge to half (b) and is built in
   neither file.

   ** Corrections to the brief that guided this file

   Each is a measurement.  (1) The brief asked for the predicate to be
   named [Antisymmetric]; it is named [OrdAntisymmetric], because
   [Antisymmetric] is a stdlib class ([Coq.Classes.RelationClasses]) used
   in tree at Instance/Proset/Skeletal.v, and [make print-assumptions]
   loads many modules into ONE scope where a shared name audits the wrong
   constant.  No in-tree file DECLARES [Antisymmetric], so this is a
   hazard avoided rather than a collision repaired.  (2) The brief left
   open whether the [Pos] comparison would reach [≅[StrictCat]] or only
   [≅[Cat]]; it reaches [StrictCat].  (3) The brief's suggested typing
   negative on [Proset P] versus an object of [Ord] does not exist as a
   well-typed mis-statement -- see the [reverse_coercion] finding -- and
   was replaced rather than dropped.  Every donor line number the brief
   gave was re-grepped at d658518e and is correct. 

   --------
   * * Ord，所有预序的范畴（Mac Lane 的 Preord）

   书籍：Mac Lane，《为在职数学家准备的范畴》，第2版，
   Springer GTM 5，第 IV.3 节，印刷页码 92，练习 4。请
   从页面图像中阅读，而不是凭记忆：“4. 证明以下子范畴
   是反射的：(a) 在所有预序的范畴 Preord 中，所有偏序的
   完全子范畴，箭头为所有单调函数。(b) 在拓扑范畴 Top
   中的 T_0 空间的完全子范畴。”目录ID：maclane:IV.3:ex4。

   本文件和 Instance/Ord/Poset.v 是 (a) 部分的一半。(b) 部分是
   Instance/Top/Kolmogorov.v，按相同的简要说明平行编写；这里
   没有依赖于那里，那边也没有依赖于这里。

   ** 这里交付的内容Mac Lane 的 AMBIENT 范畴，这个练习甚至无法在没有它的情况下陈述：[Ord]，其对象是预序集套件，其态射是单调映射。在它周围，[OrdObject], [OrdHom], [OrdHom_Setoid], [ord_hom_id], [ord_hom_compose]，遗忘函子 [Ord_Forget : Ord ⟶ Sets]，谓词 [OrdAntisymmetric]，全子范畴 [Pos_Sub] / [Posets] 及其包含被证明为满且忠实，与已有的 [Pos] 的比较，以及通向薄范畴读取的桥梁。反射本身——练习的实际内容——是兄弟文件 Instance/Ord/Poset.v，其固定的工件是 [Poset_Reflective_in_Ord]。

   ** 名称Mac Lane 写了 Preord。这个文件写了 [Ord]，因为 issue #372 锁定了验证名称 [Poset_Reflective_in_Ord]，并且名为 [Preord] 的类别会使该名称读取错误。Instance/Proset.v 的头部正好预料到了这个对象，并称它为“一个 Ord 类别”，所以拼写是树本身的。

   ** 被重复使用，这也节省了什么[OrdObject] 是 Instance/Pos.v 的 [PosetObject] 减去它的最后一个字段 [pos_antisym]，按字段和名称对照使用 [ord_] 前缀；[OrdHom] 是那个文件的 [MonoHom] 同样如此；[OrdHom_Setoid]、[ord_hom_id]、[ord_hom_compose]、[ord_hom_compose_respects]、[Ord] 和 [Ord_Forget] 是它的六个对应声明，具有相同的证明。这是刻意为之，也是让下面比较变得简单的原因：那两个记录恰好在一个字段上不同，所以 [OrdObject_of_Poset] 移除了它，而 [Poset_of_antisym] 补上了它，并且两个对象都通过 [eq_refl]（记录 eta -- Lib.v 设置 [Set Primitive Projections]，并且 [About] 报告两个记录都具有 eta 转换的原始投影）进行近似的循环转换。也重用：Construction/Subcategory.v 的 [Subcategory]、[Sub]、[Incl]、[Incl_Faithful]、[Full] 和 [Full_Implies_Full_Functor]，以及 trivially-true 的 [shom] 来自 Instance/Ab/TorsionFree.v 的 [TorsionFree_Sub] 和 Instance/Rng.v 的 [CRng_Sub]；[Full] 被以限定名 [Category.Construction.Subcategory.Full] 编写，原因是该文件导出它自己的 [Full]，其第一个参数是一个 Category。Instance/Proset.v 的 [Proset] 提供了薄范畴。Instance/StrictCat.v 的 [StrictCat] 承载了比较。

   这里的新内容：关于 ANTISYMMETRY-FREE 记录的一切、其中的偏序子范畴、到 [PosetObject] 和从 [PosetObject] 的两个通道及它们所引出的函子，以及 [ord_le_of_equiv]。

   ** 先前工作，在 d658518e 时测量（该问题的“当前状态”在一个方向上已过时，而在另一个方向上是正确的）问题 #372 说“两个环境类别都缺失”和“没有 Instance/Top.v”。这都是错误的：Instance/Top.v 声明了 [Top]，Instance/Pos.v 声明了 [Pos]，该类别的对象是偏序集合。真正缺失的，并且在这里提供的，是一个包含所有预序的类别：[rg -i 'PreorderObject|ProsetObject|OrdObject|OrdHom'] 对 .v 文件的返回在 d658518e 上没有命中，而唯一的树内“预序作为类别”的读取是 Instance/Proset.v 的 [Proset P]，它将一个预序转为一个薄类别。区分大小写的 [rg -n '\bPreord\b'] 返回三行，都在 Instance/Roster.v 中，且都是散文。这一文件使得两段散文内容错误，并且这里没有进行编辑（它们属于各自的文件）：Instance/Proset.v 表示前序类比“尚不存在”，而 Instance/Roster.v 表示 Mac Lane 的“Preord”是 [Proset]——这从未正确，[Proset] 才是一个前序，而不是所有前序的类别。

   ** 审阅者的区分，作为构造而非散文对此问题的检查是 [Ord] 确实是所有预序的范畴，而不是单个预序视为薄范畴。两种读法都已建立，并且都通过计算被固定：
   [Ord_obj_are_preorders] 记录 [obj[Ord] = OrdObject] 和
   [OrdAsCategory_obj_are_points] 记录
   [obj[OrdAsCategory P] = carrier (ord_setoid P)]，每个都是通过 [eq_refl]；
   它们的 IDENTIFICATION 在 Test/ProbeOrd372.v 中被驳回。它们之间的通道只通向一个方向，并且就是 Instance/Pos.v 已经为偏序集采用的方式：[OrdAsCategory] 将一个预序发送到其薄范畴，[OrdHomAsFunctor] 将单调映射发送到诱导函子，其三个律是在薄目标中平行态射之间的方程，因此 [I]。没有通往另一方向的通道，也没有声称有：一个 [Ord] 对象携带一个集合化结构和一个关系，而一个薄范畴两者都不携带。

   ** 与 [Pos] 的比较及其强度[Pos_Posets_strict_iso : @Isomorphism StrictCat Pos Posets] -- 类别的同构，而不仅仅是等价。较弱的 [≅[Cat] ] 读法是 [Cat] 的 Hom-集族（[Functor_Setoid]，自然同构）所给出的；[StrictCat] 通过 Theory/Functor.v 的 [Functor_StrictEq_Setoid] 比较函子，即严格的对象相等加上箭头作用的传递一致性，并且两个往返都符合这一点。这两个 [eq_on_obj] 家族中的一个是 [fun P => eq_refl] 直接的；另一个 [posets_pos_posets_obj] 则需要先进行 [destruct]，因为 [Posets] 的一个对象是 stdlib [sigT]，而 stdlib [sigT] 并不包含在 Lib.v 的 [Set Primitive Projections] 中，因此 [(`1 x; `2 x) = x] 不是定义上的。该拒绝被标记为探头的首次负面结果，[posets_pos_posets_obj] 本身作为其对照——相同的陈述得以证明，因此负面结果只衡量缺失的 eta，而不涉及其他内容。

   ** 优势，严格优先衡量

   共有十一次 [eq_refl] 出现，均不在任何拒绝之中：[poset_ord_poset_round] 和 [ord_poset_ord_round]（均为对象往返，在整个记录上）；[pos_to_posets_obj]、[posets_to_pos_obj]、[pos_roundtrip_obj] 和 [pos_roundtrip_map]（两个函子作用及 [Pos] 端在对象和底层映射上的往返）；[ord_functor_fobj]；[Ord_obj_are_preorders] 和 [OrdAsCategory_obj_are_points]；[monotone_functor_fobj] 的对应是 Instance/Pos.v，未重新陈述。

   ** 宇宙使用 [Set Printing Universes] 测量该模块的所有 66 个常量，同时读取绑定器和约束块。没有任何常量的约束块包含宇宙方程——每一项都是 [<] 或 [<=]。标识存在于绑定器中，并且它们属于捐赠者：- [Ord@{u u0 u1 u2 u3 u4} : Category@{u u4 u4}] 使用证明识别同态。[Pos@{u u0 u1 u2 u3 u4} : Category@{u u4 u4}] 也是如此——逐字符相同的绑定器和相同的十二条目块，这就是为什么将其称为继承自 Instance/Pos.v 模板而非在此处引入的依据。- [Subcategory@{u u0 u1 u2} : Category@{u u0 u0} -> Type] 也在一个空约束块上使用证明识别同态；[Posets] 即 [Category@{u0 u u}]，[Pos_Sub] 即 [Subcategory@{u u0 u0 u1} Ord@{...}]。这是唯一受到保护的拒绝：探针声明 [uh < up] 并发现 [Subcategory C] 被拒绝，提示“无法强制 up = uh”，而在同一层次上的 [x ~> y] 和 [id{C}] 则被接受。[Reflective] 不能单独测试——[Reflective@{u u0 u1 u2 u3 u4 u5}] 对 [Category@{u3 u5 u5}] 进行了 [Subcategory@{u3 u5 u4 u5} C] ——所以没有说明第二次成型的负面影响，也没有在此测量 [Reflective] 是否能识别其自身的任何内容。两种识别都没有被声称是不可避免的。两个文件中的122个常量中有113个在宇宙实例或约束块中携带 [Set] 令牌（那九个没有的是 [MixPt] 归纳族和 [mix_le]），总是作为 BOUND（[Set < u]），从不作为方程。原因是 [Prop] 值的顺序，这是一个区分性的度量而不是猜测：一个二字段记录 [{ s :> SetoidObject; le : carrier s -> carrier s -> Prop }] 在 [Type@{max(Set+1,u+1,u0+1)}] 处展开，而同样的记录将 [Type] 替换 [Prop] 后在 [Type@{max(u+1,u0+1,u1+1)}] 处展开，[Set] 无处出现。[Prop] 值性是 Instance/Pos.v 的选择，这里继承下来，使得两个记录只有一个字段不同。

   ** 一个工程发现：[reverse_coercion] 会吞掉负数一条否定断言一个薄范畴不是 [Ord] 的一个对象，被起草为一个受保护的 [Example : obj[Ord] := OrdAsCategory P] 并且是一个 FALSE PASS：受保护的命令成功了。[Set Printing All] 解释了原因——展开的项是 [@reverse_coercion (obj[Ord] ) Category P (OrdAsCategory P)]，Coq 的反向强制机制默默接受了该赋值，因为 [OrdObject] 可以强制转换为 [Type]。替代地发出的否定是在两个对象类型上的 CONVERSION 类型，在这里没有强制转换能介入。

   ** 未交付- 在上述测量的同构之外，[Posets] 与 [Pos] 之间没有等价关系，也没有声称两者作为范畴是相等的。 - 从薄范畴返回 [OrdObject] 的途径不存在，因此 [Ord] 与 [Cat] 的任何子范畴没有可比性，也没有关于薄性或骨架性作为树内谓词的内容。Instance/Proset/Skeletal.v 中的 [Proset_Skeletal_iff_Antisymmetric]、[skeleton_of_proset_antisymmetric] 和 [Proset_Skeleton] 是兄弟文件反射的薄范畴影子；它们被引用，但没有建立通向它们的桥梁。 - 与 Instance/Proset/Monotone.v 的 [MonotoneFun]（proset 之间的单调函数，不涉及集合等价类）或 Construction/Enriched/Two.v 的 [TwoPreorder]（携带判定器的 [Type] 值关系）没有关系。- 对于 [Ord]，没有极限、余极限、单oidal结构或完备性；  
   对于 [Ord]，没有 Instance/Pos.v 的 [Pos_Forget] 的类比存在，除了 [Ord_Forget] 本身，也没有它的伴随。  
   - 关于拓扑空间的特化偏序没有任何内容，而这本应是与 (b) 部分的自然桥梁，但在这两个文件中都没有建立。  

   ** 对指导此文件的简报的更正每一项都是一个测量。 (1) 简报要求谓词命名为 [Antisymmetric]；它被命名为 [OrdAntisymmetric]，因为 [Antisymmetric] 是一个 stdlib 类 ([Coq.Classes.RelationClasses])，用于 Instance/Proset/Skeletal.v 中的树，并且 [make print-assumptions] 将许多模块加载到一个作用域中，在那里共享名称审计错误的常量。没有树内文件声明 [Antisymmetric]，因此这是避免的一种风险，而不是修复的冲突。 (2) 简报未说明 [Pos] 比较是否会到达 [≅[StrictCat]] 还是只到 [≅[Cat]]；它达到了 [StrictCat]。 (3) 简报建议的对 [Proset P] 与 [Ord] 对象进行的负类型检查不存在作为类型正确的错误陈述——参见 [reverse_coercion] 发现——并且已被替换而不是删除。简报中提供的每个供体行号都在 d658518e 上重新使用 grep 检查过，并且是正确的。
*)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Pos.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(** ** Objects *)

Record OrdObject := {
  ord_setoid :> SetoidObject;

  ord_le : carrier ord_setoid → carrier ord_setoid → Prop;

  ord_le_respects : Proper (equiv ==> equiv ==> iff) ord_le;

  ord_refl  : ∀ x, ord_le x x;
  ord_trans : ∀ x y z, ord_le x y → ord_le y z → ord_le x z
}.

#[export] Existing Instance ord_le_respects.

(*
   * The order is implied by the carrier's own equivalence: this is the one
   consequence of [ord_le_respects] that the development below consumes. 

   --------
   * 顺序由承运人的自身等价性所暗示：这是 [ord_le_respects] 的一个结果，下文的发展将沿用它。
*)
Lemma ord_le_of_equiv (P : OrdObject) (x y : carrier (ord_setoid P)) :
  x ≈ y → ord_le P x y.
Proof.
  intro Hxy.
  assert (Hxx : x ≈ x) by reflexivity.
  exact (proj1 (ord_le_respects P x x Hxx x y Hxy) (ord_refl P x)).
Qed.


(** ** Morphisms / **态射 *)

Record OrdHom (P Q : OrdObject) := {
  ord_fn :> SetoidMorphism (ord_setoid P) (ord_setoid Q);
  ord_mono : ∀ x y, ord_le P x y → ord_le Q (ord_fn x) (ord_fn y)
}.

Arguments ord_fn {P Q} _.
Arguments ord_mono {P Q} _ _ _ _.

#[local] Obligation Tactic := idtac.

#[export]
Program Instance OrdHom_Setoid {P Q : OrdObject} : Setoid (OrdHom P Q) := {|
  equiv := fun f g => ∀ a, ord_fn f a ≈ ord_fn g a
|}.
Next Obligation.
  intros P Q. constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a;
    transitivity (ord_fn g a); [apply Hfg|apply Hgh].
Qed.

Program Definition ord_hom_id {P : OrdObject} : OrdHom P P := {|
  ord_fn := setoid_morphism_id
|}.
Next Obligation. intros P x y H; exact H. Qed.

Program Definition ord_hom_compose {P Q R : OrdObject}
        (g : OrdHom Q R) (f : OrdHom P Q) : OrdHom P R := {|
  ord_fn := setoid_morphism_compose (ord_fn g) (ord_fn f)
|}.
Next Obligation.
  intros P Q R g f x y H; simpl.
  apply (ord_mono g), (ord_mono f); exact H.
Qed.

Program Instance ord_hom_compose_respects {P Q R : OrdObject} :
  Proper (equiv ==> equiv ==> equiv) (@ord_hom_compose P Q R).
Next Obligation.
  intros P Q R g g' Hg f f' Hf a; simpl.
  transitivity (ord_fn g (ord_fn f' a)).
  - apply proper_morphism, Hf.
  - apply Hg.
Qed.

(** ** The category / ** 类别 *)

Program Definition Ord : Category := {|
  obj     := OrdObject;
  hom     := OrdHom;
  homset  := @OrdHom_Setoid;
  id      := @ord_hom_id;
  compose := @ord_hom_compose;
  compose_respects := @ord_hom_compose_respects
|}.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y f a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.
Next Obligation. intros x y z w f g h a; simpl; reflexivity. Qed.

Program Definition Ord_Forget : Ord ⟶ Sets := {|
  fobj := fun P => ord_setoid P;
  fmap := fun _ _ f => ord_fn f
|}.
Next Obligation. intros P Q f g Hfg a; simpl; exact (Hfg a). Qed.
Next Obligation. intros P a; simpl; reflexivity. Qed.
Next Obligation. intros P Q R f g a; simpl; reflexivity. Qed.

(* * ** Partial orders as a full subcategory / * ** 偏序作为一个完全子范畴 *)

Definition OrdAntisymmetric (P : OrdObject) : Type :=
  ∀ x y : carrier (ord_setoid P),
    ord_le P x y → ord_le P y x → x ≈ y.

Definition Pos_Sub : Subcategory Ord :=
  @Build_Subcategory Ord
    OrdAntisymmetric
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Posets : Category := Sub Ord Pos_Sub.

Lemma Pos_Sub_Full :
  Category.Construction.Subcategory.Full Ord Pos_Sub.
Proof. intros x y ox oy g; exact I. Defined.

Lemma Posets_Incl_Full : Functor.Full (Incl Ord Pos_Sub).
Proof. exact (Full_Implies_Full_Functor Ord Pos_Sub Pos_Sub_Full). Defined.

Lemma Posets_Incl_Faithful : Functor.Faithful (Incl Ord Pos_Sub).
Proof. exact (Incl_Faithful Ord Pos_Sub). Defined.

(* * ** Comparison with the pre-existing [Pos] / * ** 与现有的 [Pos] 的比较 *)

Definition OrdObject_of_Poset (P : PosetObject) : OrdObject := {|
  ord_setoid      := pos_setoid P;
  ord_le          := pos_le P;
  ord_le_respects := pos_le_respects P;
  ord_refl        := pos_refl P;
  ord_trans       := pos_trans P
|}.

Definition Poset_of_antisym (P : OrdObject) (H : OrdAntisymmetric P)
  : PosetObject := {|
  pos_setoid      := ord_setoid P;
  pos_le          := ord_le P;
  pos_le_respects := ord_le_respects P;
  pos_refl        := ord_refl P;
  pos_trans       := ord_trans P;
  pos_antisym     := H
|}.

Example poset_ord_poset_round (P : PosetObject) :
  Poset_of_antisym (OrdObject_of_Poset P) (pos_antisym P) = P := eq_refl.

Example ord_poset_ord_round (P : OrdObject) (H : OrdAntisymmetric P) :
  OrdObject_of_Poset (Poset_of_antisym P H) = P := eq_refl.

Definition OrdHom_of_MonoHom {P Q : PosetObject} (f : MonoHom P Q)
  : OrdHom (OrdObject_of_Poset P) (OrdObject_of_Poset Q) :=
  @Build_OrdHom (OrdObject_of_Poset P) (OrdObject_of_Poset Q)
    (mono_fn f) (mono_le f).

Definition MonoHom_of_OrdHom {P Q : OrdObject}
    (HP : OrdAntisymmetric P) (HQ : OrdAntisymmetric Q) (f : OrdHom P Q)
  : MonoHom (Poset_of_antisym P HP) (Poset_of_antisym Q HQ) :=
  @Build_MonoHom (Poset_of_antisym P HP) (Poset_of_antisym Q HQ)
    (ord_fn f) (ord_mono f).

Program Definition Pos_to_Posets : Pos ⟶ Posets := {|
  fobj := fun P => (OrdObject_of_Poset P; pos_antisym P);
  fmap := fun _ _ f => (OrdHom_of_MonoHom f; I)
|}.
Next Obligation. intros P Q f g Hfg a; simpl; exact (Hfg a). Qed.
Next Obligation. intros P a; simpl; reflexivity. Qed.
Next Obligation. intros P Q R f g a; simpl; reflexivity. Qed.

Program Definition Posets_to_Pos : Posets ⟶ Pos := {|
  fobj := fun x => Poset_of_antisym `1 x `2 x;
  fmap := fun x y f => MonoHom_of_OrdHom `2 x `2 y `1 f
|}.
Next Obligation. intros x y f g Hfg a; simpl; exact (Hfg a). Qed.
Next Obligation. intros x a; simpl; reflexivity. Qed.
Next Obligation. intros x y z f g a; simpl; reflexivity. Qed.

Example pos_to_posets_obj (P : PosetObject) :
  `1 (fobj[Pos_to_Posets] P) = OrdObject_of_Poset P := eq_refl.

Example posets_to_pos_obj (x : Posets) :
  fobj[Posets_to_Pos] x = Poset_of_antisym `1 x `2 x := eq_refl.

Example pos_roundtrip_obj (P : PosetObject) :
  fobj[Posets_to_Pos] (fobj[Pos_to_Posets] P) = P := eq_refl.

Example pos_roundtrip_map (P Q : PosetObject) (f : MonoHom P Q)
    (a : carrier (pos_setoid P)) :
  mono_fn (fmap[Posets_to_Pos] (fmap[Pos_to_Posets] f)) a = mono_fn f a
  := eq_refl.

Lemma posets_pos_posets_obj (x : Posets) :
  fobj[Pos_to_Posets] (fobj[Posets_to_Pos] x) = x.
Proof. destruct x as [P HP]; exact eq_refl. Defined.

Program Definition Pos_Posets_strict_iso :
  @Isomorphism StrictCat Pos Posets := {|
  to   := Pos_to_Posets;
  from := Posets_to_Pos
|}.
Next Obligation.
  exists posets_pos_posets_obj.
  intros x y f; destruct x as [P HP], y as [Q HQ]; simpl.
  intro a; simpl; reflexivity.
Qed.
Next Obligation.
  exists (fun P : PosetObject => eq_refl).
  intros P Q f a; simpl; reflexivity.
Qed.

(* * ** A preorder as a thin category, and the reviewer's distinction / * ** 将 preorder 视为一个薄范畴，以及评审者的区分 *)

Definition ord_preorder (P : OrdObject)
  : RelationClasses.PreOrder (ord_le P).
Proof.
  constructor.
  - exact (ord_refl P).
  - intros x y z f g; exact (ord_trans P x y z f g).
Defined.

Definition OrdAsCategory (P : OrdObject) : Category :=
  Proset (ord_preorder P).

Program Definition OrdHomAsFunctor {P Q : OrdObject} (f : OrdHom P Q)
  : OrdAsCategory P ⟶ OrdAsCategory Q := {|
  fobj := fun x => ord_fn f x;
  fmap := fun x y h => ord_mono f x y h
|}.
Next Obligation. intros P Q f x y g h Hgh; exact I. Qed.
Next Obligation. intros P Q f x; exact I. Qed.
Next Obligation. intros P Q f x y z g h; exact I. Qed.

Example ord_functor_fobj {P Q : OrdObject} (f : OrdHom P Q)
    (x : carrier (ord_setoid P)) :
  fobj[OrdHomAsFunctor f] x = ord_fn f x := eq_refl.

Example Ord_obj_are_preorders : obj[Ord] = OrdObject := eq_refl.

Example OrdAsCategory_obj_are_points (P : OrdObject) :
  obj[OrdAsCategory P] = carrier (ord_setoid P) := eq_refl.
