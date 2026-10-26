Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.

Generalizable All Variables.

(* * * The full subcategory of propositional setoids, reflective in [Sets] / * * 命题集合类的完整子范畴，在 [Sets] 中是反射的 *)

(*
 nLab:    https://ncatlab.org/nlab/show/full+subcategory
 nLab:    https://ncatlab.org/nlab/show/reflective+subcategory
 nLab:    https://ncatlab.org/nlab/show/Bishop+set
 nLab:    https://ncatlab.org/nlab/show/propositional+truncation
 Book:    The Univalent Foundations Program, “Homotopy Type Theory”, IAS
 2013, Definition 3.1.1 (a SET) and Definition 3.3.1 (a MERE
 PROPOSITION), as cited in Lib/Setoid/Propositional.v
 Book:    Awodey, “Category Theory”, Carnegie Mellon pre-print of the 1st
 ed. (September 2005), §10.3, printed p. 278 (PDF p. 287), read
 from the page image: “Its left adjoint F is the discrete poset
 functor.  For any set X, therefore, one has as the unit the
 identity function X = UF(X).”

 BACKGROUND.  The sets of the textbooks have a propositional equality:
 two elements are equal or they are not, and a proof that they are equal
 carries no information.  The objects of this library's [Sets]
 (Instance/Sets.v) are Bishop sets, setoids whose `≈` is [Type]-valued,
 and Lib/Setoid/Propositional.v explains why that stays so and names the
 property [PropEquiv] that a particular setoid's `≈` is logically a
 proposition.  Instance/Sets/Propositional.v carries the property along
 the constructions of [Sets], and its header records that no instance
 of the shape “every object of [Sets] is propositional” is available.
 This file takes the other route: it cuts out the full subcategory
 [PropSets] of [Sets] on the setoids that CARRY a [PropEquiv], so that
 inside it every object is propositional by construction.  It is the
 category in which a textbook argument that uses the equality of sets
 can be read without truncating anything.

 The subcategory is reflective, and the reflector is the truncation of
 the equality.  [trunc_setoid S] keeps the carrier of S and compares by
 [inhabited (x ≈ y)], a [Prop]; a map out of it into a propositional
 setoid is a map out of S, because [inhabited (x ≈ y)] can be
 eliminated into the [Prop] mirror of the target's `≈` (Lib/Setoid/
 Propositional.v's [pequiv_elim_inhabited], the one elimination
 [PropEquiv] buys).  The unit of the reflection is the identity
 function S → trunc S, and so is the counit trunc X → X.  Over the
 propositional setoids the counit is an isomorphism, as for every full
 reflective subcategory (Construction/Reflective.v's
 [reflective_counit_iso]).

 THE CHOICE PRINCIPLE AND THE SQUASH SETOID (#1349).  Instance/Pos/
 Monadicity.v and Instance/Top/Components.v each stated these; both
 require this file, which now states them once.  The principle
 ∀ A : Type@{c}, inhabited A → A is interderivable, level for level,
 with Instance/Sets/Classifier/OneLevel.v's hypothesis [Untruncate@{c}],
 that every [Powerset_squash] at level c inverts: [untr_of_choice] and
 [choice_of_untr] are the two directions, with [Untruncate@{c}]
 written out as ∀ P : Type@{c}, (∀ Q : Prop, (P → Q) → Q) → P, which
 is OneLevel.v's at [eq_refl] (control C53 of
 Test/ProbeMonadicity469.v), so no [Require] of OneLevel.v is needed.
 The squash setoid [SquashSetoid Q] is [bool] with x ≈ y the sum
 (x = y) + Q ([squash_rel], with [squash_sym] and [squash_trans]), so
 that its [true ≈ false] is Q beside a refutable [true = false]:
 Instance/Pos/Monadicity.v's [trunc_choice] reads the principle off
 it, and Instance/Top/Components.v's
 [components_on_all_Sets_unsquashes] transposes into it.

 IN-TREE CONNECTIONS.
 - Construction/Subcategory.v supplies the record, the category
 [Sub], the inclusion [Incl] and its faithfulness; the sibling
 precedent for a full subcategory of [Sets] cut out by a property of
 objects is Construction/Subcategory/Finite.v's [FinSets].
 - Construction/Reflective.v's record [Reflective] packages the
 reflection ([PropSets_Reflective]); Construction/Reflective/
 Monadic.v's [Reflective_Monadic] then makes [PropSets_Incl] monadic,
 which Instance/Pos/Monadicity.v states ([PropSets_Incl_Monadic]).
 - Instance/Pos/Monadicity.v is the first consumer.  Every poset's
 setoid is propositional there ([pos_PropEquiv]), so Instance/Pos.v's
 [Pos_Forget] factors through [PropSets] by [PropSets_lift]; the
 discrete poset on a propositional setoid needs no truncation, and
 the monad it induces on [PropSets] is isomorphic to the identity
 monad with identity components, which is Awodey's p. 278 unit
 “the identity function X = UF(X)” read over [PropSets].  Over the
 whole of [Sets] the discrete poset is the reflector [PropSets_trunc]
 followed by that one, on objects and on arrows at [eq_refl] (as
 functors the equation is refused, structurally past the standard
 library: R19 of Test/ProbeMonadicity469.v), and its monad is the
 truncation.
 - The concrete algebraic object records carry a [PropEquiv] field
 since PR #1320 (“Algebraic carriers are sets”, merged 2026-09-17),
 so their forgetful functors factor through [PropSets] by
 [PropSets_lift] as well; none of those factorizations is built
 here.
 - Instance/Top/Components.v (#462, PR #1338, merged 2026-09-30)
 built the same category first: its [PSetsSub] and [PSets] are
 [PropSets_sub] and [PropSets] at [eq_refl] (a control of
 Test/ProbeComponents462.v).  This file keeps its own copy as the
 reusable home under Instance/Sets/, with a [Require] closure of 39
 modules against Components.v's 118 (by [Print Libraries]);
 unifying the two is left to the maintainer.  CORRECTION (#1349):
 the maintainer decided “Unify them” (on PR #1346).  Components.v
 now requires this file and defines [PSetsSub] and [PSets] as
 [PropSets_sub] and [PropSets], so that control holds by
 unfolding; its closure is 119 modules with this one, and this
 file's stays 39 (by [Print Libraries]).

 WHAT IS HERE.
 - [PropSets_sub], [PropSets] and [PropSets_Incl]: the subcategory
 record ([sobj] is Instance/Sets/Propositional.v's [PropEquivObj],
 [shom] is [True]), the category and the inclusion, with the
 readbacks [PropSets_Incl_fobj] and [PropSets_Incl_fmap].
 - [PropSets_Full] (full as data), [PropSets_Incl_Full] (full as a
 functor, with the chosen preimage (g; I) readable) and
 [PropSets_Incl_Faithful].
 - [PropSets_LocallyPropositional]: its hom-setoids are propositional,
 pointwise in the target's [pequiv], by Instance/Sets/
 Propositional.v's [LocallyPropositional_of_relation] with the
 relation of its [hom_PropEquiv] read on first projections.  That
 file declares no such instance for [Sets].
 - [PropSets_lift F P]: a functor into [Sets] whose values carry a
 [PropEquiv] factors through [PropSets]; after [PropSets_Incl] it is
 F on objects and arrows ([PropSets_lift_obj], [PropSets_lift_map])
 and ≈ F ([PropSets_lift_Incl]).
 - The truncation: [trunc_equivalence], [trunc_setoid],
 [trunc_PropEquiv], the reflector [PropSets_trunc] with its object
 part [PropSets_trunc_obj], the two transposes [trunc_transpose] and
 [trunc_extend], the hom-set isomorphism [PropSets_trunc_iso] and the
 reflection [PropSets_trunc_Incl : PropSets_trunc ⊣ PropSets_Incl];
 its unit and counit are the identity functions ([PropSets_trunc_unit],
 [PropSets_trunc_counit]); [PropSets_Reflective] is the bundle.
 - Moved here by #1349: [untr_of_choice] and [choice_of_untr], from
 Instance/Pos/Monadicity.v, and the squash setoid [squash_rel],
 [squash_sym], [squash_trans] and [SquashSetoid], from
 Instance/Top/Components.v (THE CHOICE PRINCIPLE above).

 STRENGTHS.  By [eq_refl]: [PropSets_Incl_fobj], [PropSets_Incl_fmap],
 [PropSets_lift_obj], [PropSets_lift_map], [PropSets_trunc_unit] and
 [PropSets_trunc_counit].  Up to ≈: [PropSets_lift_Incl], in
 Theory/Functor.v's [Functor_Setoid], with identity isomorphisms.  An
 object of [PropSets] is a setoid PAIRED WITH a chosen [PropEquiv], as in
 Construction/Subcategory/Finite.v: two witnesses on one setoid give two
 objects, isomorphic by Construction/Subcategory.v's
 [Full_membership_iso] and not equal in general.  That is why
 Instance/Pos/Monadicity.v's monad on [PropSets] is isomorphic to the
 identity monad and not equal to it, for two reasons: its functor
 recomputes the witness from the order (R7 and R12 of
 Test/ProbeMonadicity469.v), and Coq's [sigT] has no η, so a variable
 object does not convert with its rebuilt pair (R20, R21).  Eight
 proofs end [Defined] (counted by token).  Closing each alone [Qed] in
 a copy of this file followed by Instance/Pos/Monadicity.v and the
 commands of an earlier version of that probe, five stop something:
 [PropSets_lift], [PropSets_trunc], [trunc_transpose], [trunc_extend]
 and [PropSets_trunc_Incl] (the readbacks and the transposition read
 through them).  [PropSets_Incl_Full], [PropSets_lift_Incl] and
 [trunc_equivalence] are [Defined] by the data convention only;
 [PropSets_LocallyPropositional], which was a ninth when that was
 measured, is now a plain term.  The chosen preimage of
 [PropSets_Incl_Full] computes for the use of later files: no constant
 of the tree, and no command of the probe, reads through it.
 CORRECTION (#1349): nine proofs end [Defined] now, by token,
 [SquashSetoid] having moved here, and it is load-bearing.  In a
 scratch file, a copy of it closed [Qed] makes Instance/Top/
 Components.v's [squash_id] script refused at its [refine] (“cannot
 unify ”bool“ and ”carrier (SquashSetoidQ Q)“”), and Instance/Pos/
 Monadicity.v's [trunc_choice] script at [true], whose type is not
 that copy's carrier; a copy closed [Defined] is accepted by both.

 UNIVERSES, read off [About]; [o] the carriers and homs, [so] the
 objects, as in [Sets@{o so}], and the bounds o <= Projections.*,
 so <= Projections.* of the sigma types, the compose/ID caps of [Sets]
 and the Logic_lemmas.equality, prod_rect and projections caps of the
 [Adjunction] record (first carried here by [PropSets_trunc_Incl]) are
 the [+].  [PropSets@{o so} : Category@{so o o}], the shape of
 [Sets@{o so}]: the membership [PropEquivObj@{so o o}] sits at the object
 level so, and [Sub]'s own strict level (above the hom level, used only
 in its [id_left] and [id_right] obligations) is instantiated at so,
 which o < so allows.  [trunc_equivalence] and [trunc_setoid] bind the
 single level o, with an empty block on Rocq 9.1.1; their [+] allows
 o <= inhabited.u0, the global level that [inhabited] carries on Coq
 8.19.2 and 8.20.1 (measured there: without it [trunc_equivalence] is
 refused), and [trunc_PropEquiv] has one for the same reason.
 [PropSets_lift@{co ch o so}] adds ch <= o from its functor argument;
 its readbacks pass through [Compose], which forces ch = o by typing
 and adds its strict level s (o < s); [PropSets_lift_Incl] adds a and
 b, the levels of [Functor_Setoid] (o < b its own strict bound).
 [PropSets_trunc_Incl] adds a, the free level of the [Adjunction]
 record that [Build_Adjunction'] leaves.  No block has an equation, and
 [Set] occurs only as [Set < so], which o < so implies.  Since #1349
 the six constants moved here keep the blocks they had, by [About] in
 the trees before and after: [squash_rel], [squash_sym], [squash_trans]
 and [SquashSetoid] bind o, and [untr_of_choice] and [choice_of_untr]
 bind c, each with an empty block on Rocq 9.1.1; on Coq 8.19.2 and
 8.20.1 the first four carry o <= sum.u1 and the last two
 c <= inhabited.u0, as they did in their former files (by [About] in
 overlays of the trees before and after).

 NOT DELIVERED.  The forgetful functors of the algebraic categories are
 not factored through [PropSets].  No equivalence between [PropSets] and
 a category of types with [Prop]-valued equivalence relations is built.
 Limits and colimits of [PropSets] are not constructed (the limits would
 come from Instance/Sets/Propositional.v's [limit_PropEquiv]). 

 --------
 nLab:     https://ncatlab.org/nlab/show/full+subcategory 
 nLab:     https://ncatlab.org/nlab/show/reflective+subcategory 
 nLab:     https://ncatlab.org/nlab/show/Bishop+set 
 nLab:     https://ncatlab.org/nlab/show/propositional+truncation 
 书籍:    《单值基础计划, “同伦类型理论”》，IAS 2013年, 定义 3.1.1（一个集合）和定义 3.3.1（一个纯命题），如在 Lib/Setoid/Propositional.v 中引用
 书籍:    Awodey, 《范畴论》，卡内基梅隆大学第一版预印本（2005年9月），§10.3, 印刷页 278（PDF 第287页），从页面图像阅读: “它的左伴随 F 是离散偏序集函子。因此，对于任何集合 X，单位为恒等函数 X = UF(X)。背景。教科书中的集合具有命题等式：两个元素要么相等，要么不相等，而证明它们相等并不携带任何信息。这个库的 [Sets]（Instance/Sets.v）中的对象是 B主集合（Bishop sets），这些集合其 `≈` 是 [Type] 值类型，而 Lib/Setoid/Propositional.v 解释了为什么保持如此，并命名了属性 [PropEquiv]，表示特定集合的 `≈` 在逻辑上是一个命题。Instance/Sets/Propositional.v 在 [Sets] 的构造中保持该属性，其头部记录了没有可用的“每个 [Sets] 对象都是命题性的”类型实例。这个文件走了另一条路线：它在承载 [PropEquiv] 的集合上截取了 [Sets] 的完整子范畴 [PropSets]，因此在其中每个对象都是通过构造而命题性的。它是这样一个范畴：在这里可以直接阅读教科书中使用集合等式的论证，而无需做任何截断。子范畴是反射的，并且反射器是等式的截断。[trunc_setoid S] 保持 S 的承载，并通过 [inhabited (x ≈ y)] 进行比较，一个 [Prop]；从它映射到命题等价集是从 S 映射出去的，因为 [inhabited (x ≈ y)] 可以被消除到目标 `≈` 的 [Prop] 镜像（Lib/Setoid/Propositional.v 的 [pequiv_elim_inhabited]，单一消除 [PropEquiv] 提供）。反射的单位是恒等函数 S → trunc S，余单位是 trunc X → X。在命题等价集上，余单位是同构，因为对于任何完全反射子范畴（Construction/Reflective.v 的 [reflective_counit_iso]）。选择原理与压缩集合等价类 (#1349)。Instance/Pos/Monadicity.v 和 Instance/Top/Components.v 都陈述了这些；两者都需要此文件，而此文件现在只陈述一次。原理 ∀ A : Type@{c}, inhabited A → A 与 Instance/Sets/Classifier/OneLevel.v 中的假设 [Untruncate@{c}] 在每个层次上都是可互推的，即每个 [Powerset_squash] 在层次 c 上是可逆的：[untr_of_choice] 和 [choice_of_untr] 是两个方向，其中 [Untruncate@{c}] 写作 ∀ P : Type@{c}, (∀ Q : Prop, (P → Q) → Q) → P，这就是 OneLevel.v 在 [eq_refl] （Test/ProbeMonadicity469.v 的控制 C53）处的形式，因此不需要 OneLevel.v 的 [Require]。挤压集合 [SquashSetoid Q] 是 [bool]，其中 x ≈ y 为和 (x = y) + Q ([squash_rel]，带有 [squash_sym] 和 [squash_trans])，因此它的 [true ≈ false] 是 Q 旁边的可反驳 [true = false]：Instance/Pos/Monadicity.v 的 [trunc_choice] 从中读取该原则，而 Instance/Top/Components.v 的 [components_on_all_Sets_unsquashes] 将其转置到其中。树中连接。- Construction/Subcategory.v 提供了记录、类别 [Sub]、包含 [Incl] 及其忠实性；通过对象的属性裁剪出的 [Sets] 的全子范畴的兄弟前例是 Construction/Subcategory/Finite.v 的 [FinSets]。- Construction/Reflective.v 的记录 [Reflective] 封装了反射 (ZW41WZZ)；Construction/Reflective/Monadic.v 的 [Reflective_Monadic] 然后使 [PropSets_Incl] 成为单子，Instance/Pos/Monadicity.v 宣告了这一点 (ZW44WZZ)。- Instance/Pos/Monadicity.v 是第一个使用者。每个偏序集合的集合等价类在那里是命题性的（[pos_PropEquiv]），因此 Instance/Pos.v 的 [Pos_Forget] 通过 [PropSets_lift] 因式分解经过 [PropSets]；在命题集合等价类上的离散偏序集合不需要截断，并且它在 [PropSets] 上引起的幺半群同构于具有恒等组件的恒等幺半群，这就是 Awodey 第 278 页的单位“恒等函数 X = UF(X)”在 [PropSets] 上的读法。在整个 [Sets] 上，离散偏序集合是反射器 [PropSets_trunc] 后那个反射器，在对象和 [eq_refl] 上的箭头上（作为函子，该方程被拒绝，在结构上超过标准库：Test/ProbeMonadicity469.v 的 R19），其幺半群是截断。- 具体的代数对象记录自 PR #1320（“代数承载器是集合”，合并于 2026-09-17）以来携带 [PropEquiv] 字段，因此它们的遗忘函子也通过 [PropSets] 由 [PropSets_lift] 分解；这里没有构建这些分解。- Instance/Top/Components.v（#462，PR #1338，合并于 2026-09-30）首先构建了相同的类别：其 [PSetsSub] 和 [PSets] 在 [eq_refl] 上是 [PropSets_sub] 和 [PropSets]（控制 Test/ProbeComponents462.v）。此文件在 Instance/Sets/ 下保留了自己的副本作为可重用的首页，其对 Components.v 的 118 个模块进行了 39 个模块的 [Require] 封闭（通过 [Print Libraries]）；将两者统一留给维护者。更正（#1349）：维护者决定“统一它们”（在 PR #1346 上）。Components.v 现在需要这个文件，并将 [PSetsSub] 和 [PSets] 定义为 [PropSets_sub] 和 [PropSets]，因此通过展开可以保持控制；它的闭包是包含这个文件的 119 个模块，而这个文件的闭包保持为 39（通过 [Print Libraries]）。这里是什么。- [PropSets_sub]、[PropSets] 和 [PropSets_Incl]：子类别记录（[sobj] 是 Instance/Sets/Propositional.v 的 [PropEquivObj]，[shom] 是 [True]），类别和包含，以及读取回 [PropSets_Incl_fobj] 和 [PropSets_Incl_fmap]。- [PropSets_Full]（完整作为数据），[PropSets_Incl_Full]（完整作为函子，可读取选择的前像 (g; I)）和 [PropSets_Incl_Faithful]。- [PropSets_LocallyPropositional]：它的同态集是命题性的，在目标的 [pequiv] 中按点位，由 Instance/Sets/Propositional.v 的 [LocallyPropositional_of_relation] 定义，并在第一投影上读取其 [hom_PropEquiv] 的关系。该文件没有为 [Sets] 声明这样的实例。-  [PropSets_lift F P] ：一个函子到 [Sets]，其值携带一个 [PropEquiv]，通过 [PropSets] ；经过 [PropSets_Incl] 它在对象和箭头上的表现是 F ([PropSets_lift_obj], [PropSets_lift_map]) 并且约等于 F ([PropSets_lift_Incl])。- 截断：[trunc_equivalence], [trunc_setoid], [trunc_PropEquiv]，反射子 [PropSets_trunc] 及其对象部分 [PropSets_trunc_obj]，两个转置 [trunc_transpose] 和 [trunc_extend]，同态集同构 [PropSets_trunc_iso] 和反射 [PropSets_trunc_Incl : PropSets_trunc ⊣ PropSets_Incl]；它的单位和余单位是恒等函数 ([PropSets_trunc_unit], [PropSets_trunc_counit])；[PropSets_Reflective] 是该束。- 由 #1349 移至此处：[untr_of_choice] 和 [choice_of_untr]，来自 Instance/Pos/Monadicity.v，以及压缩集合 [squash_rel], [squash_sym], [squash_trans] 和 [SquashSetoid]，来自 Instance/Top/Components.v（上面的选择原理）。优势。由 [eq_refl]: [PropSets_Incl_fobj], [PropSets_Incl_fmap], [PropSets_lift_obj], [PropSets_lift_map], [PropSets_trunc_unit] 和 [PropSets_trunc_counit] 提出。至多 ≈: [PropSets_lift_Incl]，在 Theory/Functor.v 的 [Functor_Setoid] 中，使用恒等同构。[PropSets] 的一个对象是一个与选定的 [PropEquiv] 配对的集合体，如 Construction/Subcategory/Finite.v 所示：在同一个集合体上有两个证明体就产生两个对象，它们通过 Construction/Subcategory.v 的 [Full_membership_iso] 同构，通常不相等。这就是为什么 Instance/Pos/Monadicity.v 中 [PropSets] 上的幺半群同构于恒等幺半群，而不等于它的两个原因：它的函子通过顺序重新计算证明体（Test/ProbeMonadicity469.v 的 R7 和 R12），并且 Coq 的 [sigT] 没有 η，因此一个变量对象不能与其重建的配对转换（R20, R21）。八个证明以 [Defined] 结束（按标记计数）。单独关闭每个 [Qed] 在这个文件的副本中，然后是 Instance/Pos/Monadicity.v 和该探针早期版本的命令，五个停止某些操作：[PropSets_lift], [PropSets_trunc], [trunc_transpose], [trunc_extend] 和 [PropSets_trunc_Incl]（读回和换位通过它们读取）。[PropSets_Incl_Full], [PropSets_lift_Incl] 和 [trunc_equivalence] 只是根据数据约定 [Defined]；[PropSets_LocallyPropositional]，当时测量时是第九个，现在是一个普通的项。选定的 [PropSets_Incl_Full] 原像用于后续文件的计算：树的常量和探针的命令都不读取它。更正 (#1349)：按标记计数，现在有九个证明以 [Defined] 结束，[SquashSetoid] 已移至此处，并且它是承重的。在一个草稿文件中，它的一个副本关闭了 [Qed]，使得 Instance/Top/Components.v 的 [squash_id] 脚本在 [refine] 处被拒绝（“无法统一 'bool' 和 'carrier (SquashSetoidQ Q)'”），而 Instance/Pos/Monadicity.v 的 [trunc_choice] 脚本在 [true] 处，其类型不是该副本的 carrier；一个副本关闭了 [Defined] 被两者接受。UNIVERSES，读出 [About]；[o] 承载器和态射，[so] 对象，如 [Sets@{o so}] 所示，以及界 o <= Projections.*，也就是 sigma 类型的 Projections.*，[Sets] 的复合/ID 上限，以及 Logic_lemmas.equality、prod_rect 和 [Adjunction] 记录的 projections 上限（最初由 [PropSets_trunc_Incl] 提供），是 [+]。[PropSets@{o so} : Category@{so o o}]，[Sets@{o so}] 的形状：成员 [PropEquivObj@{so o o}] 位于对象层，因此，[Sub] 自身的严格层级（高于态射层，仅用于它的 [id_left] 和 [id_right] 的约束）在 so 上实例化，这允许 o < so。[trunc_equivalence] 和 [trunc_setoid] 绑定单层 o，在 Rocq 9.1.1 上有一个空块；它们的 [+] 允许 o <= inhabited.u0，这是 [inhabited] 在 Coq 8.19.2 和 8.20.1 上携带的全局层（在那里测量：没有它 [trunc_equivalence] 会被拒绝），而 [trunc_PropEquiv] 出于同样的原因也有一个。[PropSets_lift@{co ch o so}] 从其函子参数中添加 ch <= o；它的回读通过 [Compose] ，该 [Compose] 通过类型强制 ch = o，并添加其严格层 s（o < s）；[PropSets_lift_Incl] 添加了 a 和 b，即 [Functor_Setoid] 的层（o < b 自身严格界）。[PropSets_trunc_Incl] 添加了 a，即 [Adjunction] 记录的自由层，[Build_Adjunction'] 留下的记录。没有块有方程，[Set] 仅作为 [Set < so] 出现，这意味着 o < so。自 #1349 起
 移动到这里的六个常量保持了它们原有的区块，由 [About] 在前后树中：[squash_rel]、[squash_sym]、[squash_trans] 和 [SquashSetoid] 绑定 o，[untr_of_choice] 和 [choice_of_untr] 绑定 c，每个在 Rocq 9.1.1 上都有一个空区块；在 Coq 8.19.2 和 8.20.1 上，前四个携带 o <= sum.u1，最后两个携带 c <= inhabited.u0，就像它们在原文件中一样（由 [About] 在前后树的覆盖中）。

 未交付。代数范畴的遗忘函子没有通过 [PropSets] 分解。没有建立 [PropSets] 与具有 [Prop] 值等价关系的类型范畴之间的等价。[PropSets] 的极限和余极限没有建立（极限将来自 Instance/Sets/Propositional.v 的 [limit_PropEquiv]）。
*)

(** ** The subcategory / ** 子类别 *)

Definition PropSets_sub@{o so | o < so +} :
  Subcategory@{so o so o} Sets@{o so} :=
  @Build_Subcategory Sets@{o so} PropEquivObj@{so o o}
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition PropSets@{o so | o < so +} : Category@{so o o} :=
  Sub@{so o so o so o so} Sets@{o so} PropSets_sub@{o so}.

Definition PropSets_Incl@{o so | o < so +} :
  PropSets@{o so} ⟶ Sets@{o so} :=
  Incl@{so o so o so so} Sets@{o so} PropSets_sub@{o so}.

Example PropSets_Incl_fobj@{o so | o < so +} (X : PropSets@{o so}) :
  fobj[PropSets_Incl@{o so}] X = projT1 X := eq_refl.

Example PropSets_Incl_fmap@{o so | o < so +} (X Y : PropSets@{o so})
  (f : X ~{PropSets@{o so}}~> Y) :
  fmap[PropSets_Incl@{o so}] f = projT1 f := eq_refl.

(** ** Full and faithful / ** 完整且忠实 *)

Definition PropSets_Full@{o so | o < so +} :
  Full Sets@{o so} PropSets_sub@{o so} :=
  fun _ _ _ _ _ => I.

(* Built directly rather than by [Full_Implies_Full_Functor], which is [Qed]: the chosen preimage of g is (g; I), and it computes, for later files; nothing in the tree reads through it yet. / 直接构建，而不是由 [Full_Implies_Full_Functor] 构建的，其为 [Qed]：g 的选择前像是 (g; I)，并且它为之后的文件计算；树中的内容尚未通过它读取。 *)
Definition PropSets_Incl_Full@{o so | o < so +} :
  Functor.Full PropSets_Incl@{o so}.
Proof.
  unshelve refine {| prefmap := fun X Y g => _ |}.
  - exists g. exact I.
  - intros X Y g x. simpl. reflexivity.
Defined.

Definition PropSets_Incl_Faithful@{o so | o < so +} :
  Functor.Faithful PropSets_Incl@{o so} :=
  Incl_Faithful Sets@{o so} PropSets_sub@{o so}.

(** ** Locally propositional / ** 局部命题 *)

(*
 Two arrows are ≈ when their functions agree pointwise up to the
 target's `≈`, so the target's [pequiv] mirrors it pointwise: the
 relation of Instance/Sets/Propositional.v's [hom_PropEquiv], read on
 first projections, since a hom-setoid of [PropSets] is a [sigT] over
 [Sets]'s and not [Sets]'s own. 

 --------
 当两个箭头的函数在目标的 `≈` 上逐点一致时，它们是 ≈ 的，因此目标的 [pequiv] 逐点镜像它：Instance/Sets/Propositional.v 的 [hom_PropEquiv] 的关系，在第一次投影上读取，因为 [PropSets] 的同态集是 [sigT]，基于 [Sets] 而不是 [Sets] 本身。
*)
#[export] Instance PropSets_LocallyPropositional@{o so | o < so +} :
  LocallyPropositional PropSets@{o so} :=
  LocallyPropositional_of_relation PropSets@{o so}
    (fun X Y (f g : X ~{PropSets@{o so}}~> Y) =>
       ∀ a : carrier (projT1 X),
         @pequiv _ _ (projT2 Y) (projT1 f a) (projT1 g a))
    (fun X Y f g H a => pequiv_to _ _ (H a))
    (fun X Y f g H a => pequiv_from _ _ (H a)).

(* * ** Functors into [Sets] with propositional values / * ** 带有命题值的函子到 [Sets] *)

Definition PropSets_lift@{co ch o so | o < so, ch <= o +}
  {C : Category@{co ch ch}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) : C ⟶ PropSets@{o so}.
Proof.
  unshelve refine (@Build_Functor C PropSets@{o so}
                     (fun c => existT _ (F c) (P c)) (fun x y f => _)
                     _ _ _).
  - exists (fmap[F] f). exact I.
  - intros x y f g H. simpl. exact (@fmap_respects _ _ F x y f g H).
  - intros x. simpl. exact (@fmap_id _ _ F x).
  - intros x y z f g. simpl. exact (@fmap_comp _ _ F x y z f g).
Defined.

Example PropSets_lift_obj@{co o so s | o < so, o < s +}
  {C : Category@{co o o}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) (c : C) :
  fobj[PropSets_Incl@{o so} ◯ PropSets_lift@{co o o so} F P] c
    = fobj[F] c := eq_refl.

Example PropSets_lift_map@{co o so s | o < so, o < s +}
  {C : Category@{co o o}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) (x y : C) (f : x ~> y) :
  fmap[PropSets_Incl@{o so} ◯ PropSets_lift@{co o o so} F P] f
    = fmap[F] f := eq_refl.

Definition PropSets_lift_Incl@{co o so s a b |
  o < so, o < s, o < b, co <= a, co <= b, o <= a, so <= a +}
  {C : Category@{co o o}} (F : C ⟶ Sets@{o so})
  (P : ∀ c : C, PropEquivObj@{so o o} (F c)) :
  @equiv _ (@Functor_Setoid@{a b co s so o} C Sets@{o so})
    (PropSets_Incl@{o so} ◯ PropSets_lift@{co o o so} F P) F.
Proof.
  exists (fun c => iso_id). intros x y f a. simpl. reflexivity.
Defined.

(** ** The truncation / ** 截断 *)

Definition trunc_equivalence@{o | +} (S : SetoidObject@{o o}) :
  @Equivalence@{o o} (carrier S)
    (fun x y : carrier S => inhabited (x ≈ y)).
Proof.
  constructor.
  - intros x. exact (inhabits (reflexivity x)).
  - intros x y [H]. exact (inhabits (symmetry H)).
  - intros x y z [H] [K]. exact (inhabits (transitivity H K)).
Defined.

Definition trunc_setoid@{o | +} (S : SetoidObject@{o o}) :
  SetoidObject@{o o} :=
  {| carrier := carrier S;
     is_setoid := {| equiv := fun x y : carrier S => inhabited (x ≈ y);
                     setoid_equiv := trunc_equivalence@{o} S |} |}.

Definition trunc_PropEquiv@{o so | o < so +} (S : SetoidObject@{o o}) :
  PropEquivObj@{so o o} (trunc_setoid@{o} S) :=
  @PropEquiv_of_relation (carrier S) (is_setoid (trunc_setoid@{o} S))
    (fun x y : carrier S => inhabited (x ≈ y))
    (fun x y H => H) (fun x y H => H).

Definition PropSets_trunc_obj@{o so | o < so +} (S : Sets@{o so}) :
  PropSets@{o so} :=
  existT _ (trunc_setoid@{o} S) (trunc_PropEquiv@{o so} S).

Definition PropSets_trunc@{o so | o < so +} :
  Sets@{o so} ⟶ PropSets@{o so}.
Proof.
  unshelve refine (@Build_Functor Sets@{o so} PropSets@{o so}
                     PropSets_trunc_obj@{o so} (fun S T f => _) _ _ _).
  - unshelve eexists; [ | exact I ].
    unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => f x) _).
    intros x y H. simpl in *. destruct H as [H].
    exact (inhabits (proper_morphism f x y H)).
  - intros S T f g H x. simpl. exact (inhabits (H x)).
  - intros S x. simpl. exact (inhabits (reflexivity x)).
  - intros S T U f g x. simpl. exact (inhabits (reflexivity _)).
Defined.

(** ** The reflection / ** 反射 *)

Definition trunc_transpose@{o so | o < so +}
  {S : Sets@{o so}} {X : PropSets@{o so}}
  (k : PropSets_trunc@{o so} S ~{PropSets@{o so}}~> X) :
  S ~{Sets@{o so}}~> PropSets_Incl@{o so} X.
Proof.
  unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => projT1 k x) _).
  intros x y H. exact (proper_morphism (projT1 k) x y (inhabits H)).
Defined.

Definition trunc_extend@{o so | o < so +}
  {S : Sets@{o so}} {X : PropSets@{o so}}
  (g : S ~{Sets@{o so}}~> PropSets_Incl@{o so} X) :
  PropSets_trunc@{o so} S ~{PropSets@{o so}}~> X.
Proof.
  unshelve eexists; [ | exact I ].
  unshelve refine (@Build_SetoidMorphism _ _ _ _ (fun x => g x) _).
  intros x y H. apply (@pequiv_elim_inhabited _ _ (projT2 X)).
  simpl in H. destruct H as [H]. exact (inhabits (proper_morphism g x y H)).
Defined.

#[local] Obligation Tactic := idtac.

Program Definition PropSets_trunc_iso@{o so | o < so +}
  (S : Sets@{o so}) (X : PropSets@{o so}) :
  @Isomorphism Sets@{o so}
    {| carrier := @hom PropSets@{o so} (PropSets_trunc@{o so} S) X ;
       is_setoid := @homset PropSets@{o so} (PropSets_trunc@{o so} S) X |}
    {| carrier := @hom Sets@{o so} S (PropSets_Incl@{o so} X) ;
       is_setoid := @homset Sets@{o so} S (PropSets_Incl@{o so} X) |} := {|
  to   := {| morphism := fun k => trunc_transpose@{o so} k |};
  from := {| morphism := fun g => trunc_extend@{o so} g |}
|}.
Next Obligation. intros S X k k' H x; exact (H x). Qed.
Next Obligation. intros S X g g' H x; exact (H x). Qed.
Next Obligation. intros S X g x; reflexivity. Qed.
Next Obligation. intros S X k x; reflexivity. Qed.

Definition PropSets_trunc_Incl@{o so a | o < so +} :
  @Adjunction@{so o o so o o o o so o a} PropSets@{o so} Sets@{o so}
    PropSets_trunc@{o so} PropSets_Incl@{o so}.
Proof.
  unshelve refine (@Build_Adjunction'@{so o o so o o a so} _ _
                     PropSets_trunc@{o so} PropSets_Incl@{o so}
                     PropSets_trunc_iso@{o so} _ _).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

Example PropSets_trunc_unit@{o so a | o < so +} (S : Sets@{o so}) :
  @Sets.morphism _ _ _ _
    (@Category.Theory.Adjunction.unit _ _ _ _
       PropSets_trunc_Incl@{o so a} S) = (fun x : carrier S => x)
  := eq_refl.

Example PropSets_trunc_counit@{o so a | o < so +} (X : PropSets@{o so}) :
  @Sets.morphism _ _ _ _
    (projT1 (@Category.Theory.Adjunction.counit _ _ _ _
               PropSets_trunc_Incl@{o so a} X))
    = (fun x : carrier (projT1 X) => x)
  := eq_refl.

Definition PropSets_Reflective@{o so a | o < so +} :
  Reflective PropSets_sub@{o so} :=
  {| reflective_full := PropSets_Full@{o so};
     reflector := PropSets_trunc@{o so};
     reflective_adj := PropSets_trunc_Incl@{o so a} |}.

(* * ** The choice principle, written out (moved here by #1349) / * ** 选择原则，已写出（由 #1349 移到这里） *)

(*
 The principle ∀ A, inhabited A → A under Instance/Sets/Classifier/
 OneLevel.v's name for it, written unfolded so that this file needs no
 further [Require]: the hypothesis of [choice_of_untr] is OneLevel.v's
 [Untruncate@{c}], by [eq_refl] (control C53 of
 Test/ProbeMonadicity469.v).  Moved here from Instance/Pos/Monadicity.v
 by #1349; Instance/Top/Components.v derives its [unsquash_Untruncate]
 and [Untruncate_unsquash] from these two. 

 --------
 在 Instance/Sets/Classifier/OneLevel.v 中，该原理 ∀ A, inhabited A → A 的名称，已展开写出，因此此文件不需要进一步的 [Require]：[choice_of_untr] 的假设是 OneLevel.v 的 [Untruncate@{c}]，由 [eq_refl] (Test/ProbeMonadicity469.v 的控制 C53) 得出。已从 Instance/Pos/Monadicity.v 通过 #1349 移到这里；Instance/Top/Components.v 从这两个导出它的 [unsquash_Untruncate] 和 [Untruncate_unsquash]。
*)
Definition untr_of_choice@{c | +} (G : ∀ A : Type@{c}, inhabited A → A) :
  ∀ P : Type@{c}, (∀ Q : Prop, (P → Q) → Q) → P :=
  fun P h => G P (h (inhabited P) (fun p => inhabits p)).

Definition choice_of_untr@{c | +}
  (U : ∀ P : Type@{c}, (∀ Q : Prop, (P → Q) → Q) → P) :
  ∀ A : Type@{c}, inhabited A → A :=
  fun A h => U A (fun Q k => match h with inhabits a => k a end).

(* * ** The squash setoid (moved here by #1349) / * ** 拓扑等价类（由 #1349 移动到这里） *)

(* The setoid on [bool] whose [true ≈ false] is a given type [Q]. Moved here from Instance/Top/Components.v by #1349. / 在 [bool] 上的集合体，其 [true ≈ false] 是给定类型 [Q] 。由 #1349 从 Instance/Top/Components.v 移动到这里。 *)
Definition squash_rel@{o} (Q : Type@{o}) (x y : bool) : Type@{o} :=
  ((x = y) + Q)%type.

Lemma squash_sym@{o} (Q : Type@{o}) (x y : bool) :
  squash_rel Q x y -> squash_rel Q y x.
Proof. intros [e|q]; [left; symmetry; exact e|right; exact q]. Qed.

Lemma squash_trans@{o} (Q : Type@{o}) (x y z : bool) :
  squash_rel Q x y -> squash_rel Q y z -> squash_rel Q x z.
Proof.
  intros [e1|q] [e2|q']; [left; exact (eq_trans e1 e2)|right; exact q'
                            |right; exact q|right; exact q].
Qed.

Definition SquashSetoid@{o} (Q : Type@{o}) : SetoidObject@{o o}.
Proof.
  refine {| carrier := bool; is_setoid := {| equiv := squash_rel Q |} |}.
  constructor.
  - intro x; left; reflexivity.
  - exact (squash_sym Q).
  - exact (squash_trans Q).
Defined.
