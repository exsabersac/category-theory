Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Generator.
Require Import Category.Structure.Generator.Concrete.
Require Import Category.Theory.Concrete.

Generalizable All Variables.

(*
 Separators of [Sets]: the singleton, the terminal object, and the one
 object that is not one

 nLab:  https://ncatlab.org/nlab/show/separator
 nLab:  https://ncatlab.org/nlab/show/well-pointed+category

 Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
 §V.7, book p. 127 (PDF p. 136), Definition 4 is the source: a set of
 objects GENERATES a category when, for every parallel pair h ≠ h',
 some member s of the set carries an f : s → c with h ∘ f ≠ h' ∘ f.
 Mac Lane's two examples are the one-point set for sets and the
 integers for abelian groups.  Awodey, "Category Theory" (1st ed.,
 Carnegie Mellon pre-print, September 2005), §7.2, printed p. 154
 (PDF p. 163), gives the single-object form and the characterization by
 faithfulness of the representable; Riehl, "Category Theory in
 Context", 2nd ed., Definition 4.7.7, printed p. 177 (PDF p. 197),
 gives the family form and names the dual, and her Epilogue §E.4,
 printed p. 257 (PDF p. 277), recalls it as clause (vi) of Giraud's
 theorem.  This file supplies the [Sets] half of Mac Lane's two
 examples, stated against Structure/Generator.v's [IsSeparator] and
 [Generator]; the other half is Instance/Ab/Generator.v, with
 Instance/Grp/Generator.v alongside for Awodey's group example.

 RIEHL'S SPELLING IS THE CONTRAPOSITIVE.  Riehl (and Mac Lane) write
 the condition as "f ≠ g implies some h with f ∘ h ≠ g ∘ h".  Over a
 [Type]-valued hom-setoid with no decision procedure for ≈, NEITHER
 form implies the other: the cancellation form yields only ¬∀ from
 f ≉ g, never the witnessing h, and the negative form yields only
 ¬¬(f ≈ g) from agreeing tests, never f ≈ g; they become
 interderivable under decidability of ≈ on the hom-setoid in question
 (an earlier revision of this paragraph called the negative form
 "strictly weaker", an ordering an audit showed does not hold in either
 direction).  Structure/Generator.v therefore states
 the positive cancellation law — all precompositions agree implies the
 arrows agree — exactly as Adjunction/SAFT.v's [Cogenerator] states
 its dual, and every statement below is in that form.  No weakened
 negative form is proved here, in either direction.

 THE PRIOR ART, AND WHY THIS FILE IS NOT A DUPLICATE.  Issue #447's
 "Current state" paragraph says that a search for
 Generator/Separator/SeparatingFamily/Generates finds exactly one
 [Cogenerator] record and that there is "NO definition of a separating
 set / separator / generating family anywhere".  That is STALE, and the
 correction is recorded here rather than silently worked around.
 Theory/Concrete.v already carries, under Awodey's §1.5 Remark 1.7
 reading of concreteness:

 - [Class Separator (t : C)], a one-field class whose field
 [separates] is the same cancellation law as [IsSeparator];
 - [Concrete_of_Separator] and [Separator_of_Faithful] — BOTH
 directions of the Awodey equivalence with faithfulness of
 [fobj[Curried_Hom C] t] (Functor/Hom.v), already proved;
 - [WellPointedCategory], the terminal-object case;
 - [Sets_Separator], an [#[export] Instance] proving that
 [@terminal_obj Sets Sets_Terminal] separates [Sets], with
 [Sets_point] as its probe;
 - [Sets_empty_not_Separator], the empty setoid as a
 non-example, using [empty_setoid_object].

 So the issue's Awodey checkbox "the terminal object generates Sets"
 was already discharged in the CLASS vocabulary before this file
 existed.  What was missing, and what this file adds, is the same
 content in the vocabulary issue #447 froze — [IsSeparator] and the
 [Generator] record of Structure/Generator.v — the SINGLETON reading
 (a different object from the terminal object, measured below), the
 [Generator] packages, and the transport along the isomorphism between
 the two objects.  The two vocabularies are bridged in both directions
 by Structure/Generator/Concrete.v's [IsSeparator_of_Separator] and
 [Separator_of_IsSeparator], each a one-line repackaging with no proof
 content, so nothing is proved twice: the class and the [Definition]
 are the same law with different binding forms.  (A first draft of
 this file carried its own copy of that bridge pair and its own
 isomorphism-transport lemma, built in parallel with the theory half;
 integration kept the theory half's [separator_iso] and bridges and
 removed the copies.)

 THE SINGLETON AND THE TERMINAL OBJECT ARE TWO STATEMENTS.  This is a
 measurement, not a caution.  Instance/Sets.v's
 [unit_setoid_object] is [{| carrier := poly_unit ; is_setoid :=
 unit_setoid |}], a bare record; Instance/Sets.v's [Sets_Terminal]
 is a [Program Instance] whose [terminal_obj] field is
 [{| carrier := poly_unit |}] with the setoid field left to an
 obligation term.  The two records therefore do not convert, and with
 the exact requirement list of this file

 Example term_is_unit :
 @terminal_obj Sets Sets_Terminal = unit_setoid_object := eq_refl.

 is rejected as

 "The term "eq_refl" has type "1 = 1" while it is expected to have
 type "1 = unit_setoid_object"
 (cannot unify "1" and "unit_setoid_object")."

 a CONVERSION refusal — the [1] being the terminal-object notation,
 which is what this file's import list puts in scope for the left-hand
 side, so the message is quoted with its environment.  Consequently
 [Sets_unit_separates] and [Sets_terminal_separates] are separate
 theorems, and the second is NOT obtained from the first by an
 [eq_refl] identification.  Three routes to it are recorded, all cheap
 and all here:

 1. DIRECT, and this is the delivered constant: [sets_elem_term]
 builds the constant map out of the terminal object itself, so the
 proof is the same two lines as for the singleton.
 2. TRANSPORT, [Sets_terminal_separates_by_transport]: the two
 objects ARE isomorphic ([Sets_terminal_unit_iso]), and
 Structure/Generator.v's [separator_iso] carries the property
 across.  This route is recorded because the transport lemma is
 the reusable half — it is what makes "is a separator" an
 invariant of the isomorphism class rather than of the record.
 3. FROM THE PRIOR ART, [Sets_terminal_separates_from_Concrete]:
 unpack Theory/Concrete.v's [Sets_Separator] through the
 bridge.  This one exists to make the staleness disclosure above
 machine-checked rather than a claim in prose.

 The three inhabit the same type and no claim is made that they are
 equal terms; [IsSeparator] lands in [Type], where proof irrelevance is
 not available, and comparing two of its inhabitants is not a statement
 this file makes.

 WHAT THE EMPTY SETOID SHOWS, AND WHY IT IS A THEOREM.  Separation is a
 genuine condition, and the witness is the initial object:
 Instance/Sets.v's [Sets_Initial] has [False] as carrier, so every
 hypothesis of the separator condition holds vacuously for it, and it
 would identify two arrows that differ.  [Sets_empty_not_separates]
 states this as [IsSeparator … → False].  It is stated positively, and
 NOT as a refusal probe of the kind Test/Probe*.v collects, on purpose:
 such a probe records that the ELABORATOR rejects a command, whereas
 this is a mathematical theorem about a perfectly well-typed statement
 that simply has no inhabitant.  The probe idiom cannot express it, and
 the distinction matters because the two kinds of evidence are not
 interchangeable.  Theory/Concrete.v's [Sets_empty_not_Separator]
 proves the same thing about ITS [empty_setoid_object]; the
 statement here is about [@terminal_obj (Sets^op) Sets_Initial] — the
 initial object of [Sets] as Structure/Initial.v defines it, by the
 notation [Initial C := @Terminal (C^op)] — so the two are about
 different terms and neither subsumes the other.

 Two arrows that differ are available from two places, and the choice
 costs a universe.  [Sets_empty_not_separates] uses
 Theory/Concrete.v's [Sets_two_arrows] (the identity against
 [Sets_negb], on that file's [bool_setoid_object]), and
 is polymorphic in the object universe.  [Sets_empty_not_separates_pick]
 uses instead Instance/Sets.v's [pick_true] against its
 [pick_false], the pair issue #447 named; that route is pinned at
 object universe [Set], and the pin is attributed by [About] rather
 than guessed — [About pick_true] reports [pick_true@{u}] with codomain
 [bool_setoid_object@{Set Set}], so Instance/Sets.v minimized that
 constant's object universe to [Set] at its own definition site (its
 carrier is [bool : Set]) and no annotation here can widen it.  Both
 constants are delivered; they are the same theorem at two universe
 strengths.

 UNIVERSES, MEASURED.  Every statement below is annotated, and the
 annotations are load-bearing.  Without them the elaborator minimizes
 the object universe of [Sets] to [Set]: an earlier revision of this
 file, identical but unannotated, gave
 [Sets_unit_separates@{u} : IsSeparator@{u u Set}
 unit_setoid_object@{Set Set}] under [Set Printing Universes], so the
 theorem held only for setoids whose carriers live in [Set].  As
 written it gives [Sets_unit_separates@{o so} : IsSeparator@{so so o}
 unit_setoid_object@{o o}] with [o < so], matching
 Theory/Concrete.v's [Sets_Separator@{o so}].

 One collapse is inherited and cannot be annotated away here:
 [About IsSeparator] reports [IsSeparator@{u u0 u1} : forall {C :
 Category@{u0 u1 u1}}, obj -> Type@{u}] — the hom and proof universes
 of the category are IDENTIFIED, where Theory/Category.v's own
 constraint is only [h <= p].  That is not a defect of the frozen
 interface: its model has it too ([About Cogenerator] gives
 [Cogenerator@{u u0 u1} : Category@{u0 u1 u1} -> Type…] at
 Adjunction/SAFT.v), and so does the prior art ([About Separator]
 gives [Separator@{u u0} : forall {C : Category@{u u0 u0}}, …] at
 Theory/Concrete.v).  Every statement in this file therefore
 carries [p = h].

 NOT DELIVERED HERE.  The joint-faithfulness characterization of the
 family form (Structure/Generator.v's [JointlyFaithful] against
 [Generator]) is the theory half of #447 and is not restated here; the
 single-object case of it is already Theory/Concrete.v's
 [Concrete_of_Separator] and [Separator_of_Faithful], and is only
 cited.  No claim is made that [Sets_Generator] and
 [Sets_terminal_Generator] are equal, isomorphic, or related as
 [Generator] records — only that each is a [Generator Sets].  Nothing
 here is said about generating SETS of more than one object in [Sets],
 nor about the size conditions (local presentability, Giraud's clause
 (vi)) that make separating sets useful; and the [Sets] subobject
 classifier's separating role is not touched. 

 --------
 [Sets] 的分隔符：单例、终端对象，以及那个不是一的对象

 nLab：https://ncatlab.org/nlab/show/separator
 nLab：https://ncatlab.org/nlab/show/well-pointed+categoryMac Lane，《为工作数学家准备的范畴》（Categories for the Working Mathematician），第2版（GTM 5），§V.7，第127页（PDF第136页），定义4为来源：当对于每一对平行箭头 h ≠ h'，集合中的某个成员 s 存在一个 f : s → c 使得 h ∘ f ≠ h' ∘ f 时，一个对象集合生成一个范畴。Mac Lane 的两个例子是集合的单点集和阿贝尔群的整数。Awodey，《范畴论》（Category Theory）（第1版，卡内基梅隆预印本，2005年9月），§7.2，第154页（PDF第163页），给出了单对象形式以及通过可表示函子的忠实性进行的表征；Riehl，《上下文中的范畴论》（Category Theory in Context），第2版，定义4.7.7，第177页（PDF第197页），给出了族形式并命名了对偶形式，她在结语 §E.4，第257页（PDF第277页），回忆了它作为Giraud定理的条款(vi)。此文件提供了 Mac Lane 的两个示例中的 [Sets] 一半，对应于 Structure/Generator.v 的 [IsSeparator] 和 [Generator]；另一半在 Instance/Ab/Generator.v 中，Instance/Grp/Generator.v 同时提供 Awodey 的群示例。RIEHL 的拼写是逆否命题。Riehl（和 Mac Lane）将条件写作 “f ≠ g 意味着存在某个 h 使得 f ∘ h ≠ g ∘ h”。在一个没有 ≈ 决策过程的 [Type] 值同态集中，这两种形式都不能相互推出：消去形式只能从 f ≉ g 得到 ¬∀，从不产生见证的 h，而否定形式只能从一致的测试中得到 ¬¬(f ≈ g)，从不推出 f ≈ g；当该同态集上的 ≈ 可判定时，它们才可以相互推导（本段较早的修改将否定形式称为“严格较弱”，但审计显示这种顺序在任何方向上都不成立）。Structure/Generator.v 因此说明了正消去律——所有的前组合一致意味着箭头一致——正如 Adjunction/SAFT.v 的 [Cogenerator] 说明它的对偶一样，下面的每个陈述都是这种形式。这里没有证明任何削弱的负形式，无论方向如何。

 先前技术及为何此文件不是重复。Issue #447 的“当前状态”段落指出，对 Generator/Separator/SeparatingFamily/Generates 的搜索恰好找到一个 [Cogenerator] 记录，并且“在任何地方都没有分离集合 / 分离器 / 生成族的定义”。这是陈旧的，纠正记录在此，而不是默默地绕过。Theory/Concrete.v 已经根据 Awodey 第1.5节 备注 1.7 的具体性阅读提到：- [Class Separator (t : C)]，一个只有一个字段的类，其字段 [separates] 遵循与 [IsSeparator] 相同的消去律；
 - [Concrete_of_Separator] 和 [Separator_of_Faithful] —— Awodey 等价的两个方向，并且 [fobj[Curried_Hom C] 的忠实性已被证明（Functor/Hom.v）；
 - [WellPointedCategory]，终对象的情况；
 - [Sets_Separator]，一个 [#[export] 实例，证明 [@terminal_obj Sets Sets_Terminal] 能区分 [Sets]，其探针为 [Sets_point]；
 - [Sets_empty_not_Separator]，作为非例子的空集合，使用 [empty_setoid_object]。所以 Awodey 的复选框“终结对象生成集合”这个问题，在这个文件存在之前就在 CLASS 词汇表中已经解决了。缺失的，以及这个文件补充的，是词汇表问题 #447 冻结 — [IsSeparator] 以及 Structure/Generator.v 的 [Generator] 记录中的相同内容 — SINGLETON 读取（与终结对象不同的对象，如下所述），[Generator] 包，以及沿两个对象之间同构的传递。两个词汇表通过 Structure/Generator/Concrete.v 的 [IsSeparator_of_Separator] 和 [Separator_of_IsSeparator] 在两个方向上建立了桥接，每个都是一行的重新包装，没有证明内容，因此没有被重复证明：class 和 [Definition] 是相同的定律，只是绑定形式不同。（这个文件的初稿包含了该桥对的副本以及它自己的同构传输引理，与理论部分并行构建；整合时保留了理论部分的 [separator_iso] 和桥并删除了副本。）

 单例和终对象是两个声明。这是一个测量，而不是警告。Instance/Sets.v 的 [unit_setoid_object] 是 [{| carrier := poly_unit ; is_setoid := unit_setoid |}]，一个空记录；Instance/Sets.v 的 [Sets_Terminal] 是一个 [Program Instance]，其 [terminal_obj] 字段是 [{| carrier := poly_unit |}]，集合等价关系字段保持为一个义务项。因此，这两个记录无法转换，并且在此文件的确切要求列表下

 示例 term_is_unit：
 @terminal_obj Sets Sets_Terminal = unit_setoid_object := eq_refl.

 会被拒绝，因为"术语 'eq_refl' 的类型为 '1 = 1'，而期望的类型是 '1 = unit_setoid_object'（无法统一 '1' 和 'unit_setoid_object'）。"

 一个转换拒绝 — [1] 是终对象符号，这也是该文件的导入列表为左侧启用的内容，因此消息在其环境中被引用。因此 [Sets_unit_separates] 和 [Sets_terminal_separates] 是独立定理，第二个定理不是通过 [eq_refl] 的识别从第一个定理获得的。有三条通向它的路径被记录，全部便宜且都在这里：1. 直接，这就是已提供的常量：[sets_elem_term]
 从终端对象本身构建常量映射，因此证明与单元素集合的证明相同，仅两行。
 2. 传输，[Sets_terminal_separates_by_transport]：两个对象是同构的（[Sets_terminal_unit_iso]），Structure/Generator.v 的 [separator_iso] 会将性质传递过去。记录这条路线是因为传输引理是可重复使用的一半——它使“是分隔器”成为同构类的一个不变量，而不是记录的一个不变量。
 3. 来自已有技术，[Sets_terminal_separates_from_Concrete]：
 通过桥拆包 Theory/Concrete.v 的 [Sets_Separator]。存在这一项是为了使上述陈旧性披露通过机器验证，而不是仅作为文字描述中的声明。这三者属于同一类型，并未声称它们是相等的项；[IsSeparator] 落在 [Type] 中，在那里证明无关性不可用，而比较其两个元素并不是该文件所作的陈述。空集范畴展示了什么，以及为什么它是一个定理。分离是一个真实的条件，证据是初始对象：Instance/Sets.v 的 [Sets_Initial] 以 [False] 作为载体，因此分离条件的每一个假设对它来说都是完全成立的，并且它会识别两个不同的箭头。[Sets_empty_not_separates] 将此陈述为 [IsSeparator … → False]。它是以正面方式陈述的，而不是像 Test/Probe*.v 收集的那种拒绝探针：这种探针记录的是 Elaborator 拒绝一个命令，而这是关于一个完全类型正确且只是没有元素的数学定理。探针习语无法表达它，这一区别很重要，因为这两种证据类型不可互换。Theory/Concrete.v 的 [Sets_empty_not_Separator] 证明了关于 ITS [empty_setoid_object] 的相同内容；这里的陈述是关于 [@terminal_obj (Sets^op) Sets_Initial] 的——根据 Structure/Initial.v 的定义，它是 [Sets] 的初始对象，通过记号 [Initial C := @Terminal (C^op)] ——所以两者涉及不同的项，互不包含。从两个地方可以获得两个不同的箭头，选择这个箭头会消耗一个宇宙。[Sets_empty_not_separates] 使用 Theory/Concrete.v 的 [Sets_two_arrows]（在该文件的 [bool_setoid_object] 上与 [Sets_negb] 的恒等映射），并且在对象宇宙中是多态的。[Sets_empty_not_separates_pick] 则使用 Instance/Sets.v 的 [pick_true] 对抗它的 [pick_false]，即配对问题 #447 命名的；这条路径固定在对象宇宙 [Set] 上，并且固定由 [About] 归因而不是猜测——[About pick_true] 报告 [pick_true@{u}] 的余域是 [bool_setoid_object@{Set Set}]，因此 Instance/Sets.v 将该常量的对象宇宙最小化为其定义地点的 [Set]（其承载者是 [bool : Set]），此处的任何注释都无法扩大它。两个常量都已提供；它们是在两个宇宙强度下的相同定理。宇宙，已测量。以下每个陈述都有注释，并且这些注释是承重的。没有它们，展开器会将 [Sets] 的对象宇宙最小化为 [Set]：这个文件的早期修订版，相同但没有注释，给出了 [Sets_unit_separates@{u} : IsSeparator@{u u Set} unit_setoid_object@{Set Set}] 在 [Set Printing Universes] 下，因此定理仅对载体存在于 [Set] 的集合等价类成立。按此写法，它给出了 [Sets_unit_separates@{o so} : IsSeparator@{so so o} unit_setoid_object@{o o}] 在 [o < so] 下，与 Theory/Concrete.v 的 [Sets_Separator@{o so}] 匹配。在这里有一个崩溃是继承来的，无法通过注释消除：
 [About IsSeparator] 报告 [IsSeparator@{u u0 u1} : forall {C : Category@{u0 u1 u1}}, obj -> Type@{u}] ——该类别的同态和证明宇宙被识别，其中 Theory/Category.v 自身的约束仅为 [h <= p]。这不是冻结接口的缺陷：它的模型也有这个问题（[About Cogenerator] 在 Adjunction/SAFT.v 中给出了 [Cogenerator@{u u0 u1} : Category@{u0 u1 u1} -> Type…]），以前的成果也是如此（[About Separator] 在 Theory/Concrete.v 中给出了 [Separator@{u u0} : forall {C : Category@{u u0 u0}}, …]）。因此，该文件中的每条语句都携带 [p = h]。此处未提供。家庭形式（Structure/Generator.v 中的 [JointlyFaithful] 对 [Generator] 的联合忠实特征）是 #447 的理论部分，这里未重述；它的单对象情况已经在 Theory/Concrete.v 的 [Concrete_of_Separator] 和 [Separator_of_Faithful] 中，并且仅被引用。未主张 [Sets_Generator] 和 [Sets_terminal_Generator] 相等、同构，或以 [Generator] 的记录方式相关——只是各自都是 [Generator Sets]。这里没有讨论在 [Sets] 中生成多个对象的集合，也没有讨论使分离集合有用的大小条件（局部可展现性，Giraud 条款 (vi)）；[Sets] 子对象分类器的分离角色也未涉及。
*)

(** ** The singleton separates / ** 单例分离 *)

(*
 A global element of [X], as a map out of the singleton setoid.  This is
 the same probe Instance/Sets.v's [injectivity_is_monic] uses to
 characterize monos as injections, and the same one
 Theory/Concrete.v's [Sets_point] uses out of the terminal object.

 It must stay TRANSPARENT, and that is measured: replacing this
 [Program Definition] by a tactic proof closed with [Qed], everything
 else unchanged, makes the next lemma's [exact] refuse with
 "The term "H (sets_elem x) ttt" has type "(f ∘ sets_elem x) ttt ≈
 (g ∘ sets_elem x) ttt" while it is expected to have type "f x ≈ g x"",
 a CONVERSION refusal: the whole proof is the reduction of the constant
 map at the unique inhabitant.  [sets_elem_term] below measures the
 same way, its message naming [1] where this one names
 [unit_setoid_object]. 

 --------
 [X] 的一个全局元素，作为从单例集同态出的映射。这与 Instance/Sets.v 中 [injectivity_is_monic] 用于将单射表征为注入的探针相同，也与 Theory/Concrete.v 中 [Sets_point] 从终对象使用的相同。

 它必须保持透明，这是可以测量的：用由 [Qed] 封闭的策略证明替换这个 [Program Definition]，而其它一切保持不变，会导致下一个引理的 [exact] 以“项 "H (sets_elem x) ttt" 的类型是 "(f ∘ sets_elem x) ttt ≈ (g ∘ sets_elem x) ttt"，而期望的类型是 "f x ≈ g x"” 拒绝，这是一次转换拒绝：整个证明是常数映射在唯一构成元上的化简。下面的 [sets_elem_term] 以相同方式测量，其消息命名 [1]，而这个则命名 [unit_setoid_object]。
*)
Program Definition sets_elem@{o so+} {X : SetoidObject@{o o}}
  (x : carrier X) :
  unit_setoid_object@{o o} ~{Sets@{o so}}~> X := {| morphism := fun _ => x |}.

(*
 Global elements distinguish setoid maps.  Two maps agreeing after every
 arrow out of the singleton agree at every element, because the element
 [x] is recovered as [sets_elem x] applied to the unique inhabitant of
 the singleton. 

 --------
 全局元素区分集族映射。两个映射在从单元素出发的每个箭头之后一致，就在每个元素上都一致，因为元素 [x] 可以通过将 [sets_elem x] 应用于单元素的唯一成员来恢复。
*)
Lemma Sets_unit_separates@{o so+} :
  @IsSeparator Sets@{o so} unit_setoid_object@{o o}.
Proof.
  intros X Y f g H x.
  exact (H (sets_elem x) ttt).
Qed.

(* Mac Lane's first example, as the one-object generating family. / 麦克莱恩的第一个例子，作为单对象生成族。 *)
Definition Sets_Generator@{o so+} : Generator Sets@{o so} :=
  @Generator_of_separator Sets@{o so} unit_setoid_object@{o o}
    Sets_unit_separates.

(** ** The terminal object separates / ** 终端对象分离 *)

(*
 The same constant map, but out of [Sets_Terminal]'s object rather than
 out of [unit_setoid_object].  It has to be built separately: the two
 objects do not convert, as the header measures. 

 --------
 相同的常量映射，但来自 [Sets_Terminal] 的对象，而不是来自 [unit_setoid_object]。它必须单独构建：这两个对象无法转换，正如头部所测量的。
*)
Program Definition sets_elem_term@{o so+} {X : SetoidObject@{o o}}
  (x : carrier X) :
  @terminal_obj Sets@{o so} Sets_Terminal@{so o} ~{Sets@{o so}}~> X :=
  {| morphism := fun _ => x |}.

(*
 Route 1, the delivered constant: the direct proof.  This is issue
 #447's pinned name. 

 --------
 路线1，已传递的常量：直接证明。这是问题#447的置顶名称。
*)
Lemma Sets_terminal_separates@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}).
Proof.
  intros X Y f g H x.
  exact (H (sets_elem_term x) ttt).
Qed.

Definition Sets_terminal_Generator@{o so+} : Generator Sets@{o so} :=
  @Generator_of_separator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    Sets_terminal_separates.

(*
 The isomorphism the transport route needs.  Both components are the
 constant map at [ttt], and both triangle laws hold by case analysis on
 the unique inhabitant.  Kept [Defined] because it is DATA; closing it
 with [Qed] was measured to compile, nothing in this file needing it
 transparent, but opaque data blocks downstream conversion and
 Instance/Sets.v keeps its own coherence isomorphisms [Defined] for the
 same reason. 

 --------
 传输路线所需的同构。两个组成部分都是在 [ttt] 上的常量映射，并且通过对唯一元素的情况分析，两条三角律都成立。保留了 [Defined] 因为它是数据；用 [Qed] 关闭它经过测量可以编译，这个文件中没有任何地方需要它透明，但不透明数据会阻塞下游转换，并且 Instance/Sets.v 出于同样的原因保留了自己的相干同构 [Defined]。
*)
Definition Sets_terminal_unit_iso@{o so+} :
  @Isomorphism Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o})
    unit_setoid_object@{o o}.
Proof.
  unshelve refine {| to := _; from := _ |}.
  - unshelve refine {| morphism := fun _ => ttt |}; proper.
  - unshelve refine {| morphism := fun _ => ttt |}; proper.
  - intro u; now destruct u.
  - intro u; now destruct u.
Defined.

(*
 Route 2: transport along that isomorphism, in the direction
 [unit_setoid_object ≅ terminal_obj], through Structure/Generator.v's
 [separator_iso]. 

 --------
 路线 2：沿着该同构传输，方向为 [unit_setoid_object ≅ terminal_obj]，通过 Structure/Generator.v 的 [separator_iso]。
*)
Definition Sets_terminal_separates_by_transport@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) :=
  separator_iso Sets_unit_separates (iso_sym Sets_terminal_unit_iso).

(*
 Route 3: the prior art, unpacked through Structure/Generator/
 Concrete.v's bridge.  This constant exists so that the header's claim
 about Theory/Concrete.v is checked by the compiler rather than
 asserted. 

 --------
 路线 3：通过 Structure/Generator/Concrete.v 的桥接拆解已有技术。这个常量的存在是为了让编译器检查关于 Theory/Concrete.v 的头文件声明，而不是通过断言来检查。
*)
Definition Sets_terminal_separates_from_Concrete@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) :=
  IsSeparator_of_Separator
    (@terminal_obj Sets@{o so} Sets_Terminal@{so o}) Sets_Separator@{o so}.

(* * ** The initial object does not separate / * ** 初始对象没有分离 *)

(*
 A theorem, not a refusal: the statement is well typed and has no
 inhabitant.  There is nothing to probe with out of the empty setoid,
 so the hypothesis is vacuous and would identify the identity of the
 two-element setoid with negation. 

 --------
 一个定理，而不是拒绝：该陈述类型良好且没有元素。空集合等价类中没有任何东西可供探查，因此假设是空的，并且会将二元集合等价类的恒等与否定联系起来。
*)
Lemma Sets_empty_not_separates@{o so+} :
  @IsSeparator Sets@{o so}
    (@terminal_obj (Sets@{o so}^op) Sets_Initial@{so o}) → False.
Proof.
  intro Hsep.
  apply Sets_two_arrows@{o so}.
  apply Hsep.
  intros k u; destruct u.
Qed.

(*
 The same theorem by the route issue #447 named, and pinned at object
 universe [Set] by its donors, as the header attributes. 

 --------
 由捐赠者在对象宇宙 [Set] 上命名并固定的路由问题 #447 的同一理论，如标题属性所示。
*)
Lemma Sets_empty_not_separates_pick@{so+} :
  @IsSeparator Sets@{Set so}
    (@terminal_obj (Sets@{Set so}^op) Sets_Initial@{so Set}) → False.
Proof.
  intro Hsep.
  apply Bool.diff_true_false.
  refine (Hsep unit_setoid_object@{Set Set} _ pick_true pick_false _ ttt).
  intros k u; destruct u.
Qed.
