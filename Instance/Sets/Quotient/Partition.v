Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Quotient.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Lib.v sets [Default Proof Using “Type”], which keeps only the section
 variables occurring in a statement.  Every statement below mentions the
 section's R, HR and HC only THROUGH [sets_part_pred] and [SetsParts],
 which are section-local definitions and so do not register as syntactic
 occurrences; “All” is the precedent of Theory/EckmannHilton.v and
 Theory/Category/Monoid.v. 

 --------
 Lib.v 设置了 [Default Proof Using “Type”]，它只保留出现在语句中的节变量。下面的每个语句仅通过 [sets_part_pred] 和 [SetsParts] 提到节的 R、HR 和 HC，这些都是节本地定义，因此不会被记录为语法出现；“All” 是 Theory/EckmannHilton.v 和 Theory/Category/Monoid.v 的前置内容。
*)
#[local] Set Default Proof Using "All".

(** * The quotient as a set of parts / * 商作为部分的集合 *)

(*
 nLab:      https://ncatlab.org/nlab/show/partition
 nLab:      https://ncatlab.org/nlab/show/quotient+set
 Wikipedia: https://en.wikipedia.org/wiki/Equivalence_class
 Wikipedia: https://en.wikipedia.org/wiki/Partition_of_a_set

 Fong and Spivak, “Seven Sketches in Compositionality”, §1.2.1
 definition 1.21 (printed p. 10): the quotient of a set by an
 equivalence relation IS the set of PARTS of the corresponding
 partition.  Instance/Sets/Quotient.v gives the other presentation --
 the same carrier under a coarser equality -- and this file builds the
 book's and compares the two.

 The comparison is not a formality, and the whole interest of the file
 is in what it costs.  Three separate things are true, and they are
 kept apart below because conflating any two of them would misstate the
 result.

 (1) THE UNTRUNCATED CLASS OBJECT DOES NOT EXIST AT THE RIGHT LEVEL.
 In this library `≈` is [crelation]-valued, so the class of a is
 naturally the TYPE-valued predicate x ↦ R a x.  But
 [obj[Sets@{o so}]] is [SetoidObject@{o o}], which identifies a
 setoid's carrier and relation universes, and
 [carrier A → Type@{o}] has type [Type@{o+1}].  So the untruncated
 class object is not an object of the [Sets] that A lives in; it is
 one of the next [Sets] up.  This is a genuine universe
 inconsistency and Test/ProbeSetsQuotient.v pins it, with two
 positive controls -- the truncated carrier at the same level, and
 the untruncated one a level up.  It is the same wall
 Instance/Sets/Powerset.v (#227) reports for [Powerset_obj], met
 from the other side, and this file's [SetsParts] uses that file's
 [Powerset_Prop_obj] rather than rebuilding a subset object.

 (2) TRUNCATION MAKES THE OBJECT EXIST, AND CLASSIFICATION STILL
 HOLDS -- UP TO TRUNCATION.  Taking the class of a to be
 x ↦ ‖R a x‖, with [Powerset_squash] the impredicative truncation
 Powerset.v already uses, puts the class object back at the level
 of the carrier.  [sets_part_of] is then available under EXACTLY
 the hypotheses the quotient itself takes -- R an equivalence,
 coarser than `≈` -- with no stability assumed; and it is
 surjective ([sets_part_of_surjective]) and separates points up to
 truncation ([sets_part_of_squash]).  What is NOT available is the
 last step out of the truncation, since ‖R a b‖ is a [Prop] and
 R a b need not be.

 (3) THE HYPOTHESIS THAT CLOSES THE GAP IS EXACTLY THE CONCLUSION.
 [SquashStable R] -- that ‖R x y‖ implies R x y -- gives the
 isomorphism ([sets_partition_iso]); and conversely injectivity of
 [sets_part_of] gives back [SquashStable R]
 ([partition_stability_is_the_conclusion] -- the name is prefixed
 because the tree already carries TWO constants called
 [stability_is_the_conclusion], at Instance/Grp/Epi.v and
 Instance/Field.v).  So no cheaper hypothesis exists,
 which is the discipline Instance/Grp/Epi.v and Instance/Field.v
 use for their constructive stratifications.  A [Prop]-valued R is
 squash-stable ([prop_rel_squash_stable]), by instantiating the
 impredicative quantifier at R x y itself; and Seven Sketches'
 classical setting is exactly the [Prop]-valued one, so the book's
 identification is recovered there with nothing extra assumed. 

 --------
 nLab:       https://ncatlab.org/nlab/show/partition 
 nLab:       https://ncatlab.org/nlab/show/quotient+set 
 维基百科:  https://en.wikipedia.org/wiki/Equivalence_class 
 维基百科:  https://en.wikipedia.org/wiki/Partition_of_a_set 

 Fong 和 Spivak，《组合性的七个概述》，§1.2.1
 定义 1.21（印刷第 10 页）：一个集合关于等价关系的商 集就是相应划分的部分的集合。Instance/Sets/Quotient.v 给出了另一种表示 —— 在更粗糙的等式下相同的承载体 —— 这个文件构建了书中的内容并比较了两者。

 这种比较不是形式性的，整个文件的兴趣在于它的代价。三个独立的事实是正确的，并且它们在下面被分开，因为混淆其中任何两个会造成结果表达错误。(1) 未截断的类对象在正确的层次上不存在。在这个库中，`≈` 的值为 [crelation]，因此 a 的类自然而然是 TYPE 值的谓词 x ↦ R a x。但 [obj[Sets@{o so}] 是 [SetoidObject@{o o}]，它标识了集合及其关系的宇宙，而 [carrier A → Type@{o}] 的类型是 [Type@{o+1}]。因此，未截断的类对象不是 A 所在的 [Sets] 的对象；它属于上一个 [Sets] 级别。这是真正的宇宙不一致性，Test/ProbeSetsQuotient.v 将其固定，有两个正向控制——同一层次的截断载体，以及上一层次的未截断对象。它是同一面墙
 Instance/Sets/Powerset.v (#227) 为 [Powerset_obj] 报告，
 从另一侧遇到，而这个文件的 [SetsParts] 使用了那个文件的
 [Powerset_Prop_obj]，而不是重新构建一个子集对象。(2) 截断使对象存在，并且分类仍然成立——直到截断为止。将 a 的类记作 x ↦ ‖R a x‖，其中 [Powerset_squash] 是 Powerset.v 已经使用的不可归纳截断，将类对象放回承载层。然后 [sets_part_of] 可以在完全相同的假设下使用——商本身所接受的假设——R 是等价关系，比 `≈` 更粗——且不假设稳定性；并且它是满射的（[sets_part_of_surjective]）并且在截断下区分点（[sets_part_of_squash]）。不可用的是截断的最后一步，因为 ‖R a b‖ 是 [Prop]，而 R a b 不必是。(3) 弥补差距的假设正是结论。[SquashStable R] -- 表示 ‖R x y‖ 蕴含 R x y -- 给出了同构 ([sets_partition_iso])；反过来，[sets_part_of] 的单射性也可以恢复 [SquashStable R] ([partition_stability_is_the_conclusion] -- 这个名字加了前缀，因为该树中已经有两个叫 [stability_is_the_conclusion] 的常量，分别在 Instance/Grp/Epi.v 和 Instance/Field.v)。所以不存在更简洁的假设，这是 Instance/Grp/Epi.v 和 Instance/Field.v 在进行构造性分层时所使用的规范。一个 [Prop] 值的 R 是 squash-stable ([prop_rel_squash_stable])，通过在 R x y 自身上实例化不可依赖量词；而《Seven Sketches》的经典设置正是 [Prop] 值的情况，因此书中的同一性在那里得以恢复，无需额外假设。
*)

(*
 Two presentations of a quotient, and why a library has to choose

 Text:  Fong and Spivak, “Seven Sketches in Compositionality”, CUP
 2019, §1.2.1
 Text:  Bishop, “Foundations of Constructive Analysis”, McGraw-Hill 1967
 Paper: Hofstra and Warren, “Combinatorial realizability models of type
 theory”, APAL 164(10) 2013
 Paper: Barthe, Capretta, Pons, “Setoids in type theory”, JFP 13(2) 2003

 Classically the two presentations are interchangeable and textbooks
 move between them without comment: a quotient is a set of classes, and
 a class is named by any of its members.  What breaks the symmetry in
 type theory is that “the set of classes” is a set of SUBSETS, and the
 power set is a universe-raising operation, while “the same set with a
 coarser equality” raises nothing.  The library's design (stated at
 Instance/Sets.v) takes the second reading for exactly this reason,
 and every quotient in the tree follows it -- the hom-congruence
 quotient of Construction/Quotient.v, the group and module quotients of
 Instance/Grp/Quotient.v and Instance/Mod/Quotient.v, and
 Instance/Sets/Quotient.v.

 The class reading is nevertheless not a mere alternative notation, and
 this file is where the difference is visible.  It survives at all only
 because [Prop] is impredicative in Coq, so a truncated subset stays at
 the level of the carrier; and once truncated it cannot be untruncated,
 so the passage back to a representative is the step that has to be
 paid for.  Payment is [SquashStable], and Fong and Spivak's setting
 pays it for free by working with [Prop]-valued relations throughout.

 One thing this file does NOT do is decide whether the setoid reading
 is “the right one”.  It shows what each costs and where they agree. 

 --------
 商的两种表示方式，以及为什么一个库必须作出选择

 书籍：Fong 和 Spivak，《组合性七个草图》，CUP 2019，第1.2.1节
 书籍：Bishop，《构造性分析基础》，McGraw-Hill 1967
 论文：Hofstra 和 Warren，《类型理论的组合可实现性模型》，APAL 164(10) 2013
 论文：Barthe, Capretta, Pons，《类型理论中的集合类》，JFP 13(2) 2003从经典上看，这两种呈现方式是可以互换的，教科书在两者之间切换时通常没有评论：商集合是类的集合，而一个类可以由其任意一个成员来命名。在类型理论中打破对称性的是，“类的集合”是子集的集合，并且幂集是一个提升宇宙的操作，而“用更粗糙的等式表示的相同集合”不会提升任何东西。库的设计（在 Instance/Sets.v 中说明）正是基于这个原因采用第二种解释，并且树中的每一个商集合都遵循它——Construction/Quotient.v 中的同态一致商，Instance/Grp/Quotient.v 和 Instance/Mod/Quotient.v 中的群与模的商，以及 Instance/Sets/Quotient.v。然而，类的阅读并不仅仅是一个替代的符号表示，这个文件正是显示差异的地方。它之所以能够存在，完全是因为在 Coq 中 [Prop] 是自指的，所以截断后的子集仍然停留在载体的层次；一旦截断，它就无法恢复原状，因此返回到代表元素的步骤是必须付出的代价。这个代价就是 [SquashStable]，而 Fong 和 Spivak 的方法通过始终使用 [Prop] 值的关系免费地支付了这个代价。

 这个文件没有做的一件事是决定集合论的阅读是否是“正确的”。它展示了每种方法的代价以及它们在哪些方面一致。
*)

(*
 WHAT IS DELIVERED

 * [sets_part_pred], the truncated class of an element as an object of
 Instance/Sets/Powerset.v's [Powerset_Prop_obj A] -- a `≈`-respecting
 [Prop]-valued predicate, so a subset of A in that file's sense, not a
 new notion of subset invented here.

 * That the classes are a PARTITION, proved rather than assumed:
 [sets_part_mem_self] (every element lies in its own class) and
 [sets_part_shared_elem] (two classes sharing an element are equal).

 * [SetsParts A R], the set of parts, and [sets_part_of], the class map
 out of the coarsening quotient.  Both take the quotient's own two
 hypotheses and NOTHING MORE -- in particular no stability -- and
 [sets_part_of] is surjective and separates up to truncation.

 * [SquashStable] and the three results that pin it: it suffices
 ([sets_partition_iso], an isomorphism in [Sets]), it is necessary
 ([partition_stability_is_the_conclusion], a biconditional against injectivity
 of [sets_part_of]), and it is free for a [Prop]-valued relation
 ([prop_rel_squash_stable]).

 * [SetsPartsProp A R], the object with the class-hood witness itself
 truncated -- literally a sub-setoid of [Powerset_Prop_obj A], with no
 representative carried -- together with the comparison map
 [sets_parts_forget].  This is included because it, and not
 [SetsParts], is what “the set of parts” says when read strictly, and
 because the difference between the two is exactly the constructive
 content.

 WHAT IS NOT DELIVERED

 * NO INVERSE TO [sets_parts_forget].  Recovering a representative from
 a truncated existence witness is large elimination out of [Prop],
 which is not available; no impossibility is proved here either, and
 in particular no theorem says that no OTHER map back exists.  The
 statement is that this map is not invertible by the evident
 candidate.

 * NO CLAIM THAT [SquashStable] IS UNAVOIDABLE FOR SOME OTHER
 PRESENTATION.  [partition_stability_is_the_conclusion] is about [sets_part_of];
 it says nothing about class maps built differently.

 * NO UNTRUNCATED CLASS OBJECT, at any level.  The one-level-up object
 is exhibited only inside Test/ProbeSetsQuotient.v, as the positive
 control for the universe measurement, and nothing is built over it.

 * NO PARTITION AS A FIRST-CLASS STRUCTURE.  There is no record of
 “partitions of A”, no inverse assignment from partitions to
 relations, and hence no bijection between the two -- Seven Sketches'
 §1.2.1 sets that correspondence up, and only the direction from a
 relation to its parts is formalized here.

 STATUS: axiom-free.  36 named constants, no [Program] obligations, all
 reporting “Closed under the global context”; the Makefile's
 [print-assumptions] target audits fourteen of them. 

 --------
 交付内容

 * [sets_part_pred]，作为 Instance/Sets/Powerset.v 中 [Powerset_Prop_obj A] 的对象的元素的截断类——一个 `≈`-尊重的 [Prop] 值谓词，因此是该文件意义下的 A 的子集，而不是这里发明的新子集概念。

 * 类是一个划分（PARTITION），这是被证明的而非假设的：[sets_part_mem_self]（每个元素位于它自己的类中）和 [sets_part_shared_elem]（两个共享元素的类相等）。

 * [SetsParts A R]，部分集合，以及 [sets_part_of]，共分映射出于粗化商。两者都只采用商本身的两个假设而没有其他——特别是不依赖稳定性——并且 [sets_part_of] 是满射的，并且在截断意义下可区分。* [SquashStable] 以及固定它的三个结果：它是充分的  
 （[sets_partition_iso]，[Sets] 中的同构），它是必要的  
 （[partition_stability_is_the_conclusion]，相对于 [sets_part_of] 的单射性双条件），并且它对于 [Prop] 值的关系是自由的  
 （[prop_rel_squash_stable]）。

 * [SetsPartsProp A R]，自身作为类的存在见证被截断——字面上是 [Powerset_Prop_obj A] 的一个子子集，且没有携带代表——以及比较映射  
 [sets_parts_forget]。之所以包括它，是因为它，而不是 [SetsParts]，当严格阅读时才表示“部分的集合”，并且两者之间的差异恰好是构造内容。

 未交付的内容* [sets_parts_forget] 没有逆。 从截断存在证明中恢复一个代表是从 [Prop] 中进行的大消去，这是不可用的；这里也没有证明任何不可能性，特别是没有定理表明不存在其他的回到原映射。 该说法是这个映射通过显而易见的候选对象不可逆。

 * 没有声称 [SquashStable] 对某些其他呈现是不可避免的。 [partition_stability_is_the_conclusion] 关于 [sets_part_of]； 它没有涉及用不同方式构建的类映射。

 * 没有未截断的类对象，在任何层级都是如此。 上一级对象仅在 Test/ProbeSetsQuotient.v 内展示，作为宇宙测度的阳性控制，没有在其上构建任何内容。* 没有将分区作为一等结构。没有“A 的分区”的记录，也没有从分区到关系的逆向分配，因此两者之间没有双射 —— 《七个草图》第 §1.2.1 节建立了这种对应关系，这里仅正式化了从关系到其部分的方向。

 状态：无公理。36 个命名常量，没有 [Program] 义务，全部报告“在全局上下文中封闭”；Makefile 的 [print-assumptions] 目标审核了其中的十四个。
*)

Section Partition.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).
Context (HR : Equivalence R).
Context (HC : SetoidCoarser R).

(* * ** The class of an element, as a subset / * ** 元素的类，作为一个子集 *)

(*
 The truncated class.  [Powerset_squash] (Instance/Sets/Powerset.v) is
 the impredicative truncation ∀ Q : Prop, (A → Q) → Q; applying it is
 what keeps the predicate [Prop]-valued and hence keeps the whole
 construction at the carrier's universe. 

 --------
 截断类。[Powerset_squash]（实例/集合/幂集.v）是自反截断 ∀ Q : Prop, (A → Q) → Q；应用它可以使谓词 [Prop] 保持取值，因此保持整个构造在承载体的宇宙中。
*)
Definition sets_part_pred (a : carrier A) : carrier (Powerset_Prop_obj A).
Proof.
  unshelve refine
    (@Build_SetoidMorphism (carrier A) (is_setoid A) Prop
       (is_setoid Powerset_Prop_truth)
       (fun x => Powerset_squash (R a x)) _).
  intros x x' Hxx'; split; intros H Q k; apply H; intro w; apply k.
  - transitivity x; [ exact w | exact (HC x x' Hxx') ].
  - transitivity x'; [ exact w | exact (HC x' x (symmetry Hxx')) ].
Defined.

(* Membership in one's own class, and the class of an R-related element: the two facts that make the classes a partition. / 属于自身的类，以及属于R相关元素的类：这两个事实使得这些类成为一个划分。 *)
Lemma sets_part_mem_self (a : carrier A) : sets_part_pred a a.
Proof. exact (Powerset_squash_intro (Equivalence_Reflexive a)). Qed.

Lemma sets_part_mem_of (a x : carrier A) (w : R a x) : sets_part_pred a x.
Proof. exact (Powerset_squash_intro w). Qed.

(*
 Two classes that share an element are equal.  This is the second half
 of “the classes partition A”; note that the shared element's
 membership witnesses arrive truncated, and the conclusion is an
 equality of [Prop]-valued predicates, so both are eliminated into a
 [Prop] and no untruncation is needed. 

 --------
 共享一个元素的两个类是相等的。这是“类划分A”的后半部分；注意，共享元素的成员资格证据是截断的，并且结论是一个 [Prop] 值谓词的相等性，因此两者都被消解为 [Prop]，并且不需要取消截断。
*)
Lemma sets_part_shared_elem (a b c : carrier A)
  (Ha : sets_part_pred a c) (Hb : sets_part_pred b c) :
  @equiv _ (Powerset_Prop_obj A) (sets_part_pred a) (sets_part_pred b).
Proof.
  intro x; split; intro H.
  - apply Ha; intro wac; apply Hb; intro wbc; apply H; intro wax; clear H.
    apply Powerset_squash_intro.
    transitivity a; [ | exact wax ].
    transitivity c; [ exact wbc | exact (symmetry wac) ].
  - apply Ha; intro wac; apply Hb; intro wbc; apply H; intro wbx; clear H.
    apply Powerset_squash_intro.
    transitivity b; [ | exact wbx ].
    transitivity c; [ exact wac | exact (symmetry wbc) ].
Qed.

(* Classes of R-related elements coincide. / R 相关元素的类重合。 *)
Lemma sets_part_pred_respects (a b : carrier A) (w : R a b) :
  @equiv _ (Powerset_Prop_obj A) (sets_part_pred a) (sets_part_pred b).
Proof.
  exact (sets_part_shared_elem a b b (sets_part_mem_of a b w)
           (sets_part_mem_self b)).
Qed.

(* * ** The set of parts, with a representative carried / * ** 一组零件，带有一个携带的代表 *)

(*
 An element is a subset of A together with an element it is the class
 of.  The representative is DATA -- the library's `∃` is [sigT] -- and
 the setoid IGNORES it, comparing only the subsets.  That is what makes
 this the set of parts rather than the set of pointed parts, and it is
 also exactly what makes the map back to the coarsening quotient
 writable at all; [SetsPartsProp] below is the same object with the
 representative truncated away, and there the EVIDENT map back -- take
 the representative -- cannot be written, since that would be large
 elimination out of [Prop].  Nothing here says no OTHER map back
 exists. 

 --------
 一个元素是 A 的一个子集以及它所属于的类。代表是 DATA —— 库中的 `∃` 是 [sigT] —— 而集合类型忽略它，仅比较子集。这就是它成为部分集合而不是带指向元素的部分集合的原因，同时这也正是使得回到粗化商的映射可写的原因；下面的 [SetsPartsProp] 是同样的对象，只是代表被截断了，在那里明显的回映射——取代表——不能被写出，因为那将是从 [Prop] 的大型消去。这里没有说明不存在其他回映射。
*)
Definition sets_parts_carrier : Type :=
  { P : carrier (Powerset_Prop_obj A)
      & { a : carrier A & @equiv _ (Powerset_Prop_obj A) P (sets_part_pred a) } }.

Definition sets_parts_equiv : crelation sets_parts_carrier :=
  fun S T => @equiv _ (Powerset_Prop_obj A) (`1 S) (`1 T).

Lemma sets_parts_equivalence : Equivalence sets_parts_equiv.
Proof.
  unfold sets_parts_equiv; constructor.
  - intro S; reflexivity.
  - intros S T H; now symmetry.
  - intros S T U H1 H2; now transitivity (`1 T).
Qed.

Definition SetsParts : SetoidObject :=
  {| carrier := sets_parts_carrier ;
     is_setoid := {| equiv := sets_parts_equiv ;
                     setoid_equiv := sets_parts_equivalence |} |}.

(** ** The class map / ** 类映射 *)

(*
 Defined for an ARBITRARY [crelation]-valued R: no stability is needed
 to send an element to its class. 

 --------
 对于任意 [crelation] 值的 R 定义：发送一个元素到其类不需要稳定性。
*)
(* The class of [a], with [a] itself as the carried representative. / [a] 的类别，以 [a] 本身作为携带的代表。 *)
Definition sets_part_elt (a : carrier A) : sets_parts_carrier.
Proof.
  unshelve refine
    (existT (fun P : carrier (Powerset_Prop_obj A) =>
               { b : carrier A
                   & @equiv _ (Powerset_Prop_obj A) P (sets_part_pred b) })
       (sets_part_pred a)
       (existT (fun b : carrier A =>
                  @equiv _ (Powerset_Prop_obj A) (sets_part_pred a)
                    (sets_part_pred b)) a _)).
  reflexivity.
Defined.

Definition sets_part_of : SetsQuotient A R HR ~{Sets}~> SetsParts.
Proof.
  unshelve refine
    (@Build_SetoidMorphism (carrier A) (is_setoid (SetsQuotient A R HR))
       sets_parts_carrier (is_setoid SetsParts) sets_part_elt _).
  intros a b w; exact (sets_part_pred_respects a b w).
Defined.

(* Every part is the class of its own representative, so [sets_part_of] is surjective -- and the preimage is produced, not merely asserted to exist. / 每一部分都是其自身代表的类，所以 [sets_part_of] 是满射——并且原像是被构造出来的，而不仅仅是被断言存在。 *)
Lemma sets_part_of_surjective (S : carrier SetsParts) :
  @equiv _ SetsParts (sets_part_of (`1 (`2 S))) S.
Proof.
  intro x; split; intro H.
  - exact (proj2 (`2 (`2 S) x) H).
  - exact (proj1 (`2 (`2 S) x) H).
Qed.

(*
 ... and it separates points UP TO TRUNCATION.  Evaluating the equality
 of classes at [a] turns reflexivity of R into ‖R b a‖, and symmetry
 inside the truncation gives ‖R a b‖; the last step out is what is not
 available. 

 --------
 ... 它将点分开直到截断。 在 [a] 处评估类的相等性会将 R 的自反性转化为 ‖R b a‖，而截断内的对称性则给出 ‖R a b‖；最后一步是无法获得的。
*)
Lemma sets_part_of_squash (a b : carrier A)
  (H : @equiv _ SetsParts (sets_part_of a) (sets_part_of b)) :
  Powerset_squash (R a b).
Proof.
  assert (Hba : Powerset_squash (R b a))
    by exact (proj1 (H a) (sets_part_mem_self a)).
  intros Q k; apply Hba; intro w; apply k; exact (symmetry w).
Qed.

(* * ** The hypothesis that closes the gap, and that it is the conclusion / * ** 缩小差距的假设，以及它就是结论 *)

Definition SquashStable : Type :=
  ∀ x y : carrier A, Powerset_squash (R x y) → R x y.

(*
 A [Prop]-valued relation is squash-stable: instantiate the
 impredicative quantifier at the proposition itself. 

 --------
 一个 [Prop] 值关系是压缩稳定的：在命题本身上实例化自反量化器。
*)
Lemma prop_rel_squash_stable (Rp : carrier A -> carrier A -> Prop)
  (HRel : ∀ x y : carrier A, R x y ↔ Rp x y) : SquashStable.
Proof.
  intros x y H.
  apply (snd (HRel x y)).
  exact (H (Rp x y) (fun w => fst (HRel x y) w)).
Qed.

(*
 Stability is exactly injectivity of the class map.  Backwards is
 [sets_part_of_squash]; forwards, a truncated R x y already forces the
 two classes to agree, because the goal at each point is a [Prop] and
 so the truncation may be eliminated into it. 

 --------
 稳定性恰好是类映射的单射性。向后是 [sets_part_of_squash]；向前，一个截断的 R x y 已经迫使两个类一致，因为每个点的目标是 [Prop]，因此截断可以被消除到其中。
*)
Lemma squash_stable_injective (HS : SquashStable) (a b : carrier A)
  (H : @equiv _ SetsParts (sets_part_of a) (sets_part_of b)) : R a b.
Proof. exact (HS a b (sets_part_of_squash a b H)). Qed.

(*
 Two moves inside the truncation, isolated so that the statements are
 about [Powerset_squash] rather than about [sets_part_of]'s first
 projection -- which spares every use site a reduction step.  Both are
 eliminations of a truncation into a [Prop] goal, which is exactly what
 impredicative truncation permits. 

 --------
 在截断内部的两步操作是孤立的，因此这些语句是关于 [Powerset_squash] 的，而不是关于 [sets_part_of] 的第一个投影——这为每个使用点省去了一个约简步骤。这两者都是将截断消除为 [Prop] 目标的操作，这正是任意归纳截断所允许的。
*)
Lemma squash_rel_sym (x y : carrier A) (H : Powerset_squash (R x y)) :
  Powerset_squash (R y x).
Proof. intros Q k; apply H; intro w; apply k; exact (symmetry w). Qed.

Lemma squash_rel_shift (x y z : carrier A) (H : Powerset_squash (R x y))
  (Hz : Powerset_squash (R x z)) : Powerset_squash (R y z).
Proof.
  intros Q k; apply H; intro wxy; apply Hz; intro wxz; apply k.
  transitivity x; [ exact (symmetry wxy) | exact wxz ].
Qed.

Lemma injective_squash_stable
  (Hinj : ∀ a b : carrier A,
     @equiv _ SetsParts (sets_part_of a) (sets_part_of b) → R a b) :
  SquashStable.
Proof.
  intros x y H.
  apply Hinj.
  intro z; split; intro Hz.
  - exact (squash_rel_shift x y z H Hz).
  - exact (squash_rel_shift y x z (squash_rel_sym x y H) Hz).
Qed.

Theorem partition_stability_is_the_conclusion :
  SquashStable ↔
  (∀ a b : carrier A,
     @equiv _ SetsParts (sets_part_of a) (sets_part_of b) → R a b).
Proof.
  split.
  - exact squash_stable_injective.
  - exact injective_squash_stable.
Qed.

(* * ** Seven Sketches §1.2.1: the two presentations agree / * ** 七个素描 §1.2.1：两个表述一致 *)

Definition sets_part_rep (HS : SquashStable) :
  SetsParts ~{Sets}~> SetsQuotient A R HR.
Proof.
  unshelve refine
    (@Build_SetoidMorphism sets_parts_carrier (is_setoid SetsParts)
       (carrier A) (is_setoid (SetsQuotient A R HR))
       (fun S => `1 (`2 S)) _).
  intros S T HST.
  apply (squash_stable_injective HS).
  assert (Hpred : @equiv _ (Powerset_Prop_obj A)
                    (sets_part_pred (`1 (`2 S))) (sets_part_pred (`1 (`2 T)))).
  { transitivity (`1 S); [ symmetry; exact (`2 (`2 S)) | ].
    transitivity (`1 T); [ exact HST | exact (`2 (`2 T)) ]. }
  exact Hpred.
Defined.

(* THE STATEMENT: the coarsening quotient and the set of parts are isomorphic in [Sets], under stability and nothing else. / 陈述：在稳定性且没有其他条件下，粗化商和部分集合在 [Sets] 中是同构的。 *)
Definition sets_partition_iso (HS : SquashStable) :
  @Isomorphism Sets (SetsQuotient A R HR) SetsParts.
Proof.
  unshelve refine {| to := sets_part_of ; from := sets_part_rep HS |}.
  - intro S; exact (sets_part_of_surjective S).
  - intro a; exact (Equivalence_Reflexive a).
Defined.

(* The class map is the isomorphism's forward leg on the nose. / 类映射正是同构的前向部分。 *)
Example sets_partition_iso_to (HS : SquashStable) :
  to (sets_partition_iso HS) = sets_part_of.
Proof. reflexivity. Qed.

(* ... and the backward leg is “take the carried representative”, again on the nose. / ... 而后退的那条腿是“接过被携带的代表”，再次正中目标。 *)
Example sets_partition_iso_from (HS : SquashStable) (S : carrier SetsParts) :
  from (sets_partition_iso HS) S = `1 (`2 S).
Proof. reflexivity. Qed.

(* * ** The strict reading: parts with no representative / * **严格解读：没有代表的部分 *)

(*
 “The set of parts” read strictly is a SUB-SETOID of the power set --
 the subsets that are classes -- with no representative attached.  It
 exists at the right universe because the class-hood witness is
 truncated too. 

 --------
 “部分的集合”严格来说是幂集的一个子类 —— 这些子集是类 —— 没有附加代表。它存在于正确的宇宙中，因为类的证明也被截断了。
*)
Definition sets_parts_prop_carrier : Type :=
  { P : carrier (Powerset_Prop_obj A)
      & Powerset_squash
          { a : carrier A
              & @equiv _ (Powerset_Prop_obj A) P (sets_part_pred a) } }.

Definition sets_parts_prop_equiv : crelation sets_parts_prop_carrier :=
  fun S T => @equiv _ (Powerset_Prop_obj A) (`1 S) (`1 T).

Lemma sets_parts_prop_equivalence : Equivalence sets_parts_prop_equiv.
Proof.
  unfold sets_parts_prop_equiv; constructor.
  - intro S; reflexivity.
  - intros S T H; now symmetry.
  - intros S T U H1 H2; now transitivity (`1 T).
Qed.

Definition SetsPartsProp : SetoidObject :=
  {| carrier := sets_parts_prop_carrier ;
     is_setoid := {| equiv := sets_parts_prop_equiv ;
                     setoid_equiv := sets_parts_prop_equivalence |} |}.

(*
 Forgetting the representative.  This map exists unconditionally; what
 does not exist is the evident inverse, which would have to produce a
 representative from a truncated existence witness -- large elimination
 out of [Prop].  No impossibility is claimed, only that this candidate
 is unavailable. 

 --------
 忘记代表。这个映射是无条件存在的；不存在的是明显的逆映射，它必须从一个被截断的存在证明中产生一个代表 —— 从 [Prop] 中进行大消去。并不是说这是不可能的，只是这个候选不可用。
*)
Definition sets_parts_forget : SetsParts ~{Sets}~> SetsPartsProp.
Proof.
  unshelve refine
    {| morphism := fun S : carrier SetsParts =>
         existT (fun P : carrier (Powerset_Prop_obj A) =>
                   Powerset_squash
                     { a : carrier A
                         & @equiv _ (Powerset_Prop_obj A) P
                             (sets_part_pred a) })
           (`1 S) (Powerset_squash_intro (`2 S)) |}.
  intros S T HST; exact HST.
Defined.

(* It is the identity on the underlying subset, by conversion. / 它是通过转换在底层子集上的恒等映射。 *)
Example sets_parts_forget_pred (S : carrier SetsParts) :
  `1 (sets_parts_forget S) = `1 S.
Proof. reflexivity. Qed.

(* The composite class map into the strict object. / 复合类映射到严格对象。 *)
Definition sets_part_of_prop : SetsQuotient A R HR ~{Sets}~> SetsPartsProp :=
  sets_parts_forget ∘ sets_part_of.

Lemma sets_part_of_prop_surjective (S : carrier SetsPartsProp) :
  Powerset_squash
    { a : carrier A & @equiv _ SetsPartsProp (sets_part_of_prop a) S }.
Proof.
  intros Q k; apply (`2 S); intros [a Ha]; apply k.
  exists a.
  assert (Hsym : @equiv _ (Powerset_Prop_obj A) (sets_part_pred a) (`1 S))
    by (symmetry; exact Ha).
  exact Hsym.
Qed.

End Partition.


(* * ** Non-vacuity: the parity quotient, read as a set of parts / * ** 非空性：奇偶商，读作一组部分 *)

(*
 Instance/Sets/Quotient.v's [nat_parity] is [Prop]-valued (an equation
 of booleans), so [prop_rel_squash_stable] discharges the hypothesis
 and the isomorphism is unconditional at it. 

 --------
 Instance/Sets/Quotient.v 的 [nat_parity] 是 [Prop] 值的（一个布尔方程），所以 [prop_rel_squash_stable] 消除了假设，并且在它上面的同构是无条件的。
*)
Definition nat_parity_stable : SquashStable nat_parity.
Proof.
  apply (prop_rel_squash_stable nat_parity nat_parity_Equivalence nat_parity_coarser
           (fun m n => Nat.even m = Nat.even n)).
  intros m n; split; intro H; exact H.
Qed.

Definition nat_parity_partition_iso :
  @Isomorphism Sets NatParity (SetsParts nat_parity nat_parity_Equivalence nat_parity_coarser) :=
  sets_partition_iso nat_parity nat_parity_Equivalence nat_parity_coarser
    nat_parity_stable.

(*
 The parts genuinely merge and genuinely separate: 0 and 2 have the
 same class, 0 and 1 do not.  The negative goes through the
 isomorphism's own injectivity clause, so it is a statement about the
 PARTS and not about [nat_parity] restated. 

 --------
 这些部分真正地融合并真正地分离：0 和 2 属于同一类别，0 和 1 不同。负面通过同构自身的单射性条款，因此这是关于部分的陈述，而不是关于重新表述的 [nat_parity]。
*)
Lemma nat_parity_parts_merge :
  @equiv _ (SetsParts nat_parity nat_parity_Equivalence nat_parity_coarser)
    (sets_part_of nat_parity nat_parity_Equivalence nat_parity_coarser 0%nat)
    (sets_part_of nat_parity nat_parity_Equivalence nat_parity_coarser 2%nat).
Proof.
  exact (sets_part_pred_respects nat_parity nat_parity_Equivalence
           nat_parity_coarser 0%nat 2%nat eq_refl).
Qed.

Lemma nat_parity_parts_separate :
  @equiv _ (SetsParts nat_parity nat_parity_Equivalence nat_parity_coarser)
    (sets_part_of nat_parity nat_parity_Equivalence nat_parity_coarser 0%nat)
    (sets_part_of nat_parity nat_parity_Equivalence nat_parity_coarser 1%nat)
  → False.
Proof.
  intro H.
  pose proof (squash_stable_injective nat_parity nat_parity_Equivalence
                nat_parity_coarser nat_parity_stable 0%nat 1%nat H) as E.
  discriminate E.
Qed.
