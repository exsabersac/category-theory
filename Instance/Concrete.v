Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Rel.

Generalizable All Variables.

(*
 Obligation discipline: with the default tactic, Program discharges some
 obligations and names the variables of the rest itself, and both behaviours
 have varied across the Coq versions this library supports.  Setting the
 tactic to [idtac] makes every obligation below the raw field type, with
 variables introduced by name in the proof — the same discipline
 Construction/Free/Quiver/Concrete.v uses. 

 --------
 义务规范：使用默认策略时，程序会解决一些义务，并自行命名其余义务的变量，而这两种行为在本库支持的不同 Coq 版本中有所不同。将策略设置为 [idtac] 会使 proof 中的每个义务都遵循原始字段类型，并通过名称引入变量——这是 Construction/Free/Quiver/Concrete.v 使用的相同规范。
*)
#[local] Obligation Tactic := idtac.

(* * * The concrete-category roster: Coq, CMon, and Rel / * * 具体类别列表：Coq、CMon 和 Rel *)

(*
 nLab:      https://ncatlab.org/nlab/show/concrete+category
 Wikipedia: https://en.wikipedia.org/wiki/Concrete_category
 Book:      Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 GTM 5, Springer 1998, §I.7, printed p. 26
 Book:      Riehl, “Category Theory in Context”, Dover 2016, §1.6,
 Definition 1.6.18, printed p. 45
 Paper:     Freyd, “Homotopy is not concrete”, Lecture Notes in Mathematics
 168, Springer 1970, pp. 25-34

 This file instantiates [Concrete] (Theory/Concrete.v) at the in-tree
 categories for which Mac Lane's §I.7 remark has content, and settles the
 negative half of that remark for Rel as precisely as the library permits.
 `Sets` itself is handled in Theory/Concrete.v, twice over — by the identity
 functor and by global elements.

 Positive instances here
 -----------------------

 [Coq_Concrete]  — Instance/Coq.v's category of types and functions, via the
 functor sending a type to itself under Leibniz equality.  Morphism
 equivalence in `Coq` is already pointwise `=`, so this functor is the
 identity on hom-setoids and faithfulness is the identity implication.

 [CMon_Concrete] — Instance/CMon.v's category of commutative monoids, via
 `CMon_Forget` (Instance/CMon.v).  That file's header comment at lines
 166-168 asserts faithfulness without proving it; [CMon_Forget_Faithful]
 below supplies the proof.

 [Rel_Concrete]  — Instance/Rel.v's category of sets and relations, via the
 direct-image (powerset) functor.  See the discussion of the negative
 result below for why this instance is worth having.

 Algebraic categories beyond CMon are cross-referenced, not depended on.
 Theory/Algebra/Monoid/Hom.v already proves `Mon_Forget_Faithful`, but its
 `Mon` is the category of monoid OBJECTS internal to an ambient monoidal
 category, whose forgetful functor lands in that ambient category rather
 than in `Sets`; it therefore does not yield a `Concrete` instance without
 first fixing the ambient category to `Sets`, which is not done here.
 Theory/Lawvere/Sets.v's `ev1_Faithful` does land in `Sets`, but only under
 its reachability hypothesis, so it too is left as a cross-reference.

 The negative half of Mac Lane's §I.7 remark, for Rel
 ---------------------------------------------------

 Rel is commonly quoted alongside Toph as a category that “is not
 concrete”.  Read literally — “Rel has no faithful functor to sets” —
 that quotation is too strong, and this file does not assert it:
 [Rel_Concrete] below exhibits a faithful functor.  The target of the
 correction is that FOLKLORE reading, not Mac Lane's own sentence, which
 (as the issue filing this work summarizes it) already scopes the claim
 to the evident forgetful functor; an audit of the first commit was right
 to insist the distinction be drawn, since the primary text was not
 available to check.  What is true, and what is proved here, concerns the
 EVIDENT candidate, the assignment sending a set to itself:

 [Rel_hom_is_not_a_function] — the elementary obstruction.  Instance/Rel.v's
 `some_number`, the strict order `<` on nat, is a morphism of
 Rel that is not the graph of any function nat → nat.  So the evident
 underlying-set assignment `X ↦ X` cannot be extended to arrows at all,
 and there is nothing to check faithfulness of.

 [Rel_subsingleton_not_Faithful] — the sharp obstruction, stated for every
 candidate at once.  No functor `U : Rel ⟶ Sets` whose value at the
 one-element set is a subsingleton can be faithful, because Rel has two
 distinct endorelations of the one-element set ([Rel_two_arrows]) which
 any such `U` must send to the same function.  The evident underlying-set
 candidate would have `U 1` a singleton, so it is covered.

 [Rel_Concrete] is the complement of that result and is what keeps it from
 being overread.  The direct-image functor sends a set `X` to its powerset
 and a relation to its direct-image map; it is faithful because probing a
 relation with singletons recovers it.  Its value at the one-element set
 has two elements, so it escapes [Rel_subsingleton_not_Faithful] exactly
 as it must.  Conclusion: Rel is concrete, but not via its evident
 forgetful functor — which is the reading of Mac Lane's remark this
 development adopts, and it is an erratum against the literal reading.

 Deferral, disclosed
 -------------------

 The Toph half of the remark — Freyd's 1970 theorem that the pointed
 homotopy category has no faithful functor to sets — is out of scope, is
 not proved, and is not assumed.  The library has no homotopy category, so
 the statement is not expressible in-tree at all.  Theory/Concrete.v's
 header records the same deferral.  It becomes STATEABLE once the
 homotopy-category construction of Mac Lane's §I.7 lands (catalog item
 `maclane:I.7:construction5`, filed as issue #260); until then there is
 no object in the tree for the theorem to be about.

 Vacuity
 -------

 Each positive instance is accompanied by two parallel morphisms shown
 DISTINCT in the relevant hom-setoid ([Coq_two_arrows], [CMon_two_arrows],
 [Rel_two_arrows]).  Faithfulness is an injectivity statement, so it would
 be content-free over trivial hom-setoids; these witnesses show it is not. 

 --------
 nLab：       https://ncatlab.org/nlab/show/concrete+category
 维基百科：  https://en.wikipedia.org/wiki/Concrete_category
 书籍：      Mac Lane，《工作数学家的范畴论》，第2版，GTM 5，施普林格 1998，第 I.7 节，印刷页 26
 书籍：      Riehl，《语境中的范畴论》，多佛 2016，第 1.6 节，定义 1.6.18，印刷页 45
 论文：      Freyd，《同伦不是具体的》，数学讲义 168，施普林格 1970，第 25-34 页

 本文件在树内范畴中实例化了 [Concrete]（Theory/Concrete.v），这些范畴中 Mac Lane 的 §I.7 注释有内容，并且尽图书馆允许的精度解决了 Rel 的该注释的否定部分。
 `Sets` 本身在 Theory/Concrete.v 中处理过两次——通过恒等函子和全局元素。

 正实例实例在此
 -----------------------[Coq_Concrete] —— Instance/Coq.v 中的类型与函数范畴，通过将一个类型在莱布尼茨等价下映射到它自身的函子。`Coq` 中的态射等价已经是逐点的 `=`，因此这个函子在同态集合上是恒等的，并且忠实性就是恒等蕴涵。

 [CMon_Concrete] —— Instance/CMon.v 中的交换幺半群范畴，通过 `CMon_Forget` (Instance/CMon.v)。该文件在第 166-168 行的头部注释断言了忠实性，但没有证明；下面的 [CMon_Forget_Faithful] 提供了证明。

 [Rel_Concrete] —— Instance/Rel.v 中的集合与关系范畴，通过直接像（幂集）函子。参见下文对该实例价值的负面结果讨论。超过 CMon 的代数范畴是交叉引用的，而不是依赖的。
 Theory/Algebra/Monoid/Hom.v 已经证明了 `Mon_Forget_Faithful`，但它的 `Mon` 是一个内部于一个环境单体范畴的幺半群对象的范畴，其遗忘函子落在该环境范畴中，而不是在 `Sets` 中；因此，在没有先将环境范畴固定为 `Sets` 的情况下，它不会生成 `Concrete` 实例，这里没有进行该操作。
 Theory/Lawvere/Sets.v 的 `ev1_Faithful` 确实落在 `Sets` 中，但仅在其可达性假设下，因此它也只是被作为交叉引用。

 Mac Lane §I.7 的负面部分，对于 Rel
 ---------------------------------------------------Rel 通常与 Toph 一起被引用为“非具体”的范畴。字面理解——“Rel 没有忠实函子到集合”——这个引用太绝对了，而该文件并未断言这一点：下文的 [Rel_Concrete] 展示了一个忠实函子。此更正的目标是纠正广为流传的理解，而非 Mac Lane 本人的原话，（正如本工作提交的问题总结所述）他早已将该断言的范围限定于显而易见的遗忘函子；对第一次提交的审查坚持区分此点是正确的，因为主要文本不可获得以供核对。真正正确且在此证明的，是关于显而易见候选函子，即将一个集合赋值给它自身的映射。[Rel_hom_is_not_a_function] — 基本障碍。实例/关系.v 的 `some_number`，nat 上的严格顺序 `<`，是 Rel 的一个态射，但不是任何函数 nat → nat 的图。因此，显而易见的底层集合赋值 `X ↦ X` 根本无法扩展到箭头上，也没有什么可以检查保真性的。

 [Rel_subsingleton_not_Faithful] — 尖锐障碍，为每个候选同时陈述。没有任何函子 `U : Rel ⟶ Sets`，其在单元素集上的值是子单元集，可以是保真的，因为 Rel 对单元素集有两个不同的自关系（[Rel_two_arrows]），任何这样的 `U` 都必须将它们映射为相同的函数。显而易见的底层集合候选将有 `U 1` 作为单元素集，因此它已被涵盖。[Rel_Concrete] 是该结果的补集，也是防止其被过度读取的原因。直接像函子将一个集合 `X` 映射到其幂集，并将一个关系映射到其直接像映射；它是忠实的，因为用单子集合探测一个关系可以恢复它。它在单元素集合上的值有两个元素，因此它正好像必须的那样逃脱 [Rel_subsingleton_not_Faithful]。结论：Rel 是具体的，但不是通过其显而易见的遗忘函子——这是本发展采用的对 Mac Lane 评论的解读，同时也是对字面解读的勘误。

 延迟，已披露
 -------------------备注的上半部分——Freyd 在 1970 年的定理，即有基点的同伦范畴没有到集合的忠实函子——超出讨论范围，未被证明，也未被假设。该库没有同伦范畴，因此该陈述在树中根本无法表达。Theory/Concrete.v 的头部也记录了相同的延迟。一旦 Mac Lane §I.7 的同伦范畴构造到位（目录项 `maclane:I.7:construction5`，记录为问题 #260），它就可以被表述；在此之前，树中没有定理涉及的对象。

 空性
 ------每个正实例都伴随着两个平行的态射，显示在相关的同态集合中是不同的（[Coq_two_arrows]，[CMon_two_arrows]，[Rel_two_arrows]）。忠实性是一个单射性声明，因此在平凡的同态集合上将是无内容的；这些证据表明情况并非如此。
*)

(** ** Coq: types and functions / ** Coq：类型和函数 *)

(*
 Every type is a setoid under Leibniz equality, and every function respects
 it.  `Coq`'s own hom-equivalence is pointwise `=`, which is exactly the
 hom-equivalence of the image setoids, so this functor neither adds nor
 loses information on arrows. 

 --------
 在莱布尼茨等式下，每种类型都是一个集合，并且每个函数都尊重它。`Coq` 自身的同态等价是逐点的 `=`，这正是像集合的同态等价，所以这个函子既不增加也不丢失箭头上的信息。
*)
Program Definition Coq_Underlying@{u u0 +} :
  Coq@{u u0 u0 u0} ⟶ Sets@{u0 u} := {|
  fobj := fun A => {| carrier   := A
                    ; is_setoid := {| equiv        := @eq A
                                    ; setoid_equiv := eq_equivalence |} |};
  fmap := fun _ _ f => {| morphism := f |}
|}.
Next Obligation. intros A B f a b Hab; simpl in *; subst; exact eq_refl. Qed.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; reflexivity. Qed.
Next Obligation. intros A B C f g a; reflexivity. Qed.

(*
 Faithfulness is the identity implication: both `≈`s unfold to pointwise
 Leibniz equality of the same function. 

 --------
 忠诚性是身份蕴含：两个 `≈` 都展开为相同函数的逐点莱布尼茨等式。
*)
#[export] Instance Coq_Underlying_Faithful@{u u0 +} :
  Faithful Coq_Underlying@{u u0} .
Proof.
  constructor; intros A B f g Hfg.
  exact Hfg.
Qed.

#[export] Instance Coq_Concrete@{u u0 +} : Concrete Coq@{u u0 u0 u0} := {|
  underlying          := Coq_Underlying@{u u0};
  underlying_faithful := Coq_Underlying_Faithful@{u u0}
|}.

(*
 Non-vacuity for [Coq_Concrete]: `negb` and the identity are parallel arrows
 `bool ~> bool` that differ in the hom-setoid, whose `≈` is pointwise `=`.
 (Stated with `→ False`: hom-equivalence here is `Type`-valued, so `¬` —
 which forces `Prop` — does not apply.) 

 --------
 非空性对于 [Coq_Concrete]：`negb` 和恒等映射是平行箭头 `bool ~> bool`，在同态集合上有所不同，其 `≈` 是逐点 `=`。（用 `→ False` 表述：此处的同态等价是 `Type` 值，因此 `¬`——这强制 `Prop`——不适用。）
*)
Lemma Coq_two_arrows : @id Coq bool ≈ negb → False.
Proof.
  intro Heq.
  specialize (Heq true).
  simpl in Heq.
  discriminate.
Qed.

(** ** CMon: commutative monoids / ** CMon：交换幺半群 *)

(*
 The proof Instance/CMon.v itself only asserts.  Equivalence of
 homomorphisms in `CMon` (`CMonHom_Setoid`) is by definition pointwise
 equivalence of the underlying setoid maps, which is what `CMon_Forget`
 records, so injectivity of its hom-map is the identity implication. 

 --------
 证明实例 CMon.v 本身仅仅断言。在 `CMon`（`CMonHom_Setoid`）中的同态的等价性根据定义是基础集合化映射的逐点等价，这正是 `CMon_Forget` 记录的内容，因此其同态映射的单射性就是恒等蕴涵。
*)
#[export] Instance CMon_Forget_Faithful : Faithful CMon_Forget.
Proof.
  constructor; simpl; intros M N f g Hfg a.
  exact (Hfg a).
Qed.

#[export] Instance CMon_Concrete : Concrete CMon := {|
  underlying          := CMon_Forget;
  underlying_faithful := CMon_Forget_Faithful
|}.

(* The natural numbers under Leibniz equality, as a setoid. / 在莱布尼茨等式下的自然数，作为一个集合结构。 *)
Definition nat_setoid_object : SetoidObject :=
  {| carrier   := nat
   ; is_setoid := {| equiv := @eq nat ; setoid_equiv := eq_equivalence |} |}.

(*
 The additive monoid of natural numbers, used only to show that `CMon` has
 parallel morphisms that differ. 

 --------
 自然数的加法幺半群，仅用于显示  `CMon`  存在不同的平行态射。
*)
Definition nat_CMon : CMonObject.
Proof.
  unshelve refine {| cmon_setoid := nat_setoid_object
                   ; cmon_zero   := 0%nat
                   ; cmon_plus   := Nat.add |}.
  - intros a b c; simpl; symmetry; apply PeanoNat.Nat.add_assoc.
  - intros a b; simpl; apply PeanoNat.Nat.add_comm.
  - intros a; simpl; reflexivity.
  (*
 [cmon_prop] raises no fourth goal: the carrier's `≈` IS Coq's [eq], so
 [refine]'s typeclass resolution closes the field with [eq_PropEquiv]
 (Lib/Setoid/Propositional.v) before the bullets are reached. 

 --------
 [cmon_prop] 没有提出第四个目标：载体的 `≈` 是 Coq 的 [eq]，因此 [refine] 的类型类解析会在到达项目符号之前使用 [eq_PropEquiv] （Lib/Setoid/Propositional.v）关闭该字段。
*)
Defined.

(*
 The constant-zero endomorphism of `nat_CMon`; it preserves the unit and the
 operation, so it is a genuine homomorphism. 

 --------
 `nat_CMon` 的常零自同态；它保持单位元和运算，因此它是真正的同态。
*)
Definition nat_CMon_zero_hom : CMonHom nat_CMon nat_CMon.
Proof.
  unshelve refine (Build_CMonHom nat_CMon nat_CMon _ _ _).
  - refine {| morphism := fun _ => 0%nat |}.
  - simpl; reflexivity.
  - intros a b; simpl; reflexivity.
Defined.

(*
 Non-vacuity for [CMon_Concrete]: the identity and the constant-zero
 homomorphism are parallel arrows of `CMon` that differ in the hom-setoid,
 whose `≈` is pointwise equivalence of the underlying maps. 

 --------
 [CMon_Concrete] 的非空性：恒等映射和恒零同态是 `CMon` 的平行箭头，但在同类集合中不同，其 `≈` 是底层映射的逐点等价。
*)
Lemma CMon_two_arrows : @id CMon nat_CMon ≈ nat_CMon_zero_hom → False.
Proof.
  intro Heq.
  specialize (Heq 1%nat).
  simpl in Heq.
  discriminate.
Qed.

(* * ** Rel: sets and relations, the negative half / * ** 关系：集合与关系，负半部分 *)

(* An auxiliary arithmetic fact, proved here to keep the file's dependencies to the ones already present in Instance/Rel.v. / 一个辅助算术事实，在此证明以将文件的依赖项保持在 Instance/Rel.v 中已经存在的那些。 *)
Lemma nat_neq_succ (n : nat) : n = S n → False.
Proof.
  induction n as [|n IH]; intro Hn.
  - discriminate.
  - apply IH.
    now injection Hn.
Qed.

(*
 Instance/Rel.v's `some_number` is the strict order `<` on nat,
 read as a relation nat ⇸ nat.  It is not the graph of any function: if it
 were the graph of `f`, then `f 0` would have to be simultaneously the
 unique natural number above 0 and its own successor.

 This is the elementary form of Mac Lane's negative remark.  The evident
 underlying-set assignment for Rel — send a set to itself — has no action on
 arrows to define, because Rel's arrows are not functions between the
 underlying sets. 

 --------
 Instance/Rel.v 的 `some_number` 是自然数上的严格顺序 `<`，读作一个关系 nat ⇸ nat。它不是任何函数的图：如果它是 `f` 的图，那么 `f 0` 必须同时是大于 0 的唯一自然数并且是它自身的后继。

 这是 Mac Lane 消极评论的基本形式。Rel 的明显底层集合分配 —— 将一个集合映射到自身 —— 对箭头没有作用来定义，因为 Rel 的箭头不是底层集合之间的函数。
*)
Theorem Rel_hom_is_not_a_function (f : nat → nat) :
  (∀ x y : nat, some_number x y ↔ f x = y) → False.
Proof.
  intro Hgraph.
  (* `f 0` is above 0, since `f 0 = f 0`. / `f 0` 高于 0，因为 `f 0 = f 0` 。 *)
  assert (H0 : some_number 0%nat (f 0%nat)) by now apply Hgraph.
  (* `S (f 0)` is also above 0, so the graph reading forces `f 0 = S (f 0)`. / `S (f 0)` 也大于 0，所以图表读数迫使 `f 0 = S (f 0)` 。 *)
  assert (HS : some_number 0%nat (S (f 0%nat))).
  { unfold some_number in *.
    apply PeanoNat.Nat.lt_lt_succ_r, H0. }
  apply (nat_neq_succ (f 0%nat)).
  now apply Hgraph.
Qed.

(*
 The two endorelations of the one-element set: the identity (the diagonal,
 which relates the point to itself) and the empty relation.  In Rel's
 hom-setoid, whose `≈` is pointwise `↔`, they differ.  A one-element SET has
 only one endofunction, so this pair already shows Rel's hom-setoids are
 strictly larger than the corresponding function sets. 

 --------
 一个单元素集合的两个自关系：恒等关系（对角线，将该点与自身相关联）和空关系。在 Rel 的同态集（hom-setoid）中，其 `≈` 是逐点 `↔` ，它们是不同的。一个单元素集合只有一个自函数，因此这一对已经显示出 Rel 的同态集严格大于相应的函数集合。
*)
Definition Rel_empty : (unit : Rel) ~{Rel}~> (unit : Rel) :=
  fun _ _ => False.

Lemma Rel_two_arrows : @id Rel unit ≈ Rel_empty → False.
Proof.
  intro Heq.
  apply (Heq tt tt).
  (* `id` in Rel is `Singleton`, so the point is related to itself. / `id` 在关系中是 `Singleton`，所以这个点与它自身相关。 *)
  constructor.
Qed.

(*
 The sharp negative result.  Any candidate underlying-set functor for Rel
 that sends the one-element set to a subsingleton — as the evident
 “underlying set” candidate would — is not faithful, because it must
 identify the two arrows of [Rel_two_arrows].

 Note what is and is not claimed: this refutes a FAMILY of candidates,
 selected by their value at the one-element set.  It does not say Rel is
 non-concretizable, and [Rel_Concrete] below shows it is not. 

 --------
 尖锐的负面结果。任何对 Rel 的候选底集合函子，如果将单元素集合映射到子单集合——就像显而易见的“底集合”候选那样——都不是忠实的，因为它必须将 [Rel_two_arrows] 的两个箭头识别为相同。

 注意所声称的内容与未声称的内容：这驳斥了一族候选，它们是通过在单元素集合上的取值来选择的。它并没有说 Rel 不能具体化，而下面的 [Rel_Concrete] 表明它不是如此。
*)
Theorem Rel_subsingleton_not_Faithful (U : Rel ⟶ Sets)
        (Hsub : ∀ a b : carrier (U (unit : Rel)), a ≈ b) :
  Faithful U → False.
Proof.
  intro HF.
  apply Rel_two_arrows.
  apply (fmap_inj (F:=U)).
  simpl; intro a.
  apply Hsub.
Qed.

(* * ** Rel: sets and relations, the positive half / * ** 关系：集合与关系，正半部分 *)

(*
 The direct-image functor `P : Rel ⟶ Sets`.  An object `X` is sent to its
 powerset — `Ensemble X`, compared by pointwise `↔` — and a relation
 `R ⊆ X × Y` to the map taking a subset `S ⊆ X` to its image
 `{ y | ∃ x ∈ S, R x y }`.  This is the Kleisli presentation of Rel over
 the powerset monad read as a functor into sets. 

 --------
 直接映像函子  `P : Rel ⟶ Sets` 。一个对象  `X` 被发送到它的幂集 —  `Ensemble X` ，按点对点的  `↔`  比较 — 而一个关系  `R ⊆ X × Y` 被发送到将子集  `S ⊆ X` 映射到其像  `{ y | ∃ x ∈ S, R x y }` 的映射。 这是 Rel 在幂集幺半群上的 Kleisli 表示，作为到集合的函子来读取。
*)
Program Definition Rel_Powerset : Rel ⟶ Sets := {|
  fobj := fun X => {| carrier   := X → Prop
                    ; is_setoid := {| equiv := fun S T => ∀ x, S x ↔ T x |} |};
  fmap := fun X Y R =>
            {| morphism := fun S y => (exists x : X, S x ∧ R x y)%type |}
|}.
Next Obligation.
  (* the powerset setoid: pointwise `↔` is an equivalence / 幂集等价类：逐点 `↔` 是一个等价关系 *)
  (* `↔` here is Category.Lib's `iffT`, a pair of maps, so the two directions are reached with [fst] and [snd] rather than [proj1]/[proj2]. / `↔` 这是 Category.Lib 的 `iffT`，一对地图，因此两个方向是通过 [fst] 和 [snd] 到达的，而不是 [proj1] / [proj2]。 *)
  intros X; constructor.
  - intros S a; split; intro Ha; exact Ha.
  - intros S T HST a; split; [ exact (snd (HST a)) | exact (fst (HST a)) ].
  - intros S T U HST HTU a; split; intro Ha.
    + exact (fst (HTU a) (fst (HST a) Ha)).
    + exact (snd (HST a) (snd (HTU a) Ha)).
Qed.
Next Obligation.
  (* the direct image of a fixed relation respects `≈` of subsets / 固定关系的直接映像遵守子集的 `≈` *)
  intros X Y R S T HST b.
  split; intros [a [Ha HR]]; exists a; split.
  - exact (fst (HST a) Ha).
  - exact HR.
  - exact (snd (HST a) Ha).
  - exact HR.
Qed.
Next Obligation.
  (* equivalent relations have equal direct images / 等价关系具有相等的直接像 *)
  intros X Y R R' HRR' S b.
  split; intros [a [Ha HR]]; exists a; split.
  - exact Ha.
  - exact (fst (HRR' a b) HR).
  - exact Ha.
  - exact (snd (HRR' a b) HR).
Qed.
Next Obligation.
  (* the direct image along the diagonal is the identity on subsets / 沿对角线的直接映像在子集上是恒等映射 *)
  intros X S a; split; intro Hin.
  - destruct Hin as [b [HSb Hdiag]].
    now destruct Hdiag.
  - exists a.
    split; [ exact Hin | constructor ].
Qed.
Next Obligation.
  (* direct image takes relational composites to composites of maps / 直接图像将关系复合映射到映射的复合 *)
  intros X Y Z R R' S c; split.
  - intros [a [Ha [b [HR' HR]]]].
    exists b; split; [ exists a; split; assumption | exact HR ].
  - intros [b [[a [Ha HR']] HR]].
    exists a; split; [ exact Ha | exists b; split; assumption ].
Qed.

(* Faithfulness: probe the direct-image map with the singleton subsets. If `R` and `R'` have the same direct images then they agree on every `{x}`, hence everywhere. / 忠实性：用单元素子集探测直接像映射。如果 `R` 和 `R'` 有相同的直接像，那么它们在每一个 `{x}` 上都一致，因此在所有地方都一致。 *)
#[export] Instance Rel_Powerset_Faithful : Faithful Rel_Powerset.
Proof.
  constructor; simpl; intros X Y R R' Himg x y.
  specialize (Himg (fun a => a = x) y).
  split; intro Hxy.
  - destruct Himg as [Hfwd _].
    destruct Hfwd as [a [Ha HR]]; [ now exists x | ].
    now subst.
  - destruct Himg as [_ Hbwd].
    destruct Hbwd as [a [Ha HR]]; [ now exists x | ].
    now subst.
Qed.

#[export] Instance Rel_Concrete : Concrete Rel := {|
  underlying          := Rel_Powerset;
  underlying_faithful := Rel_Powerset_Faithful
|}.

(*
 The powerset functor escapes [Rel_subsingleton_not_Faithful] exactly where
 it must: its value at the one-element set has two distinct elements, the
 empty subset and the whole set.  So the hypothesis of that theorem is not
 met, and no contradiction arises with [Rel_Concrete]. 

 --------
 幂集函子正是在必须的地方逃出了 [Rel_subsingleton_not_Faithful]：它在单元素集合上的值有两个不同的元素，即空子集和整个集合。因此，该定理的假设不成立，也不会与 [Rel_Concrete] 产生矛盾。
*)
Lemma Rel_Powerset_unit_not_subsingleton :
  (∀ a b : carrier (Rel_Powerset (unit : Rel)), a ≈ b) → False.
Proof.
  intro Hsub.
  apply (Hsub (fun _ => False) (fun _ => True) tt).
  exact I.
Qed.
