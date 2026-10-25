Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Adjunction.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.Coalgebra.
Require Import Category.Comonad.Duality.
Require Import Category.Structure.Thin.Monad.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Adjunction.
Require Import Category.Instance.Props.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Monad.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* * * The modal operator B ⇒ − on propositions / * * 命题上的模态算子 B ⇒ − *)

(*
 nLab: https://ncatlab.org/nlab/show/modal+operator
 nLab: https://ncatlab.org/nlab/show/closure+operator
 Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
 SS 1.4.4, Example 1.123, printed pp. 34-35, and footnote 8,
 printed p. 33
 Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
 SS 10.2, Example 10.4, printed p. 270

 WHAT THE BOOK SAYS.  Seven Sketches Example 1.123 orders propositions
 by entailment ("p ≤ q iff p implies q") and says: "A closure operator
 on it is often called a modal operator.  It is a function j from
 propositions to propositions, for which p ⇒ j(p) and j(j(p)) = j(p).
 An example of a j is 'assuming Bob is in San Diego....'  Think of this
 as a proposition B; so 'assuming Bob is in San Diego, p' means B ⇒ p.
 Let's see why B ⇒ − is a closure operator."  The argument that
 follows is informal.  Awodey's Example 10.4 (p. 270) names a different
 modality, "The 'possibility operator' ⋄p in modal logic is another
 example", which is not stated here.

 WHICH READING IS IMPLEMENTED.  The entailment preorder is
 Instance/Props.v's [Props]: objects [Prop], arrows [Basics.impl], and
 the hom-setoid [True], so [Props] is thin.  [modal_functor B] is
 p ↦ (B → p), [modal_ext] is the first axiom, and the second is
 [modal_idem] as mutual entailment (stdlib [<->]; the library's [↔] is
 [iffT]), which is the isomorphism of [Props].  The book's "=" between
 propositions is [modal_idem_ext], under propositional extensionality
 supplied as a hypothesis; no axiom is assumed.  [modal_monad] is the
 monad: its unit is [modal_ext], its multiplication [modal_mult], the
 transparent term f ↦ (b ↦ f b b), of which [modal_idem] is built, so
 that join computes ([modal_monad_join]); its five laws are [I].
 [modal_monad_is_thin]: it IS Structure/Thin/Monad.v's [thin_monad] at
 [Props] with the witness [fun _ _ _ _ => I], on the whole record by
 [eq_refl].  It is not DEFINED through [thin_monad]: that route is
 refused bare, the sort level of Structure/Thin.v's [Thin] being left
 in the body alone; pinned to u or h it adds h <= u or u <= h
 (measured); with + the thin level stays in the block only (the reason
 Instance/Proset/Monad.v gives for [closure_monad]).  Its algebras are
 the j-closed propositions, (B → p) → p ([modal_talgebra_iff]), and at
 B := False the proposition False is not closed
 ([modal_false_not_closed]).

 THE MONAD OF THE CURRYING ADJUNCTION, at its true strength.  [Props]
 is cartesian closed ([Props_Closed]), and
 Structure/Cartesian/Closed/Adjunction.v's [Curry_Adjunction B] is
 (− ∧ B) ⊣ (B ⇒ −).  Its monad [curry_monad B] has the functor
 p ↦ (B → p ∧ B), by [eq_refl] ([curry_monad_fobj]).  That is a
 different term from B ⇒ −: the equation of the two object maps is
 refused by conversion (measured).  It is NOT a different functor in
 the library's sense: the two are ≈ ([curry_modal_iso], a natural
 isomorphism in [Props]), they have the same closed elements
 ([curry_modal_closed_iff]), and under propositional extensionality,
 taken as a hypothesis, the object maps are equal
 ([curry_modal_fobj_ext]).  So no proof that the object maps differ
 can exist unless that axiom, which is consistent with Coq, is
 refuted (for the functors themselves, functional extensionality as
 well).  The
 modality is obtained from [Props_Closed] up to natural isomorphism,
 and not on the nose.

 THE DUAL.  The same adjunction's comonad [curry_comonad B]
 (Comonad/Duality.v's [Adjunction_Comonad]) has the functor
 p ↦ (B → p) ∧ B ([curry_comonad_fobj]), which is B ∧ − up to mutual
 entailment ([curry_comonad_is_and]): the other composite of footnote 8,
 an interior operator.  Its coalgebras are the p with
 p → (B → p) ∧ B ([curry_wcoalgebra_iff]), that is, the propositions
 that entail B ([curry_open_iff_entails]).

 THE ORDER-LEVEL OPERATOR.  [impl_PreOrder] is [Basics.impl] as a
 stdlib [PreOrder] (the tree declares none, and [Search PreOrder
 Basics.impl] finds none in the loaded stdlib), and [modal_closure B]
 is B ⇒ − as an Instance/Proset/Monad.v [ClosureOperator] on it.  Its
 functor agrees with [modal_functor B] on objects by [eq_refl]
 ([modal_closure_fobj]), and [closure_monad (modal_closure B)] has the
 unit and multiplication of [modal_monad B] by [eq_refl].  The two
 categories are not convertible as the tree stands; the refusal at
 [impl_PreOrder] is the opacity of the two files' Program obligations
 alone: with them transparent (verbatim restatements under Set
 Transparent Obligations), Props = Proset impl_PreOrder is eq_refl on
 the whole record; for a variable P it is refused at [id]
 structurally.  In detail: [Props] is its own [Program Definition]
 (Instance/Proset/Limit.v says it is not [Proset P] for any P, which
 holds by conversion as the tree stands); at [impl_PreOrder] the [obj],
 [hom], [id] and [compose] fields agree by [eq_refl] and the refusal is
 at [homset], each category carrying its own proof that [True] is an
 equivalence (Instance/Props.v's [Props_obligation_1] and
 Instance/Proset.v's [Proset_obligation_1]); for a variable
 [P : PreOrder Basics.impl] the [obj] and [hom] fields agree and [id]
 is refused, with the obligations transparent or not, the identity of
 [Proset P] being the reflexivity proof of the variable P.

 STRENGTHS, measured.  [eq_refl]: [modal_monad_is_thin] (whole record),
 [modal_monad_join] (join computes), [modal_talgebra_round] (structure
 map), [curry_monad_fobj],
 [curry_comonad_fobj], [modal_closure_fobj], [modal_closure_ret],
 [modal_closure_join].  ≈: [curry_modal_iso].  Refused by conversion:
 the object equation of the curry and modal functors (so also the
 functor equation), and [Props = Proset P].  No [Qed] enters the first:
 both sides normalise, to B → p ∧ B and to B → p, distinct [Prop]
 terms, so no flip to [Defined] can change it.  The second is an
 opacity refusal at [impl_PreOrder]: flipped, with verbatim
 restatements of the two [Program Definition]s under [Set Transparent
 Obligations], [Props = Proset impl_PreOrder] is [eq_refl] on the whole
 record; for a variable P the same flip leaves it refused at [id],
 structurally.

 UNIVERSES, read off [About] with all instances printed.  No constant
 has a level that occurs in its body only.  [Set < u] is [Props]'s own
 (its objects are [Prop]), first carried by Instance/Props.v's [Props].
 [h < e] in the curry constants is first carried by
 Structure/Cartesian/Closed.v's [Closed] (its [u0 < u1], the level of
 the [Sets] isomorphism of [exp_iso]), which [curry_functor] and
 [curry_cofunctor] take as an argument for that reason: [Exp_Functor]
 and [Prod_Functor] each carry a level absent from their own types, so
 with [Props_Closed] inlined the level e would occur in the body only.
 Those levels, the last level of [Curry_Adjunction]'s [Adjunction] and
 the level u4 of [Adjunction_Comonad], sixth in its binder (free in
 their blocks), are pinned to e or h.  The caps [h <= compose.u0,
 compose.u1, compose.u2, ID.u0, prod_rect.u0, prod_rect.u1,
 prod_rect.u2] are global stdlib
 universes already in the blocks of [Closed] and [Curry_Adjunction].
 [impl_PreOrder] carries the global [Set < Defs.u0] (stdlib's
 [PreOrder] at a relation on [Prop]).  The biconditionals [@{u h +}]
 add the free [iffT] level of their [Prop] side.  This file loads both
 declarations of [Thin] and of [proset_thin] (Structure/Thin.v with
 Instance/Proset/Order.v, and Instance/Proset/Galois.v, through
 Instance/Proset/Monad.v; measured by [Locate]) and names neither: the
 witness is the term [fun _ _ _ _ => I].

 NOT DELIVERED.  No Lawvere-Tierney topology or nucleus (B ⇒ −
 preserves meets, which is not stated); no other modality (Awodey's ⋄);
 no functoriality in B; nothing over a Heyting algebra other than
 [Props]. 

 --------
 nLab：https://ncatlab.org/nlab/show/modal+operator
 nLab：https://ncatlab.org/nlab/show/closure+operator
 书籍：Fong 和 Spivak，《组合性七个素描》，arXiv 第三版，
 第 1.4.4 节，例 1.123，印刷页 34-35，以及脚注 8，
 印刷页 33
 书籍：Awodey，《范畴论》（第一版，CMU 预印本，2005 年 9 月），
 第 10.2 节，例 10.4，印刷页 270书中所说。七个示例 1.123 按蕴涵排列命题（“p ≤ q 当且仅当 p 蕴涵 q”）并说：“它上的闭包算子通常被称为模态算子。它是一个从命题到命题的函数 j，对其有 p ⇒ j(p) 且 j(j(p)) = j(p)。j 的一个例子是‘假设 Bob 在圣地亚哥……’。将其视为命题 B；所以‘假设 Bob 在圣地亚哥，p’意味着 B ⇒ p。我们来看为什么 B ⇒ − 是一个闭包算子。”随后的论证是非正式的。Awodey 的示例 10.4（第 270 页）给出了一个不同的模态，“模态逻辑中的‘可能算子’⋄p 是另一个例子”，这里未说明。实施了哪种读法。蕴涵预序是 Instance/Props.v 的 [Props]：对象 [Prop]，箭头 [Basics.impl]，以及齐次集同构 [True]，所以 [Props] 是稀薄的。[modal_functor B] 是 p ↦ (B → p)，[modal_ext] 是第一个公理，第二个是 [modal_idem] 作为相互蕴涵（stdlib [<->]；库的 [↔] 是 [iffT]），它是 [Props] 的同构。书中命题之间的“=”是 [modal_idem_ext]，在提供为假设的命题外延下；没有假定任何公理。[modal_monad] 是 monad：它的 unit 是 [modal_ext]，它的 multiplication 是 [modal_mult]，透明项 f ↦ (b ↦ f b b)，由此构建了 [modal_idem]，因此 join 计算 ([modal_monad_join])；它的五条定律是 [I]。[modal_monad_is_thin] ：它是在 Structure/Thin/Monad.v 的 [thin_monad] 上，带有证据 [fun _ _ _ _ => I]，由 [eq_refl] 完整记录的。它不是通过 [thin_monad] 定义的：那条路径被直接拒绝，Structure/Thin.v 的 [Thin] 的类型级别仅保留在主体中；固定到 u 或 h 时，它会添加 h <= u 或 u <= h（经测量）；使用 + 时，薄类型级别仅保留在区块中（Instance/Proset/Monad.v 给出 [closure_monad] 的原因）。它的代数是 j-封闭命题，(B → p) → p ([modal_talgebra_iff])，并且在 B := False 时，命题 False 不是封闭的 ([modal_false_not_closed])。咖里附随的单子，在其真实强度下。[Props] 是笛卡尔闭合的（[Props_Closed]），并且 Structure/Cartesian/Closed/Adjunction.v 的 [Curry_Adjunction B] 是 (− ∧ B) ⊣ (B ⇒ −)。它的单子 [curry_monad B] 有函子 p ↦ (B → p ∧ B)，由 [eq_refl]（[curry_monad_fobj]）。这是一个不同于 B ⇒ − 的项：两个对象映射的方程被转换（测量）拒绝。这在库的意义上并不是一个不同的函子：两者是 ≈（[curry_modal_iso]，在 [Props] 中是自然同构），它们有相同的闭合元素（[curry_modal_closed_iff]），并且在命题外延性下，作为假设时，对象映射是相等的（[curry_modal_fobj_ext]）。所以，除非那个公理（与 Coq 一致）被驳斥，否则不可能存在物体映射的差异的证明（对于函子本身，也包括函数外延性）。模态是从 [Props_Closed] 得到的，直到自然同构为止，而不是精确相等。

 对偶。相同伴随的余单子 [curry_comonad B]（Comonad/Duality.v 中的 [Adjunction_Comonad]）有函子 p ↦ (B → p) ∧ B（[curry_comonad_fobj]），它在相互蕴含下是 B ∧ −（[curry_comonad_is_and]）：脚注 8 的另一个复合，是一个内算子。它的余代数是 p，使得 p → (B → p) ∧ B（[curry_wcoalgebra_iff]），也就是能够蕴含 B 的命题（[curry_open_iff_entails]）。订单级运算符。[impl_PreOrder] 是 [Basics.impl] 作为一个 stdlib [PreOrder]（树没有声明，[Search PreOrder Basics.impl] 在已加载的 stdlib 中也未找到），而 [modal_closure B] 是 B ⇒ − 在其上的 Instance/Proset/Monad.v [ClosureOperator]。它的函子在对象上与 [modal_functor B] 一致，通过 [eq_refl]（[modal_closure_fobj]），且 [closure_monad (modal_closure B)] 具有 [modal_monad B] 的单位和乘法，通过 [eq_refl]。根据当前树状结构，这两个范畴不可转换；在 [impl_PreOrder] 处拒绝，仅由于这两个文件的 Program 义务是不可见的：当它们透明（在 Set Transparent Obligations 下逐字重述）时，Props = Proset impl_PreOrder 在整个记录上都是 eq_refl；对于变量 P，在 [id] 处从结构上被拒绝。详细说明：[Props] 是其自身的 [Program Definition]（Instance/Proset/Limit.v 说明它对于任何 P 都不是 [Proset P]，这通过当前树的转换成立）；在 [impl_PreOrder] 时，[obj]、[hom]、[id] 和 [compose] 字段通过 [eq_refl] 一致，并且拒绝发生在 [homset]，每个类别都携带其自身的证明，表明 [True] 是一个等价关系（Instance/Props.v 的 [Props_obligation_1] 和 Instance/Proset.v 的 [Proset_obligation_1]）；对于一个变量 [P : PreOrder Basics.impl]，[obj] 和 [hom] 字段一致并且 [id] 被拒绝，义务透明或不透明，[Proset P] 的身份为变量 P 的自反性证明。优势，已测量。 [eq_refl] ： [modal_monad_is_thin]（完整记录）， [modal_monad_join]（加入计算）， [modal_talgebra_round]（结构图）， [curry_monad_fobj]， [curry_comonad_fobj]， [modal_closure_fobj]， [modal_closure_ret]， [modal_closure_join]。≈：[curry_modal_iso]。被转换拒绝：curry 和模态函子（functor）对象方程（因此也包括函子方程），以及 [Props = Proset P]。没有 [Qed] 进入第一个：两边归一化为 B → p ∧ B 和 B → p，不同的 [Prop] 项，因此翻转到 [Defined] 无法改变它。第二个在 [impl_PreOrder] 上是一个不透明拒绝：翻转后，在 [Set Transparent Obligations] 下对两个 [Program Definition] 的逐字重新陈述，[Props = Proset impl_PreOrder] 在整个记录上是 [eq_refl]；对于一个变量 P，相同的翻转会导致其在结构上于 [id] 处被拒绝。宇宙，读取 [About] 并打印所有实例。没有常量在其本体中只出现一个层级。[Set < u] 是 [Props] 本身（它的对象是 [Prop]），最初由 Instance/Props.v 的 [Props] 承载。curry 常量中的 [h < e] 最初由 Structure/Cartesian/Closed.v 的 [Closed] 承载（其 [u0 < u1]，[exp_iso] 的 [Sets] 同构的层级），因此 [curry_functor] 和 [curry_cofunctor] 将其作为参数：[Exp_Functor] 和 [Prod_Functor] 各自承载一个在其自身类型中缺失的层级，因此在内联 [Props_Closed] 时，层级 e 将只出现在本体中。那些层级，[Curry_Adjunction] 的 [Adjunction] 的最后一层以及 [Adjunction_Comonad] 的 u4 层级，在其绑定器中为第六层（在它们的块中自由），被固定为 e 或 h。大写字母 [h <= compose.u0, compose.u1, compose.u2, ID.u0, prod_rect.u0, prod_rect.u1, prod_rect.u2] 已经是在 [Closed] 和 [Curry_Adjunction] 块中的全局标准库宇宙。[impl_PreOrder] 携带全局 [Set < Defs.u0]（标准库的 [PreOrder] 在 [Prop] 上的一个关系）。双条件 [@{u h +}] 增加其 [Prop] 侧的自由 [iffT] 级别。此文件加载 [Thin] 和 [proset_thin] 的两个声明（Structure/Thin.v 与 Instance/Proset/Order.v，以及通过 Instance/Proset/Monad.v 的 Instance/Proset/Galois.v；由 [Locate] 测量）且都未命名：证明者是项 [fun _ _ _ _ => I]。未交付。没有 Lawvere-Tierney 拓扑或核（B ⇒ − 保持交集，这一点没有说明）；没有其他模态（Awodey 的 ⋄）；在 B 中没有函子性；除了 [Props] 之外，没有关于 Heyting 代数的其他内容。
*)

(* * ** The operator and its two axioms / * ** 运算符及其两个公理 *)

(*
 j p := B → p, an endofunctor of the entailment preorder [Props]; its
 law fields are [I], the hom-setoid of [Props] being [True]. 

 --------
 j p := B → p，是蕴涵预序 [Props] 的一个自函子；其律域是 [I]，[Props] 的同构集合为 [True]。
*)
Definition modal_functor@{u h} (B : Prop) : Props@{u h} ⟶ Props@{u h} :=
  @Build_Functor Props@{u h} Props@{u h} (fun p => B → p)
    (fun p q (f : Basics.impl p q) (g : B → p) (b : B) => f (g b))
    (fun _ _ _ _ _ => I) (fun _ => I) (fun _ _ _ _ _ => I).

(*
 Seven Sketches Example 1.123's two axioms: p ⇒ j(p), and
 j(j(p)) = j(p), read as mutual entailment. 

 --------
 Seven Sketches 示例 1.123 的两个公理：p ⇒ j(p)，以及 j(j(p)) = j(p)，读作相互蕴涵。
*)
Definition modal_ext@{} (B p : Prop) : p → (B → p) := fun x _ => x.

(* The multiplication, a transparent term: the assumption used twice. / 乘法，一个透明的术语：使用了两次的假设。 *)
Definition modal_mult@{} (B p : Prop) : (B → (B → p)) → (B → p) :=
  fun f b => f b b.

Definition modal_idem@{} (B p : Prop) : (B → (B → p)) <-> (B → p) :=
  conj (modal_mult B p) (modal_ext B (B → p)).

(*
 The book's equation itself, under propositional extensionality taken
 as a hypothesis. 

 --------
 在假设命题外延性的情况下，书中的方程本身。
*)
Lemma modal_idem_ext@{} (propext : ∀ P Q : Prop, (P <-> Q) → P = Q)
  (B p : Prop) : (B → (B → p)) = (B → p).
Proof. exact (propext _ _ (modal_idem B p)). Qed.

(*
 The monad: unit the first axiom, multiplication the forward half of
 the second, every law [I]. 

 --------
 单子：单位是第一个公理，乘法是第二个公理的前半部分，每条定律 [I]。
*)
Definition modal_monad@{u h} (B : Prop) :
  @Monad Props@{u h} (modal_functor@{u h} B) :=
  @Build_Monad Props@{u h} (modal_functor@{u h} B)
    (modal_ext B) (modal_mult B)
    (fun _ _ _ => I) (fun _ => I) (fun _ => I) (fun _ => I)
    (fun _ _ _ => I).

(* Its join computes: it is the term f ↦ (b ↦ f b b). / 它的 join 计算为：它是项 f ↦ (b ↦ f b b)。 *)
Example modal_monad_join@{u h} (B p : Prop) (f : B → (B → p)) (b : B) :
  @join _ _ (modal_monad@{u h} B) p f b = f b b := eq_refl.

(* It IS Structure/Thin/Monad.v's [thin_monad] at [Props] with the witness [fun _ _ _ _ => I], on the WHOLE record: that constructor's law fields reduce to [I] by beta. / 它是 Structure/Thin/Monad.v 中的 [thin_monad]，在 [Props] 处，凭借证据 [fun _ _ _ _ => I]，在整个记录上：该构造函数的定律字段通过 beta 简化为 [I]。 *)
Example modal_monad_is_thin@{u h t} (B : Prop) :
  modal_monad@{u h} B
    = @thin_monad@{t u h} Props@{u h} (fun _ _ _ _ => I)
        (modal_functor@{u h} B) (modal_ext B) (modal_mult B) := eq_refl.

(* Its algebras are the j-closed propositions, (B → p) → p. / 它的代数是 j-封闭命题，(B → p) → p。 *)
Definition modal_talgebra_iff@{u h +} (B p : Prop) :
  @TAlgebra Props@{u h} (modal_functor B) (modal_monad B) p
    ↔ ((B → p) → p) :=
  (fun a => @t_alg Props@{u h} (modal_functor B) (modal_monad B) p a,
   fun h => @Build_TAlgebra Props@{u h} (modal_functor B) (modal_monad B) p
              h I I).

Example modal_talgebra_round@{u h p} (B p : Prop) (h : (B → p) → p) :
  match modal_talgebra_iff@{u h p} B p with
  | (to_closed, of_closed) => to_closed (of_closed h)
  end = h := eq_refl.

(* Non-vacuity: at B := False the proposition False is not closed. / 非虚空性：在 B := False 时，命题 False 并未闭合。 *)
Lemma modal_false_not_closed@{u h} :
  @TAlgebra Props@{u h} (modal_functor False) (modal_monad False) False
    → False.
Proof.
  intro a. destruct (modal_talgebra_iff False False) as [to_closed _].
  exact (to_closed a (fun x => x)).
Qed.

(* * ** The monad of the currying adjunction (− ∧ B) ⊣ (B ⇒ −) / * ** 柯里化伴随的幺半群 (− ∧ B) ⊣ (B ⇒ −) *)

(*
 The two composites of Structure/Cartesian/Closed/Adjunction.v's
 [Prod_Functor B] and [Exp_Functor B] at [Props], for a closed
 structure [CL] (in use, always [Props_Closed]).  Taking [CL] as an
 argument keeps its exponential level e in the type: [Exp_Functor] and
 [Prod_Functor] each carry a level absent from their own types, pinned
 here to e. 

 --------
 Structure/Cartesian/Closed/Adjunction.v 的两个组合 [Prod_Functor B] 和 [Exp_Functor B] 在 [Props] 的位置，对于一个闭合结构 [CL]（在使用中，总是 [Props_Closed]）。将 [CL] 作为参数会在类型中保持其指数水平 e：[Exp_Functor] 和 [Prod_Functor] 各自携带一个在它们自身类型中缺失的水平，这里固定为 e。
*)
Definition curry_functor@{u h e | h < e +}
  (CL : @Closed@{u h e} Props@{u h} Props_Cartesian@{u h}) (B : Prop) :
  Props@{u h} ⟶ Props@{u h} :=
  @Compose@{u u u e h} Props@{u h} Props@{u h} Props@{u h}
    (@Exp_Functor@{u h e e} Props@{u h} _ CL B)
    (@Prod_Functor@{u h e e} Props@{u h} _ B).

Definition curry_cofunctor@{u h e | h < e +}
  (CL : @Closed@{u h e} Props@{u h} Props_Cartesian@{u h}) (B : Prop) :
  Props@{u h} ⟶ Props@{u h} :=
  @Compose@{u u u e h} Props@{u h} Props@{u h} Props@{u h}
    (@Prod_Functor@{u h e e} Props@{u h} _ B)
    (@Exp_Functor@{u h e e} Props@{u h} _ CL B).

(*
 The monad of [Curry_Adjunction B].  The adjunction's last level is
 free in its block and is pinned to h. 

 --------
 [Curry_Adjunction B] 的单子。伴随的最后一级在其块中是自由的，并且固定在 h 上。
*)
Definition curry_monad@{u h e | h < e +} (B : Prop) :
  @Monad Props@{u h} (curry_functor@{u h e} Props_Closed B) :=
  @Adjunction_Monad@{u h u h e h} Props@{u h} Props@{u h} _ _
    (@Curry_Adjunction@{u h e e h} Props@{u h} _ _ B).

(* Its functor is B ⇒ (− ∧ B), on the nose. / 它的函子是 B ⇒ (− ∧ B)，确切如此。 *)
Example curry_monad_fobj@{u h e | h < e +} (B p : Prop) :
  fobj[curry_functor@{u h e} Props_Closed B] p = (B → p /\ B) := eq_refl.

(*
 It is not B ⇒ − by conversion (the equation of objects is refused),
 but the two functors are naturally isomorphic. 

 --------
 它不是 B ⇒ − 通过转换（对象的方程被拒绝），但两个函子自然同构。
*)
Lemma curry_modal_iso@{u h e + | h < e +} (B : Prop) :
  curry_functor@{u h e} Props_Closed B ≈ modal_functor@{u h} B.
Proof.
  unshelve eexists.
  - intro p. unshelve refine (@Build_Isomorphism Props _ _ _ _ I I).
    + exact (fun f b => proj1 (f b)).
    + exact (fun f b => conj (f b) b).
  - intros; exact I.
Qed.

(*
 Under propositional extensionality, taken as a hypothesis, the two
 object maps agree, so no proof of their difference can exist unless
 that axiom is refuted. 

 --------
 在命题外延性假设下，这两个对象映射是一致的，因此除非该公理被驳斥，否则不存在证明它们差异的证据。
*)
Lemma curry_modal_fobj_ext@{u h e | h < e +}
  (propext : ∀ P Q : Prop, (P <-> Q) → P = Q) (B p : Prop) :
  fobj[curry_functor@{u h e} Props_Closed B] p = fobj[modal_functor@{u h} B] p.
Proof.
  apply propext. split.
  - exact (fun f b => proj1 (f b)).
  - exact (fun f b => conj (f b) b).
Qed.

Definition curry_talgebra_iff@{u h e + | h < e +} (B p : Prop) :
  @TAlgebra Props@{u h} _ (curry_monad@{u h e} B) p
    ↔ ((B → p /\ B) → p) :=
  (fun a => @t_alg Props@{u h} _ (curry_monad@{u h e} B) p a,
   fun h => @Build_TAlgebra Props@{u h} _ (curry_monad@{u h e} B) p
              h I I).

(* The two monads have the same closed elements. / 这两个范畴具有相同的闭合元素。 *)
Definition curry_modal_closed_iff@{} (B p : Prop) :
  ((B → p /\ B) → p) <-> ((B → p) → p) :=
  conj (fun h f => h (fun b => conj (f b) b))
       (fun h f => h (fun b => proj1 (f b))).

(* * ** The dual: the comonad of the same adjunction, B ∧ − / * ** 对偶：相同伴随的余单子，B ∧ − *)

(*
 [Adjunction_Comonad]'s level u4 (sixth in its binder) occurs in neither
 its type nor its block; it is pinned to h, as is the adjunction's last
 level. 

 --------
 [Adjunction_Comonad] 的第 u4 级（在其活页夹中的第六级）既不出现在其类型中，也不出现在其区块中；它被固定在 h 上，就像附加的最后一级一样。
*)
Definition curry_comonad@{u h e | h < e +} (B : Prop) :
  @Comonad Props@{u h} (curry_cofunctor@{u h e} Props_Closed B) :=
  @Adjunction_Comonad@{u h u h e h h} Props@{u h} Props@{u h} _ _
    (@Curry_Adjunction@{u h e e h} Props@{u h} _ _ B).

Example curry_comonad_fobj@{u h e | h < e +} (B p : Prop) :
  fobj[curry_cofunctor@{u h e} Props_Closed B] p = ((B → p) /\ B) := eq_refl.

(* The interior operator it defines is B ∧ −, up to mutual entailment. / 它所定义的内部运算符是 B ∧ −，直至相互蕴涵。 *)
Definition curry_comonad_is_and@{} (B p : Prop) :
  ((B → p) /\ B) <-> (B /\ p) :=
  conj (fun '(conj f b) => conj b (f b))
       (fun '(conj b x) => conj (fun _ => x) b).

Definition curry_wcoalgebra_iff@{u h e + | h < e +} (B p : Prop) :
  @WCoalgebra Props@{u h} _ (curry_comonad@{u h e} B) p
    ↔ (p → (B → p) /\ B) :=
  (fun c => @w_coalg Props@{u h} _ (curry_comonad@{u h e} B) p c,
   fun h => @Build_WCoalgebra Props@{u h} _ (curry_comonad@{u h e} B) p
              h I I).

(* Its open elements are the propositions that entail B. / 它的开放元素是能推出 B 的命题。 *)
Definition curry_open_iff_entails@{} (B p : Prop) :
  (p → (B → p) /\ B) <-> (p → B) :=
  conj (fun h x => proj2 (h x)) (fun h x => conj (fun _ => x) (h x)).

(* * ** The same operator on the preorder of propositions / * ** 命题预序上的相同运算符 *)

Definition impl_PreOrder@{} : PreOrder Basics.impl :=
  {| PreOrder_Reflexive := fun _ x => x
   ; PreOrder_Transitive := fun _ _ _ f g x => g (f x) |}.

Definition modal_mono@{u} (B : Prop) :
  @MonotoneFun@{u u} Prop Basics.impl Prop Basics.impl :=
  {| mono_map := fun p => B → p
   ; mono_pres := fun p q (f : Basics.impl p q) =>
       (fun g b => f (g b)) : Basics.impl (B → p) (B → q) |}.

Definition modal_closure@{u} (B : Prop) : ClosureOperator@{u} impl_PreOrder :=
  {| cl_fun  := modal_mono B
   ; cl_ext  := modal_ext B
   ; cl_mult := modal_mult B |}.

(*
 [Props] is not [Proset impl_PreOrder] by conversion, so the two
 presentations are distinct terms; their functors agree on objects. 

 --------
 [Props] 不是通过转换得到的 [Proset impl_PreOrder]，因此这两个表示是不同的项；它们的函子在对象上是一致的。
*)
Example modal_closure_fobj@{u h} (B p : Prop) :
  fobj[closure_functor@{u h} (modal_closure@{u} B)] p
    = fobj[modal_functor@{u h} B] p := eq_refl.

(* And the two monads have the same unit and multiplication. / 这两个单子有相同的单位和乘法。 *)
Example modal_closure_ret@{u h} (B p : Prop) :
  @ret _ _ (closure_monad@{u h} (modal_closure@{u} B)) p
    = @ret _ _ (modal_monad@{u h} B) p := eq_refl.

Example modal_closure_join@{u h} (B p : Prop) :
  @join _ _ (closure_monad@{u h} (modal_closure@{u} B)) p
    = @join _ _ (modal_monad@{u h} B) p := eq_refl.
