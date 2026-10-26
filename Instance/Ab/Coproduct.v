Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Biproduct.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Coq.ZArith.ZArith.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.

Generalizable All Variables.

(* * * The direct sum is the coproduct in Ab / * * 直和是在Ab中的余积 *)

(*
 Book: Mac Lane, “Categories for the Working Mathematician” (2nd ed.),
 §III.3, book p. 63 (maclane:III.3:remark1)
 Book: Awodey, “Category Theory” (1st ed., CMU pre-print, Sept 2005),
 §3.2, Example 3.10, printed p. 64 (awodey:3.2:example10)
 Book: Riehl, “Category Theory in Context” (2nd ed.), §3.1,
 printed p. 93 (riehl:3.1:exxi)
 Wikipedia: https://en.wikipedia.org/wiki/Coproduct

 Mac Lane's §III.3 roster names the direct sum as the coproduct in Ab,
 and Awodey's Example 3.10 says exactly why it is not the free product:
 the free product of abelian groups need not be abelian, so the
 coproduct in Ab is instead carried by the underlying PRODUCT set, with
 injections a ↦ (a, 0) and b ↦ (0, b) and copairing (a, b) ↦ f a + g b.
 That is the semiadditive phenomenon, and Instance/CMon/Biproduct.v had
 already proved every line of it one layer down, for commutative
 monoids.

 HOW MUCH IS INHERITED, MEASURED RATHER THAN ASSERTED.  Instance/Ab.v
 makes [AbObject] extend [CMonObject] by a coercion
 ([ab_cmon :> CMonObject], Instance/Ab.v) and — the load-bearing
 choice — defines [AbHom A B := CMonHom A B] as a bare [Definition]
 (Instance/Ab.v), with [Ab]'s hom-setoid, identity and composition
 taken from [CMon] literally.  So an arrow of Ab IS an arrow of CMon,
 not merely one up to some comparison.

 The consequence, measured: TEN of the biproduct record's ELEVEN fields
 are supplied by Instance/CMon/Biproduct.v's constants WITH NO ADAPTER
 AT ALL, by [:=] and no tactic — the four structural morphisms, all
 four interaction laws, and both universal properties.  The ONLY new
 field is [biproduct_obj]: [Ab_product] adds the negation
 [(a, b) ↦ (−a, −b)] that a [CMonObject] does not carry, and its two
 obligations are this file's only new proof content.

 AN EARLIER DRAFT OF THIS HEADER GOT THAT WRONG AND IS CORRECTED HERE.
 It claimed that the two interaction laws comparing against [zero_mor]
 “do not transfer” and are “not even well-typed here”, on the ground
 that Ab's zero object is [Ab_Zero] while CMon's is [CMon_Zero].  That
 is FALSE, and the falsity is now machine-checked:
 [ab_zero_mor_is_cmon_zero_mor] shows the two zero morphisms are the
 SAME TERM by [eq_refl].  They are, because [Ab_Zero] is assembled from
 [Ab_Terminal] and [Ab_Initial], whose [one] and [zero] fields are
 Instance/Ab.v's [Ab_one] and [Ab_zero_hom] — and those are literally
 [CMon_one] and [CMon_zero_hom] (Instance/Ab.v).  So
 [Ab_exl_inr] and [Ab_exr_inl] are [CMon_exl_inr] and [CMon_exr_inl],
 supplied by [:=] like the rest.  The general lesson is the one the
 correction cost: at this depth of inheritance, “different record at a
 different category” is not by itself a reason for anything, and the
 convertibility has to be TESTED rather than reasoned about.

 WHAT IS PROVED, AND AT WHAT STRENGTH.  [Ab_Biproducts] inhabits
 [HasBiproducts Ab] — the first such instance outside CMon — and
 [Structure/Biproduct/Cartesian.v]'s generic bridge then yields
 [Ab_Cartesian] and [Ab_Cocartesian], the tree's first product and
 coproduct structures on Ab (neither existed: no [Ab_Cartesian],
 [Ab_product] or [Ab_Biproduct] occurred anywhere).  The identification
 of the coproduct object with the product object,
 [Ab_coprod_is_prod], holds at LEIBNIZ EQUALITY by [eq_refl], as do the
 readings of [inl], [inr] and [merge] as the concrete maps
 ([Ab_inl_is_pair_zero] and its siblings).  Non-degeneracy is proved
 rather than assumed: over ℤ ⊕ ℤ the two injections have DIFFERENT
 values at the generator ([ab_coprod_injections_differ]), and the
 copairing and both projections COMPUTE on closed input by [eq_refl]
 ([ab_coprod_merge_computes], [ab_coprod_exl_computes],
 [ab_coprod_exr_computes]).

 A UNIVERSE PIN, MEASURED AND ATTRIBUTED BUT NOT REPAIRED.
 [Ab_product@{…}] is universe-polymorphic with thirteen free binders,
 but [Ab_Biproduct@{u} : ∀ M N : AbObject@{Set Set Set}, …] and
 [Ab_Cocartesian@{u} : Cartesian@{u Set}] are PINNED at [Set].  The
 cause is located rather than guessed: Instance/Ab.v's [Ab_trivial]
 is declared with NO universe binders, at [AbObject@{Set Set Set}], and
 everything mentioning a zero morphism goes through it via [Ab_Zero].
 The contrast that identifies it is Instance/CMon/Coproduct.v, whose
 [CMon_Cocartesian@{u u0} : Cartesian@{u u0}] is FREE of any [Set] —
 because Instance/CMon/Biproduct.v's [CMon_trivial@{o}] IS
 polymorphic.  So the pin is one donor constant's, it enters exactly
 where the zero object does, and it is NOT claimed unavoidable; the
 repair belongs to Instance/Ab.v and is not made here.  Both halves are
 guarded in Test/ProbeCoproduct.v, the negative at [Ab_Biproduct] and
 the control at [Ab_product], each above [Set].

 WHAT IS NOT DELIVERED.  No indexed or infinite direct sums — the
 coproduct here is binary, matching [Cocartesian]; the indexed statement
 would need [HasIndexedCoproducts Ab], which is not built.  No
 [Additive Ab] or [Abelian Ab] instance is claimed: Instance/Ab.v
 records that it instantiates none of [Preadditive], [Additive] or
 [Abelian], and while [Structure/AbCategory.v] has since supplied
 [Ab_Preadditive], the remaining two need more than biproducts.  And
 nothing is said about coproducts in Grp, where the answer is the free
 product and no part of this file applies — that is exactly Awodey's
 point in Example 3.10, and it is why this file is about Ab. 

 --------
 书籍：Mac Lane，《为职数学家准备的范畴论》（第2版），§III.3，第63页（maclane:III.3:remark1）
 书籍：Awodey，《范畴论》（第1版，CMU预印本，2005年9月），§3.2，例3.10，第64页（awodey:3.2:example10）
 书籍：Riehl，《语境中的范畴论》（第2版），§3.1，第93页（riehl:3.1:exxi）
 维基百科：https://en.wikipedia.org/wiki/CoproductMac Lane 的 §III.3 名单将直和称为 Ab 中的余积，而 Awodey 的例 3.10 则正好说明了为什么它不是自由积：阿贝尔群的自由积不一定是阿贝尔群，因此 Ab 中的余积是由底层的乘积集合承载的，注入映射为 a ↦ (a, 0) 和 b ↦ (0, b)，而共对映射为 (a, b) ↦ f a + g b。这就是半加性现象，而 Instance/CMon/Biproduct.v 已经在一层之下为交换幺半群证明了其中的每一行。继承了多少，是通过度量而非断言。 Instance/Ab.v 使 [AbObject] 通过一个强制转换扩展 [CMonObject] ([ab_cmon :> CMonObject], Instance/Ab.v)，而——承载负载的选择——将 [AbHom A B := CMonHom A B] 定义为一个裸的 [Definition] (Instance/Ab.v)，其 [Ab] 的同态集合、恒等和组合字面上取自 [CMon]。因此，Ab 的箭头就是 CMon 的箭头，而不仅仅是在某种比较下的箭头。结果，经测量：副产品记录的十一（ELEVEN）字段中有十（TEN）个字段由 Instance/CMon/Biproduct.v 的常量提供，完全没有适配器，由 [:=] 提供，也没有策略——四个结构态射、所有四个交互律以及两个泛性质。唯一的新字段是 [biproduct_obj]：[Ab_product] 添加了一个 [(a, b) ↦ (−a, −b)] 的否定，而 [CMonObject] 不包含该否定，其两个义务是该文件中唯一的新证明内容。这个标题的早期草稿写错了，这里已更正。它声称两个与 [zero_mor] 比较的交互定律“无法转移”，并且在这里“甚至类型不正确”，理由是 Ab 的零对象是 [Ab_Zero]，而 CMon 的零对象是 [CMon_Zero]。这是错误的，现在该错误已经通过机器验证：[ab_zero_mor_is_cmon_zero_mor] 显示两个零态射在 [eq_refl] 下是相同的项。它们确实相同，因为 [Ab_Zero] 是由 [Ab_Terminal] 和 [Ab_Initial] 组装而成的，其中的 [one] 和 [zero] 字段是 Instance/Ab.v 的 [Ab_one] 和 [Ab_zero_hom]——而这些实际上就是 [CMon_one] 和 [CMon_zero_hom]（Instance/Ab.v）。所以 [Ab_exl_inr] 和 [Ab_exr_inl] 是 [CMon_exl_inr] 和 [CMon_exr_inl]，由 [:=] 提供，就像其他部分一样。总体的教训是关于纠正成本的：在这种继承深度下，“不同类别的不同记录”本身并不是任何事情的理由，而且可转换性必须经过测试而不是仅凭推理。什么被证明，以及在哪种强度下被证明。[Ab_Biproducts] 存在于 [HasBiproducts Ab]——这是 CMon 之外的第一个此类实例——然后 [Structure/Biproduct/Cartesian.v] 的通用桥梁产生了 [Ab_Cartesian] 和 [Ab_Cocartesian]，这是树在 Ab 上的第一个乘积和余积结构（它们之前不存在：没有 [Ab_Cartesian]、[Ab_product] 或 [Ab_Biproduct] 出现过）。将余积对象与乘积对象 [Ab_coprod_is_prod] 等同在 LEIBNIZ 等式下成立，由 [eq_refl] 证明，[inl]、[inr] 和 [merge] 作为具体映射（[Ab_inl_is_pair_zero] 及其相关映射）的读法同样成立。非退化性是被证明而非假设的：在 ℤ ⊕ ℤ 上，两条注入在生成元 [ab_coprod_injections_differ] 上具有不同的值，并且共配对和两个投影通过 [eq_refl] 对闭合输入进行计算（[ab_coprod_merge_computes]、[ab_coprod_exl_computes]、[ab_coprod_exr_computes]）。一个宇宙 PIN，已测量并赋值但未修复。[Ab_product@{…}] 是一个具有十三个自由绑定器的宇宙多态对象，但 [Ab_Biproduct@{u} : ∀ M N : AbObject@{Set Set Set}, …] 和 [Ab_Cocartesian@{u} : Cartesian@{u Set}] 在 [Set] 被固定。原因是定位出来的，而不是猜测的：Instance/Ab.v 的 [Ab_trivial] 在 [AbObject@{Set Set Set}] 声明时没有宇宙绑定器，并且所有提到零态射的内容都通过 [Ab_Zero] 经过它。识别它的对比是 Instance/CMon/Coproduct.v，其 [CMon_Cocartesian@{u u0} : Cartesian@{u u0}] 没有任何 [Set]——因为 Instance/CMon/Biproduct.v 的 [CMon_trivial@{o}] 是多态的。所以这个固定是一个供体常量的，它正好进入零对象所在的位置，并且并不被认为是不可避免的；修复属于 Instance/Ab.v，并且这里没有进行。两个部分都在 Test/ProbeCoproduct.v 中受到保护，负极在 [Ab_Biproduct]，控制在 [Ab_product]，每个都在 [Set] 之上。

 未提供的内容：不提供索引或无限直接和——这里的余积是二元的，匹配 [Cocartesian]；索引语句需要 [HasIndexedCoproducts Ab]，而它没有构建。没有声明 [Additive Ab] 或 [Abelian Ab] 的实例：Instance/Ab.v 记录它没有实例化 [Preadditive]、[Additive] 或 [Abelian]，虽然 [Structure/AbCategory.v] 已经提供了 [Ab_Preadditive]，但剩下的两个需要的不仅是双积。而且对 Grp 中的余积没有任何说明，其答案是自由积，这个文件的任何部分都不适用——这正是 Awodey 在示例 3.10 中指出的，这也是为什么这个文件是关于 Ab 的原因。
*)

(* * ** The direct sum as an object of Ab / * ** 作为 Ab 对象的直和 *)

(*
 The underlying commutative monoid is [CMon_product]; all that is added
 is the componentwise negation. 

 --------
 底层的交换幺半群是 [CMon_product]；所有添加的只是分量逐一取反。
*)
Program Definition Ab_product (M N : AbObject) : AbObject := {|
  ab_cmon := CMon_product M N;
  ab_neg := fun p => (ab_neg M (fst p), ab_neg N (snd p))
|}.
Next Obligation.
  intros p q [H1 H2].
  split; simpl.
  - now rewrite H1.
  - now rewrite H2.
Qed.
Next Obligation.
  split; simpl; apply ab_neg_left.
Qed.

(* * ** The four structural morphisms, inherited on the nose / * ** 四个结构态射，直接继承 *)

(*
 [Ab]'s homs, identity and composition ARE [CMon]'s, and the underlying
 commutative monoid of [Ab_product M N] IS [CMon_product M N], so each
 of these four is supplied by [:=] with no tactic and no adapter. 

 --------
 [Ab] 的同态、身份和组成是 [CMon] 的，并且 [Ab_product M N] 的底层交换幺半群是 [CMon_product M N]，因此这四个中的每一个都是由 [:=] 提供的，无需策略和适配器。
*)
Definition Ab_inl (M N : AbObject) : M ~{Ab}~> Ab_product M N :=
  CMon_inl M N.

Definition Ab_inr (M N : AbObject) : N ~{Ab}~> Ab_product M N :=
  CMon_inr M N.

Definition Ab_exl (M N : AbObject) : Ab_product M N ~{Ab}~> M :=
  CMon_exl M N.

Definition Ab_exr (M N : AbObject) : Ab_product M N ~{Ab}~> N :=
  CMon_exr M N.

(* The copairing (a, b) ↦ f a + g b — Awodey's formula — likewise. / 共配对 (a, b) ↦ f a + g b — Awodey 的公式 — 同样如此。 *)
Definition Ab_copair {M N P : AbObject}
  (f : M ~{Ab}~> P) (g : N ~{Ab}~> P) : Ab_product M N ~{Ab}~> P :=
  CMon_copair f g.

(* * ** The zero morphism of Ab is CMon's / * ** Ab 的零态射是 CMon 的 *)

(*
 The fact that makes the two [zero_mor] laws transfer: Ab's zero
 morphism and CMon's are the same term, [Ab_Zero]'s [one] and [zero]
 being [CMon_one] and [CMon_zero_hom] (Instance/Ab.v) and
 Ab's composition being CMon's. 

 --------
 使两条 [zero_mor] 定律得以转移的事实是：Ab 的零态射与 CMon 的是同一项，[Ab_Zero] 的 [one] 和 [zero] 是 [CMon_one] 和 [CMon_zero_hom]（Instance/Ab.v），且 Ab 的复合是 CMon 的复合。
*)
Example ab_zero_mor_is_cmon_zero_mor (M N : AbObject) :
  @zero_mor Ab Ab_Zero M N = @zero_mor CMon CMon_Zero M N := eq_refl.

(* Its value at a point, for readability at the use sites downstream. / 它在某一点的值，用于下游使用地点的可读性。 *)
Lemma ab_zero_mor_value (M N : AbObject) (a : carrier (cmon_setoid M)) :
  cmon_map (@zero_mor Ab Ab_Zero M N) a ≈ cmon_zero N.
Proof.
  simpl.
  apply (cmon_map_zero (Ab_zero_hom N)).
Qed.

(* * ** The four interaction laws, all four inherited on the nose / * ** 四种相互作用定律，全部四个完全继承 *)

Definition Ab_exl_inl (M N : AbObject) :
  Ab_exl M N ∘ Ab_inl M N ≈ id := CMon_exl_inl M N.

Definition Ab_exr_inr (M N : AbObject) :
  Ab_exr M N ∘ Ab_inr M N ≈ id := CMon_exr_inr M N.

Definition Ab_exl_inr (M N : AbObject) :
  Ab_exl M N ∘ Ab_inr M N ≈ @zero_mor Ab Ab_Zero N M := CMon_exl_inr M N.

Definition Ab_exr_inl (M N : AbObject) :
  Ab_exr M N ∘ Ab_inl M N ≈ @zero_mor Ab Ab_Zero M N := CMon_exr_inl M N.

(* * ** Both universal properties, inherited on the nose / * ** 两个通用属性，完全文继承 *)

(*
 The ∃! ranges over [Ab_product M N ~{Ab}~> P], which IS
 [CMon_product M N ~{CMon}~> P]; its equality is [CMonHom_Setoid], which
 IS Ab's; and the composites are [cmon_hom_compose], which IS Ab's.  So
 both universal properties are the CMon ones, verbatim. 

 --------
 ∃! 范围在 [Ab_product M N ~{Ab}~> P] 上，它是 [CMon_product M N ~{CMon}~> P]；它的等式是 [CMonHom_Setoid]，它是 Ab's；复合体是 [cmon_hom_compose]，它是 Ab's。所以两个全称属性都是 CMon 的，逐字对应。
*)
Definition Ab_is_product (M N P : AbObject)
  (f : P ~{Ab}~> M) (g : P ~{Ab}~> N) :
  ∃! h : P ~{Ab}~> Ab_product M N,
    (Ab_exl M N ∘ h ≈ f) ∧ (Ab_exr M N ∘ h ≈ g) :=
  CMon_bi_is_product M N P f g.

Definition Ab_is_coproduct (M N P : AbObject)
  (f : M ~{Ab}~> P) (g : N ~{Ab}~> P) :
  ∃! h : Ab_product M N ~{Ab}~> P,
    (h ∘ Ab_inl M N ≈ f) ∧ (h ∘ Ab_inr M N ≈ g) :=
  CMon_bi_is_coproduct M N P f g.

(* * ** The biproduct, and with it the product and coproduct structures / * ** 双积（biproduct），以及随之而来的积（product）和余积（coproduct）结构 *)

Definition Ab_Biproduct (M N : AbObject) : @Biproduct Ab Ab_Zero M N :=
  @Build_Biproduct Ab Ab_Zero M N
    (Ab_product M N)
    (Ab_inl M N)
    (Ab_inr M N)
    (Ab_exl M N)
    (Ab_exr M N)
    (Ab_exl_inl M N)
    (Ab_exr_inr M N)
    (Ab_exl_inr M N)
    (Ab_exr_inl M N)
    (Ab_is_product M N)
    (Ab_is_coproduct M N).

#[export] Instance Ab_Biproducts : @HasBiproducts Ab Ab_Zero :=
  @Build_HasBiproducts Ab Ab_Zero Ab_Biproduct.

(* Mac Lane's roster entry. [Cocartesian Ab] is the deliverable; the cartesian structure comes with it, from the same biproduct. / Mac Lane 的名册条目。[Cocartesian Ab] 是可交付成果；笛卡尔结构随之而来，来自同一副产品。 *)
#[export] Instance Ab_Cartesian : @Cartesian Ab :=
  @biproduct_Cartesian Ab Ab_Zero Ab_Biproducts.

#[export] Instance Ab_Cocartesian : @Cocartesian Ab :=
  @biproduct_Cocartesian Ab Ab_Zero Ab_Biproducts.

(** ** Strict identifications / ** 严格识别 *)

(*
 Awodey's Example 3.10 in one conversion: the coproduct of two abelian
 groups IS their product, the same object, not merely isomorphic to it. 

 --------
 Awodey 的例子 3.10 在一次转换中：两个阿贝尔群的余积就是它们的积，即相同的对象，而不仅仅是与之同构。
*)
Example Ab_coprod_is_prod (M N : AbObject) :
  @Coprod Ab Ab_Cocartesian M N = @product_obj Ab Ab_Cartesian M N :=
  eq_refl.

Example Ab_coprod_obj (M N : AbObject) :
  @Coprod Ab Ab_Cocartesian M N = Ab_product M N := eq_refl.

(* And the injections and the copairing are the concrete maps. / 而注入和共配对则是具体映射。 *)
Example Ab_inl_is_pair_zero (M N : AbObject) :
  @inl Ab Ab_Cocartesian M N = CMon_inl M N := eq_refl.

Example Ab_inr_is_zero_pair (M N : AbObject) :
  @inr Ab Ab_Cocartesian M N = CMon_inr M N := eq_refl.

Example Ab_merge_is_copair (M N P : AbObject)
  (f : M ~{Ab}~> P) (g : N ~{Ab}~> P) :
  @merge Ab Ab_Cocartesian P M N f g = CMon_copair f g := eq_refl.

(* The underlying set of the coproduct is the PRODUCT of the underlying sets — the sentence Awodey uses to distinguish Ab from Grp. / 余积的底层集合是底层集合的积——这是 Awodey 用来区分 Ab 和 Grp 的句子。 *)
Example Ab_coprod_carrier (M N : AbObject) :
  carrier (cmon_setoid (@Coprod Ab Ab_Cocartesian M N))
    = (carrier (cmon_setoid M) * carrier (cmon_setoid N))%type := eq_refl.

(** ** Non-vacuity over ℤ ⊕ ℤ / ** ℤ ⊕ ℤ 上的非空性 *)

(*
 [Instance/Rng.v]'s [ring_ab] reads the additive group off a ring, and
 [Theory/Algebra/Rig.v]'s [Int_Ring] is the axiom-free integers, so ℤ is
 available as an abelian group with no new construction. 

 --------
 [Instance/Rng.v] 的 [ring_ab] 表示一个环的加法群，而 [Theory/Algebra/Rig.v] 的 [Int_Ring] 是无公理的整数，所以 ℤ 可以作为一个阿贝尔群使用，无需新的构造。
*)
Definition ab_Z : AbObject := ring_ab Int_Ring.

(* The two injections are genuinely different maps: at the generator 1 they land at (1, 0) and at (0, 1). / 这两个注射确实是不同的映射：在生成元 1 处，它们落在 (1, 0) 和 (0, 1)。 *)
Lemma ab_coprod_injections_differ :
  cmon_map (@inl Ab Ab_Cocartesian ab_Z ab_Z) 1%Z
    ≈ cmon_map (@inr Ab Ab_Cocartesian ab_Z ab_Z) 1%Z → False.
Proof.
  intros [H _].
  simpl in H.
  discriminate H.
Qed.

(*
 And the copairing computes: with both legs the identity it is
 Awodey's (a, b) ↦ f a + g b, i.e. addition. 

 --------
 而共配对计算如下：对两个分量都是恒等映射，它是 Awodey 的 (a, b) ↦ f a + g b，即加法。
*)
Example ab_coprod_merge_computes :
  cmon_map (@merge Ab Ab_Cocartesian ab_Z ab_Z ab_Z id id) (2%Z, 3%Z)
    = 5%Z := eq_refl.

(* The two summands are not collapsed by the copairing either: the projections separate them. / 这两个加数也不会被共配对折叠：投影将它们分开。 *)
Example ab_coprod_exl_computes :
  cmon_map (Ab_exl ab_Z ab_Z) (2%Z, 3%Z) = 2%Z := eq_refl.

Example ab_coprod_exr_computes :
  cmon_map (Ab_exr ab_Z ab_Z) (2%Z, 3%Z) = 3%Z := eq_refl.
