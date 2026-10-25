Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Rep.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Grp.Galois.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Lia.

Generalizable All Variables.

(*
 Several proofs below draw on the two [PreOrder] witnesses of the section
 without naming them in the statement, so capture every section variable
 rather than the [Default Proof Using "Type"] subset inherited from Lib.v
 (the Construction/Reflective/Idempotent.v precedent). 

 --------
 下面的几个证明利用了本节的两个 [PreOrder] 证人，但在声明中没有命名它们，因此要捕获每个节变量，而不是继承自 Lib.v 的 [Default Proof Using "Type"] 子集（Construction/Reflective/Idempotent.v 的先例）。
*)
Set Default Proof Using "All".

(* * * Mac Lane's Exercise 2 at a Galois connection between posets / * * Mac Lane 的练习 2 关于偏序集合之间的伽罗瓦连接 *)

(*
 Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 Springer GTM 5, 1998, SS IV.5, printed p. 97, Exercise 2
 (catalog id maclane:IV.5:ex2)
 Book:      Riehl, "Category Theory in Context", Dover 2016, SS 4.2,
 printed p. 142, Corollary 4.2.10 (riehl:4.2:cor10)
 Wikipedia: https://en.wikipedia.org/wiki/Galois_connection
 nLab:      https://ncatlab.org/nlab/show/idempotent+monad

 Mac Lane, verbatim from the printed page:

 "In a Galois connection between posets, show that the subset
 {p | p = RLp} of P equals {p | p = Rq for some q} and give a
 bijection from this set to the subset {q | q = LRq} of Q.  What are
 these sets in the case of a group of automorphisms of a field?  Does
 this generalize to an arbitrary adjunction?"

 Construction/Reflective/FixedPoints.v answers the closing question for
 an arbitrary adjunction.  This file is the exercise as stated: the
 thin case, where the categorical equivalence collapses to a bijection
 because every hom-set of [Proset] has at most one element.

 THE POSET INSTANCE IS A SPECIALISATION, NOT A RE-PROOF.  That is the
 issue's second reviewer check, and it is met by one line:
 [galois_fixed_point_equivalence] is [adjunction_fixed_point_
 equivalence] applied to [GaloisAdjunction], with no tactic.  What this
 file adds around it is the DICTIONARY -- that invertibility of the unit
 at [a] is exactly Instance/Grp/Galois.v's [GalClosed_r], and dually --
 and the elementwise reading Mac Lane asks for, which needs
 antisymmetry.

 ANTISYMMETRY IS AN EXPLICIT HYPOTHESIS, and it has to be.  #380
 recorded that Instance/Poset.v defines [Poset] as [Proset] with the
 antisymmetry argument DISCARDED, so the two are the same category and
 nothing about equality of objects can be read off it.  Every statement
 below that mentions Leibniz [=] on the underlying order therefore takes
 an [Antisymmetric] witness in the shape
 Instance/Proset/Galois.v's [mutual_le_to_eq] consumes, and that
 lemma is reused rather than restated.  The statements that do NOT
 mention [=] -- the two dictionary biconditionals, the equivalence, and
 the two passages between the closed subsets -- take no such witness.

 WHAT IS DELIVERED, clause by clause of the exercise:

 - "{p | p = RLp}": [closed_r_eq], the elementwise reading of
 [GalClosed_r] under antisymmetry.
 - "equals {p | p = Rq for some q}": [closed_r_iff_image_eq], from
 [closed_r_eq] and Instance/Grp/Galois.v's
 [gal_closed_r_image].  The mutual-relatedness form of "is an
 image", that file's [gal_closed_r_iff], is the same fact
 stated without antisymmetry; it is cited, not applied.
 - "a bijection from this set to {q | q = LRq}": [closed_r_to_l] and
 [closed_l_to_r], with [closed_round_r] and [closed_round_l] closing
 both round trips on the FIRST projection at Leibniz [=].  The
 whole-sigma round trip is NOT claimed: [GalClosed_r] is
 [Prop]-valued, so two inhabitants of one closedness statement need
 not be equal, and no proof irrelevance is taken.
 - "What are these sets in the case of a group of automorphisms of a
 field?": NOT delivered, and the reason is that the tree carries no
 automorphism group of a field (measured: a scoped search over
 Instance/Field.v, Instance/Field/ and Instance/Rng/ returns
 nothing).  What IS delivered is the group-ACTION instance already
 in Instance/Grp/Galois.v: [group_action_fixed_point_equivalence]
 applies the general theorem to that file's own
 [group_action_adjunction], and its [closed_G_iff] / [closed_U_iff]
 answer the "what are these sets" question there -- the closed
 subsets of the group are exactly the stabilisers, and the closed
 subsets of the acted-on set exactly the fixed-point sets.
 - "Does this generalize to an arbitrary adjunction?":
 Construction/Reflective/FixedPoints.v, cited here.

 RIEHL'S COROLLARY 4.2.10 is [gal_lrl_eq] and [gal_rlr_eq]: his

 "F G F = F   and   G F G = G"

 proved from Instance/Grp/Galois.v's four closure inequalities plus
 antisymmetry, exactly as he does it ("By the triangle identities
 F(a) <= FGF(a) <= F(a) for all a in A, whence F = FGF.  The other
 formula is dual.").  Both are terms with no tactic beyond the
 [mutual_le_to_eq] application.  His illustration -- the direct-image /
 inverse-image connection, where

 "f(X) = f(f^{-1}(f(X)))   and   f^{-1}(f(f^{-1}(Y))) = f^{-1}(Y)"

 hold although "neither of the inclusions X subset f^{-1}(f(X)) or
 f(f^{-1}(Y)) subset Y need be equalities" -- is [image_preimage_image]
 and [preimage_image_preimage], stated at the carriers' [≈] because
 Leibniz equality of two elements of [Powerset_Prop_obj] would need
 both propositional and functional extensionality.  The two
 non-equalities are ALREADY IN TREE: Instance/Powerset.v's
 [unit_not_iso] and [counit_not_iso] refute exactly those
 two inclusions at the constant map on a two-element carrier, so they
 are cited here and not restated -- a correction to this issue's own
 plan, which asked for them to be built.

 A COMPUTING WITNESS.  Section (G) reads the whole dictionary off
 Instance/Proset/Galois.v's [nat_shift_galois k], truncated
 subtraction left adjoint to addition on the naturals: the closed
 elements on the left are exactly the [a] with [k <= a]
 ([nat_shift_closed_r_iff]), the closed elements on the right are ALL
 of them ([nat_shift_closed_l_all]), and at [k := 2] the restricted
 left adjoint carries the fixed object [5] to [3] by [eq_refl].  So the
 exercise's bijection is here the bijection between {a | 2 <= a} and
 the naturals, with the left side a PROPER subset -- [1] is not closed
 and [5] is.

 UNIVERSES, measured off both binder and constraint block.  Sections
 (E) and (G) keep the two carrier types at SEPARATE free universes and
 relate neither to the order; the hom-with-proof identification that
 [unit_fixed_iff_closed_r] displays inside [IsIsomorphism] is
 [Adjunction]'s, inherited.  Exactly FIVE of the 27 constants carry a
 word-bounded [Set], always as a strict LOWER bound and never as an
 equation -- [Set < u] at [image_preimage_image] and
 [preimage_image_preimage], [Set < u] together with [Set < u1] at
 [image_closed_l] and [preimage_closed_r], and [Set < u9] at
 [group_action_fixed_point_equivalence] -- and all five are in
 sections (F) and (H): it comes from [Powerset_Prop_obj], whose own
 block carries it (#382 and #384 attribute that; it is not
 re-attributed here).  The [nat] witnesses
 carry NO [Set] -- a prediction this file's plan made and measurement
 refuted, [nat_shift_galois] being over the monomorphic [nat] with no
 universe of its own.

 NOT DELIVERED besides the field question: no antisymmetric quotient of
 a preorder, so the two "sets" are subtypes of a preorder rather than of
 a poset; no naturality of any identification in the connection; no
 comparison of [closed_r_to_l] with the equivalence's own functor
 beyond their agreement on the underlying element; and no lattice
 structure on the closed elements. 

 --------
 书籍：      Mac Lane, 《为工作数学家准备的范畴论》，第2版，
 Springer GTM 5, 1998, 第 IV.5 节, 印刷页 97, 练习 2
 (目录编号 maclane:IV.5:ex2)
 书籍：      Riehl, 《语境中的范畴论》，Dover 2016, 第 4.2 节,
 印刷页 142, 推论 4.2.10 (riehl:4.2:cor10)
 维基百科： https://en.wikipedia.org/wiki/Galois_connection 
 nLab:      https://ncatlab.org/nlab/show/idempotent+monad 

 Mac Lane，原文摘自印刷页：

 “在偏序集之间的伽罗瓦联系中，证明子集
 {p | p = RLp} ⊆ P 等于 {p | p = Rq 对某些 q成立}，并给出
 从该集合到 Q 中子集 {q | q = LRq} 的双射。对于一个域的自同构群，这些集合是什么？
 这是否可以推广到任意的余附伴？”Construction/Reflective/FixedPoints.v 回答了任意伴随问题的结束问题。这个文件是按原题要求的练习：薄情况，其中范畴等价退化为一个一一对应，因为 [Proset] 的每个 Hom 集最多只有一个元素。

 偏序集实例是一个特化，而不是重新证明。这是该问题第二位审稿人的检查点，通过一行代码即可满足：[galois_fixed_point_equivalence] 是将 [adjunction_fixed_point_equivalence] 应用于 [GaloisAdjunction] 的结果，无需策略。这个文件在其周围添加的是词典——在 [a] 上单位的可逆性恰好是 Instance/Grp/Galois.v 中的 [GalClosed_r]，且对偶相同——以及 Mac Lane 要求的逐元素阅读，这需要反对称性。反对称性是一个明确的假设，并且它必须是这样。#380
 记录显示 Instance/Poset.v 将 [Poset] 定义为 [Proset]，并且丢弃了反对称性参数，所以两者是相同的范畴，不能从中读取对象的相等性。下面每一条提到基础序上的 Leibniz [=] 的声明，因此都采用了 Instance/Proset/Galois.v 中 [mutual_le_to_eq] 所采用的 [Antisymmetric] 见证，并且该引理是重复使用的，而不是重新陈述。那些没有提到 [=] 的声明——两个字典二重条件、等价性，以及闭合集合之间的两段转换——则不需要这样的见证。

 练习的每个条款所交付的内容如下：- “{p | p = RLp}”：[closed_r_eq]，在反对称性下 [GalClosed_r] 的按元素读取。- “等于 {p | p = Rq 对某些 q}”：[closed_r_iff_image_eq]，来自 [closed_r_eq] 和 Instance/Grp/Galois.v 的 [gal_closed_r_image]。“是一个映射”的相互关联形式，该文件的 [gal_closed_r_iff]，是在没有反对称性情况下陈述的相同事实；它被引用，但未被应用。- “从该集合到 {q | q = LRq} 的双射”：[closed_r_to_l] 和 [closed_l_to_r]，同时 [closed_round_r] 和 [closed_round_l] 完成了在 Leibniz [=] 上对 FIRST 投影的双程。整个 sigma 双程并未被声明：[GalClosed_r] 是 [Prop] 值，因此一个闭合性陈述的两个元素不必相等，且未采取证明无关性。- “在一个域的自同构群的情况下，这些集合是什么？”：未提供，原因是该树没有域的自同构群（测量：对 Instance/Field.v、Instance/Field/ 和 Instance/Rng/ 进行范围搜索未返回任何结果）。已提供的是已经在 Instance/Grp/Galois.v 中的群作用（group-ACTION）实例：[group_action_fixed_point_equivalence] 将一般定理应用于该文件自身的 [group_action_adjunction]，其 [closed_G_iff] / [closed_U_iff] 回答了那里“这些集合是什么”这个问题——群的闭合子集正好是稳定子，而被作用集的闭合子集正好是定点集。- “这能推广到任意伴随对吗？”：引用了 Construction/Reflective/FixedPoints.v。RIEHL 的推论 4.2.10 是 [gal_lrl_eq] 和 [gal_rlr_eq]：他的

 “F G F = F 并且 G F G = G”

 从 Instance/Grp/Galois.v 的四个闭合不等式加上反对称性证明，完全按照他的做法（“根据三角恒等式 F(a) <= FGF(a) <= F(a) 对所有 a 属于 A，因此 F = FGF。另一个公式是对偶的。”）。两个都是没有策略的项，除了 [mutual_le_to_eq] 的应用。他的例子——直接像 / 逆像的联系，其中

 “f(X) = f(f^{-1}(f(X))) 并且 f^{-1}(f(f^{-1}(Y))) = f^{-1}(Y)”尽管“两个包含关系 X ⊆ f^{-1}(f(X)) 或 f(f^{-1}(Y)) ⊆ Y 不一定是等号”——是 [image_preimage_image] 和 [preimage_image_preimage]，在载体的 [≈] 中陈述，因为 [Powerset_Prop_obj] 中两个元素的莱布尼茨相等性将需要命题性和函数性外延性。这两个非等式已经在 TREE 中：Instance/Powerset.v 的 [unit_not_iso] 和 [counit_not_iso] 精确地反驳了双元素载体上的常数映射的这两个包含关系，所以这里引用它们而不重新陈述——这是对本期计划的一个修改，本期计划要求构建这些内容。一个计算见证者。章节 (G) 从 Instance/Proset/Galois.v 的 [nat_shift_galois k] 读出整个字典，截断的减法作为自然数加法的左伴随：左边的闭元素正是 [a] 与 [k <= a] ([nat_shift_closed_r_iff])，右边的闭元素是它们的全部 ([nat_shift_closed_l_all])，且在 [k := 2] 处，受限的左伴随将固定对象 [5] 通过 [eq_refl] 映射到 [3]。因此，练习的双射在这里就是 {a | 2 <= a} 与自然数之间的双射，左边是一个真子集——[1] 不是闭合的，而 [5] 是闭合的。宇宙，同时由绑定器和约束块测量。部分(E)和(G)将两种载体类型保持在独立的自由宇宙中，并且不将它们与顺序相关联；[unit_fixed_iff_closed_r]在[IsIsomorphism]中显示的带证明的同类标识是继承自[Adjunction]的。在27个常量中恰好有五个常量携带一个字界定的[Set]，总是作为严格的下界，从不作为方程——[Set < u]在[image_preimage_image]和[preimage_image_preimage]，[Set < u]与[Set < u1]一起在[image_closed_l]和[preimage_closed_r]，以及[Set < u9]在[group_action_fixed_point_equivalence]——并且全部五个都在(F)和(H)部分：它来源于[Powerset_Prop_obj]，其自身的块携带它（#382和#384标明了这一点；这里没有重新标注）。[nat] 目击者不携带 [Set]——这是本文件计划的预测，但测量结果驳斥了这一点，[nat_shift_galois] 位于单态 [nat] 之上，没有自己的宇宙。

 除了场问题之外未提供：预序不存在反对称商，因此两个“集合”是预序的子类型而非偏序集的子类型；在连接中的任何识别都没有自然性；没有对 [closed_r_to_l] 与该等价自身函子之间的比较，除了它们在底层元素上的一致；封闭元素上也没有格结构。
*)

(* * ** (E) The dictionary, the equivalence, and Mac Lane's bijection / * **（E）字典、等价性以及Mac Lane的双射 *)

Section GaloisFixed.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (G : GaloisConnection RA RB).

Definition GAdj := GaloisAdjunction PA PB G.

(*
 Invertibility of the unit at [a] IS closedness of [a].  In a thin
 category an isomorphism is a reverse arrow and nothing else: the
 forward direction is the projection [two_sided_inverse], and the
 backward direction supplies the two inverse laws with [I], since
 [Proset]'s hom-setoid identifies every pair of parallel arrows.
 [GalClosed_r] is [Prop]-valued while [IsIsomorphism] lands in [Type];
 that costs nothing here, because a reverse arrow of [Proset PA] IS a
 proof of [RA], so the [Prop] is literally the [two_sided_inverse]
 field. 

 --------
 单位在 [a] 的可逆性就是 [a] 的封闭性。在薄范畴中，同构就是一个反向箭头，仅此而已：正向方向是投影 [two_sided_inverse]，而反向方向提供两个逆律与 [I]，因为 [Proset] 的同态集识别每对平行箭头。[GalClosed_r] 是 [Prop] 值类型，而 [IsIsomorphism] 的取值在 [Type]；这里没有任何成本，因为 [Proset PA] 的反向箭头就是 [RA] 的证明，所以 [Prop] 实际上就是 [two_sided_inverse] 场。
*)
Lemma unit_fixed_iff_closed_r (a : A) :
  IsIsomorphism (@unit (Proset PB) (Proset PA) _ _ GAdj a)
    ↔ GalClosed_r G a.
Proof.
  split.
  - intro H; exact (@two_sided_inverse (Proset PA) _ _ _ H).
  - intro H.
    exact (@Build_IsIsomorphism (Proset PA) _ _ _ H I I).
Defined.

Lemma counit_fixed_iff_closed_l (b : B) :
  IsIsomorphism (@counit (Proset PB) (Proset PA) _ _ GAdj b)
    ↔ GalClosed_l G b.
Proof.
  split.
  - intro H; exact (@two_sided_inverse (Proset PB) _ _ _ H).
  - intro H.
    exact (@Build_IsIsomorphism (Proset PB) _ _ _ H I I).
Defined.

(*
 The exercise's closing question, answered at a Galois connection by
 pure instantiation of the general theorem. 

 --------
 练习的结束问题，通过纯粹实例化一般定理，在伽罗瓦连接处得到解答。
*)
Definition galois_fixed_point_equivalence :
  EquivalenceOfCategories (FixedL GAdj) :=
  adjunction_fixed_point_equivalence GAdj.

Definition galois_fixed_point_equivalence_swap :
  EquivalenceOfCategories (FixedR GAdj) :=
  fixed_point_equivalence_swap GAdj.

(* * *** Riehl Corollary 4.2.10, the thin fixed-point formulae / * *** Riehl 推论 4.2.10，薄不动点公式 *)

Lemma gal_lrl_eq (antiB : @Antisymmetric B eq eq_equiv RB) (a : A) :
  gal_l G (gal_r G (gal_l G a)) = gal_l G a.
Proof.
  refine (mutual_le_to_eq PB antiB
            (x := gal_l G (gal_r G (gal_l G a))) (y := gal_l G a) _).
  exact (@Build_Isomorphism (Proset PB) _ _
           (gal_lrl_below PA G a) (gal_lrl_above PB G a) I I).
Qed.

Lemma gal_rlr_eq (antiA : @Antisymmetric A eq eq_equiv RA) (b : B) :
  gal_r G (gal_l G (gal_r G b)) = gal_r G b.
Proof.
  refine (mutual_le_to_eq PA antiA
            (x := gal_r G (gal_l G (gal_r G b))) (y := gal_r G b) _).
  exact (@Build_Isomorphism (Proset PA) _ _
           (gal_rlr_below PA G b) (gal_rlr_above PB G b) I I).
Qed.

(* * *** Mac Lane's two subsets, elementwise / * *** 马克·莱恩的两个子集，按元素逐个 *)

(* "{p | p = RLp}", with the equation oriented as Mac Lane writes it. / "{p | p = RLp}"，方程按照麦克莱恩的写法排列。 *)
Lemma closed_r_eq (antiA : @Antisymmetric A eq eq_equiv RA) (a : A) :
  GalClosed_r G a ↔ gal_r G (gal_l G a) = a.
Proof.
  split.
  - intro H.
    refine (mutual_le_to_eq PA antiA
              (x := gal_r G (gal_l G a)) (y := a) _).
    exact (@Build_Isomorphism (Proset PA) _ _ H (gal_unit G PB a) I I).
  - intro Heq; unfold GalClosed_r; rewrite Heq.
    exact (@reflexivity A RA (@PreOrder_Reflexive A RA PA) a).
Qed.

Lemma closed_l_eq (antiB : @Antisymmetric B eq eq_equiv RB) (b : B) :
  GalClosed_l G b ↔ gal_l G (gal_r G b) = b.
Proof.
  split.
  - intro H.
    refine (mutual_le_to_eq PB antiB
              (x := gal_l G (gal_r G b)) (y := b) _).
    exact (@Build_Isomorphism (Proset PB) _ _ (gal_counit G PA b) H I I).
  - intro Heq; unfold GalClosed_l; rewrite Heq.
    exact (@reflexivity B RB (@PreOrder_Reflexive B RB PB) b).
Qed.

(*
 "... equals {p | p = Rq for some q}".  Forward through [closed_r_eq],
 backward through Instance/Grp/Galois.v's [gal_closed_r_image]; the
 mutual-relatedness form of the same fact is that file's
 [gal_closed_r_iff], which antisymmetry would turn into Mac
 Lane's equation and which is not applied here. 

 --------
 "... 等于 {p | p = Rq 对某些 q}”。正向通过 [closed_r_eq]，反向通过 Instance/Grp/Galois.v 的 [gal_closed_r_image]；相同事实的相互关联形式是该文件的 [gal_closed_r_iff]，反对称性会将其转化为 Mac Lane 方程，但此处未应用。
*)
Lemma closed_r_iff_image_eq (antiA : @Antisymmetric A eq eq_equiv RA)
  (a : A) : GalClosed_r G a ↔ ∃ b : B, a = gal_r G b.
Proof.
  split.
  - intro H.
    exact (gal_l G a; eq_sym (fst (closed_r_eq antiA a) H)).
  - intros [b Heq]; rewrite Heq.
    exact (gal_closed_r_image PA G b).
Qed.

Lemma closed_l_iff_image_eq (antiB : @Antisymmetric B eq eq_equiv RB)
  (b : B) : GalClosed_l G b ↔ ∃ a : A, b = gal_l G a.
Proof.
  split.
  - intro H.
    exact (gal_r G b; eq_sym (fst (closed_l_eq antiB b) H)).
  - intros [a Heq]; rewrite Heq.
    exact (gal_closed_l_image PB G a).
Qed.

(* * *** The bijection between the two sets of closed elements / * *** 两个闭合元素集合之间的双射 *)

Definition closed_r_to_l (p : ∃ a : A, GalClosed_r G a) :
  ∃ b : B, GalClosed_l G b :=
  (gal_l G `1 p; gal_closed_l_image PB G `1 p).

Definition closed_l_to_r (q : ∃ b : B, GalClosed_l G b) :
  ∃ a : A, GalClosed_r G a :=
  (gal_r G `1 q; gal_closed_r_image PA G `1 q).

(*
 Both round trips return the underlying element on the nose.  The whole
 sigma is not compared: the second component is a [Prop] and no proof
 irrelevance is available. 

 --------
 两次往返都精确返回底层元素。整个 sigma 没有被比较：第二个分量是一个 [Prop]，并且没有可用的证明无关性。
*)
Lemma closed_round_r (antiA : @Antisymmetric A eq eq_equiv RA)
  (p : ∃ a : A, GalClosed_r G a) :
  `1 (closed_l_to_r (closed_r_to_l p)) = `1 p.
Proof. exact (fst (closed_r_eq antiA `1 p) `2 p). Qed.

Lemma closed_round_l (antiB : @Antisymmetric B eq eq_equiv RB)
  (q : ∃ b : B, GalClosed_l G b) :
  `1 (closed_r_to_l (closed_l_to_r q)) = `1 q.
Proof. exact (fst (closed_l_eq antiB `1 q) `2 q). Qed.

End GaloisFixed.

(* * ** (F) Riehl's illustration: the direct-image / inverse-image pair / * **（F）Riehl 的插图：直接像 / 反像对 *)

Section PowersetFixed.

Context {X Y : SetoidObject}.
Context (f : X ~{Sets}~> Y).

(* "f(X) = f(f^{-1}(f(X)))", at the power set's own [≈]. / "f(X) = f(f^{-1}(f(X)))"，在幂集自身的 [≈] 上。 *)
Lemma image_preimage_image (S : carrier (Powerset_Prop_obj X)) :
  Powerset_Prop_image f
      (Powerset_Prop_preimage f (Powerset_Prop_image f S))
    ≈ Powerset_Prop_image f S.
Proof.
  apply subset_le_antisym.
  - exact (gal_lrl_below (subset_le_preorder X)
             (image_preimage_galois f) S).
  - exact (gal_lrl_above (subset_le_preorder Y)
             (image_preimage_galois f) S).
Qed.

(* "f^{-1}(f(f^{-1}(Y))) = f^{-1}(Y)". *)
Lemma preimage_image_preimage (T : carrier (Powerset_Prop_obj Y)) :
  Powerset_Prop_preimage f
      (Powerset_Prop_image f (Powerset_Prop_preimage f T))
    ≈ Powerset_Prop_preimage f T.
Proof.
  apply subset_le_antisym.
  - exact (gal_rlr_below (subset_le_preorder X)
             (image_preimage_galois f) T).
  - exact (gal_rlr_above (subset_le_preorder Y)
             (image_preimage_galois f) T).
Qed.

(* Every direct image is closed on the right-hand side, every inverse image on the left: the two instances of the general closure facts. / 每个直接像在右侧封闭，每个逆像在左侧：一般封闭性质的两个实例。 *)
Definition image_closed_l (S : carrier (Powerset_Prop_obj X)) :
  GalClosed_l (image_preimage_galois f) (Powerset_Prop_image f S) :=
  gal_closed_l_image (subset_le_preorder Y) (image_preimage_galois f) S.

Definition preimage_closed_r (T : carrier (Powerset_Prop_obj Y)) :
  GalClosed_r (image_preimage_galois f) (Powerset_Prop_preimage f T) :=
  gal_closed_r_image (subset_le_preorder X) (image_preimage_galois f) T.

End PowersetFixed.

(* * ** (G) A computing witness on the naturals / * **（G）自然数上的计算见证 *)

(*
 [nat_shift_galois k] has [gal_l n = n - k] (truncated) and
 [gal_r m = m + k], so the composite [gal_r (gal_l a)] is [max a k] and
 an element of the left-hand order is closed exactly when [k <= a]. 

 --------
 [nat_shift_galois k] 拥有 [gal_l n = n - k]（已截断）和 [gal_r m = m + k]，因此复合 [gal_r (gal_l a)] 是 [max a k]，并且当 [k <= a] 时，左侧序的一个元素是封闭的。
*)
Lemma nat_shift_closed_r_iff (k a : nat) :
  GalClosed_r (nat_shift_galois k) a ↔ Nat.le k a.
Proof.
  unfold GalClosed_r; simpl; split; intro H; lia.
Qed.

(* On the right-hand side every element is closed: [(b + k) - k] is [b]. / 在右侧，每个元素都是封闭的：[(b + k) - k] 是 [b]。 *)
Lemma nat_shift_closed_l_all (k b : nat) :
  GalClosed_l (nat_shift_galois k) b.
Proof. unfold GalClosed_l; simpl; lia. Qed.

(* The left-hand closed elements are a PROPER subset: [1] is outside and [5] is inside, at [k := 2]. / 左侧闭合元素是一个真子集：[1] 在外部，而 [5] 在 [k := 2] 内部。 *)
Example nat_shift_two_one_not_closed :
  GalClosed_r (nat_shift_galois 2%nat) 1%nat → False.
Proof. intro H; pose proof (fst (nat_shift_closed_r_iff 2 1) H); lia. Qed.

Definition nat_shift_five_closed :
  GalClosed_r (nat_shift_galois 2%nat) 5%nat :=
  snd (nat_shift_closed_r_iff 2%nat 5%nat) (ltac:(lia)).

Example nat_shift_gal_l_five :
  gal_l (nat_shift_galois 2%nat) 5%nat = 3%nat := eq_refl.

(*
 [5] as an object of the unit-fixed subcategory of the shift
 adjunction, and the restricted left adjoint's value there. 

 --------
 [5] 作为移位伴随的单位固定子范畴的一个对象，以及受限左伴随在那里的值。
*)
Definition nat_shift_five_fixed :
  obj[Sub (Proset Nat.le_preorder)
        (UnitFixed (nat_shift_adjunction 2%nat))] :=
  (5%nat; snd (unit_fixed_iff_closed_r Nat.le_preorder Nat.le_preorder
                 (nat_shift_galois 2%nat) 5%nat) nat_shift_five_closed).

Example nat_shift_FixedL_obj :
  `1 (fobj[FixedL (nat_shift_adjunction 2%nat)] nat_shift_five_fixed)
    = 3%nat := eq_refl.

(* * ** (H) Mac Lane's "what are these sets", for a group action / * **（H）麦克莱恩的“这些集合是什么”，用于群作用 *)

(*
 The field question is out of reach in this tree; the group-ACTION
 Galois connection of Instance/Grp/Galois.v is the available reading,
 and the general theorem applies to it with no tactic.  That file's
 [closed_G_iff] and [closed_U_iff] identify the two sets of closed
 elements: the closed subsets of the group are exactly the stabilisers,
 and the closed subsets of the acted-on set exactly the fixed-point
 sets. 

 --------
 该树中的场问题无法触及；Instance/Grp/Galois.v 中的群-作用 Galois 连接是可用的读数，而且一般定理可以直接应用于它，而无需使用策略。该文件的 [closed_G_iff] 和 [closed_U_iff] 标识了两组封闭元素：群的封闭子集正好是稳定子，而被作用集合的封闭子集正好是不动点集。
*)
Definition group_action_fixed_point_equivalence
  (G : GrpObject) (A : MSetoidAction (grp_mon G)) :
  EquivalenceOfCategories (FixedL (group_action_adjunction G A)) :=
  adjunction_fixed_point_equivalence (group_action_adjunction G A).
