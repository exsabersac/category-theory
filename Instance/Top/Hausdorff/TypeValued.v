Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Reflective.
Require Import Category.Adjunction.GAFT.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.StoneCech.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Complete.Refutations.

Generalizable All Variables.

(* * * Hausdorff spaces over the Type-valued [Top] / * * 关于取值类型 [Top] 的豪斯多夫空间 *)

(*
 Mac Lane, “Categories for the Working Mathematician”, 2nd ed. (GTM 5),
 §V.9, book p. 135 (PDF p. 144), read from the page image,
 Proposition 2 (catalog id maclane:V.9:prop2): the inclusion
 Haus → Top has a left adjoint H, “obtained by the adjoint functor
 theorem”.  The statement over Instance/Top/Prop.v's [PTopCat] is
 Instance/Top/Hausdorff.v's; this file records what holds over
 Instance/Top.v's Type-valued [Top].
 Riehl, “Category Theory in Context”, §4.7, printed p. 180 (PDF p. 200),
 read from the page image, Exercise 4.7.ii (riehl:4.7:exii), the same
 reflector “by Theorem 4.7.3”
 nLab:      https://ncatlab.org/nlab/show/Hausdorff+space

 BACKGROUND.  Instance/Top.v's [Top@{h o}] has Type-valued opens, and
 its homs sit strictly above its points ([o < h]; that file's header,
 point 2).  Its Hausdorff subcategory, [HausdorffSpaces], is defined
 by the classical negative axiom [IsHausdorff], which Mac Lane uses
 without defining it (book p. 158, §VI.9), and whose separating opens
 are data.  The completeness of [CompHaus], the premise the adjoint
 functor theorem needs there, is refuted under informative excluded
 middle (Instance/Top/Complete/Refutations.v's
 [CompHaus_not_complete_below_IEM], through Instance/Top/StoneCech/
 Refutations.v's [CompHaus_ArrowIndex_of_Top]).  The same argument
 with the compactness clause dropped reaches Haus.  The direct
 reflection below, [TopT2_Reflective], is onto another subcategory,
 [TSepSub tprem_T2], the spaces of the positive and truncated T2; it
 needs no completeness and no solution set, and is not walled, once
 the separation premise alone is a proposition.

 THE DIRECT REFLECTION.  A premise [TSepPremise] reads a proposition
 off a family of Type-valued opens; [tprem_T2] is nLab's constructive
 Hausdorff premise with the meeting point truncated
 ([inhabited { z & U z * V z }]), and [TSep prem X] says that it forces
 the points' equality.  [TSepQuot] is the intersection-of-separating-
 relations quotient of Instance/Top/Separation.v, built on
 Instance/Top/Subspace/TypeValued.v's [TQuot]; [TSepLaws] asks two laws
 ([tl_pull], [tl_equiv]).  [TSep_Reflective] assembles the reflection
 by universal arrows, and [TopT2_Reflective] is the largest Hausdorff
 quotient over [Top].  [IsHausdorff_TSep2_nn]: Instance/Top.v's
 [IsHausdorff] gives this T2 only under a double negation.

 THE ADJOINT FUNCTOR THEOREM AT Haus ⟶ Top.  [GAFT_TopHaus] states
 Adjunction/GAFT.v's [GAFT] at [Incl Top Hausdorff_Subcategory]; it is
 accepted.  [TopHaus_not_complete] is Freyd's argument
 (Structure/Complete/Freyd.v's [freyd_no_separated_pair]) at
 [HausdorffSpaces], with the two points of [Bool_Discrete] as the
 separated pair, both spaces Hausdorff at every universe of the
 predicate and of its separating opens ([tophaus_bool_hausdorff],
 [tophaus_point_hausdorff], whose opens are propositions; Instance/Top/
 StoneCech.v's [Discrete_Hausdorff] separates by the opens [z ≈ x],
 which sit at the points' universe); [TopHaus_ArrowIndex_of_Top]
 restricts an arrow index of [Top] to [HausdorffSpaces]; and
 [TopHaus_not_complete_below_IEM] feeds it the index that
 Instance/Top/Complete/Refutations.v's [Top_ArrowIndex_transport]
 carries from Instance/Top/StoneCech/Refutations.v's
 [ObjDecEq_of_IEM].  So [GAFT_TopHaus_vacuous]: under [IEM], the
 hypotheses of [GAFT_TopHaus] cannot all hold, at every universe
 instance of [GAFT_TopHaus] (UNIVERSES, below).

 STRENGTHS.  No [eq_refl] readback is claimed.  One [Defined], counted
 by token ([tsep_universal]), by the data convention: flipped alone to
 [Qed] in a scratch copy, every readback of this file, of
 Instance/Top/Separation.v, of Instance/Top/Hausdorff.v and of
 Test/ProbeHausdorff461.v stays accepted.  17 [Qed], counted by token.
 Every constant is closed under the global context ([Print
 Assumptions] on each); [IEM] is a hypothesis of the two refutations,
 never an axiom.

 UNIVERSES, read by [About] under [Set Printing Universes] on all 48
 constants of this file's [Print Module] listing (the record
 constructor [Build_TSepLaws] among them; no [Program] obligation).
 - The premise, the laws and the quotient's relation and setoid:
 [@{o}], empty blocks; [TSepPremise@{o}]'s sort is
 [Type@{max(Set+1,o+1)}], the relations it returns being
 Prop-valued.
 [TSepQuot] and [TSepQuot_sep] add the caps
 [o <= projections.u0], [o <= projections.u1], [TQuot]'s own.
 - The mediator ([tsep_ker] through [tsep_med]): [@{o u}] with
 [o < u], the hom universe of [ContinuousMorphism@{u u0}], whose
 block is [u0 < u].
 - [TSepSub], [TSep_Full]: [@{o h}] with [o < h], [Top]'s own;
 [TSepSpaces] and the reflection's constants add [h < u], the
 auxiliary of Construction/Subcategory.v's [Sub] above the hom
 universe, and [<=]-related auxiliaries; the strict stdlib cap
 [o < Projections.u0] is first carried by [tsep_universal].
 [TopT2_Reflective@{o h u u0 u1 u2}]: [o < h], [h < u], nothing
 mentions [Set].
 - [IsHausdorff_TSep2_nn@{o u u0 u1}]: [IsHausdorff]'s own four
 universes and bounds.
 - [tophaus_bool_hausdorff@{t p q o}], [tophaus_point_hausdorff]:
 [IsHausdorff]'s block ([p < t], [q < t], [p <= o], [q <= o],
 [o <= t]).  [TopHaus_Bool], [TopHaus_Point], [tophaus_pt_bool]:
 the nine universes of [HausdorffSpaces] named, [@{c hh h t s a o p
 q}] (its objects and homs, [Top]'s homs, the predicate, two
 auxiliaries, the points, the two opens), and exactly the eleven
 constraints of [HausdorffSpaces]'s own block.
 [TopHaus_not_complete@{r s c hh h t sh a o p q}] adds [s <= r] and
 [hh <= r], [Complete]'s own.  [TopHaus_not_complete_below_IEM]
 reads [HausdorffSpaces] with its homs at [Top]'s, [h], and its
 objects at any [c] with [h <= c]: [TopHaus_not_complete]'s
 constraints at [hh := h], and [o < s].
 - [GAFT_TopHaus_vacuous@{e h o u u0 u1 u2 u3 u4 u6}]: the hypotheses
 are written at [GAFT_TopHaus]'s own instance, nine of its ten
 universes named (the tenth occurs in no hypothesis), and the
 [About] block carries every constraint of [GAFT_TopHaus]'s and
 adds only eight stdlib caps, each of the form [h <= _] or [o <= _]
 on a stdlib universe (compared by script).  In particular the
 objects of the Hausdorff subcategory sit at any [u4] with
 [h <= u4], its predicate at any [u] with [o <= u <= u4], and its
 separating opens at any [u2], [u3] below [u] and at or below [o].
 Test/ProbeHausdorff461.v pins this with the constraint list closed
 by strict inequalities, so that no equation among them can be
 inferred: [p461_vacuous_apart] reads the theorem with the objects
 strictly above [h], the predicate strictly between [o] and [h] and
 the opens strictly below [o], and [p461_not_complete_above] the
 refutation of completeness with the objects strictly above [h].
 The two spaces' own lemmas are what reach opens below the points:
 [Discrete_Hausdorff] read there is refused, that file's N11
 (“Cannot enforce o = p because p < o”), where
 [tophaus_bool_hausdorff] is accepted ([p461_bool_opens_below]).
 - No block carries an equation.  A word count of [Set] over the
 [About] output of the 48 constants reads 1, [TSepPremise]'s
 sort.

 NOT DELIVERED.  The reflector over [Top] by [GAFT] (vacuous under
 [IEM], above; without [IEM] neither obtained nor refuted); a
 reflection of [HausdorffSpaces], the subcategory of the negative
 form, by any route; [GAFT] at [TSepSub tprem_T2]; T0 and T1 over
 [Top] beyond Instance/Top/Kolmogorov.v's T0 reflection; a comparison
 of [TopT2_Reflective] with Instance/Top/Hausdorff.v's reflector
 across the two encodings; completeness of [TSepSpaces]; Exercises 4
 and 5 over [Top]. 

 --------
 Mac Lane，《为工作数学家准备的范畴论》，第2版（GTM 5），§V.9，书籍第135页（PDF第144页），从页面图像阅读，命题2（目录ID maclane:V.9:prop2）：包含函子 Haus → Top 有一个左伴随 H，“由伴随函子定理得到”。在 Instance/Top/Prop.v 中的 [PTopCat] 的陈述在 Instance/Top/Hausdorff.v 中；该文件记录在 Instance/Top.v 中类型值 [Top] 上成立的内容。
 Riehl，《上下文中的范畴论》，§4.7，印刷版第180页（PDF第200页），从页面图像阅读，练习4.7.ii（riehl:4.7:exii），同一个反射器“由定理4.7.3”。
 nLab：https://ncatlab.org/nlab/show/Hausdorff+space背景。Instance/Top.v 的 [Top@{h o}] 有类型值的开集，并且它的同态严格位于它的点之上（[o < h]；该文件的头部，第2点）。它的豪斯多夫子范畴 [HausdorffSpaces] 由经典的负公理 [IsHausdorff] 定义，Mac Lane 在书中（第158页，第VI.9节）使用该公理而未定义，并且其分离开集是数据。[CompHaus] 的完备性，即伴随函子定理在那里需要的前提，在信息排中律下被否定（Instance/Top/Complete/Refutations.v 的 [CompHaus_not_complete_below_IEM]，通过 Instance/Top/StoneCech/Refutations.v 的 [CompHaus_ArrowIndex_of_Top]）。在去掉紧致性条件的情况下，同样的论证可以得出 Haus。下面的直接反射，[TopT2_Reflective]，是到另一个子类别[TSepSub tprem_T2]的，正的和截断的T2空间；它不需要完整性，也不需要解集，并且不是封闭的，一旦仅有分离前提出为命题。直接反射。前提 [TSepPremise] 从一族类型值开的集读取命题；[tprem_T2] 是 nLab 的构造性豪斯多夫前提，带有截断的交点 ([inhabited { z & U z * V z }])，而 [TSep prem X] 说明它强制点的相等。[TSepQuot] 是 Instance/Top/Separation.v 的分离关系交集商，由 Instance/Top/Subspace/TypeValued.v 的 [TQuot] 构建；[TSepLaws] 询问两个定律 ([tl_pull], [tl_equiv])。[TSep_Reflective] 通过泛箭头组装反射，而 [TopT2_Reflective] 是 [Top] 上最大的豪斯多夫商。[IsHausdorff_TSep2_nn]：Instance/Top.v 的 [IsHausdorff] 仅在双重否定下给出该 T2。Haus ⟶ Top 的伴随函子定理 [GAFT_TopHaus] 陈述了 Adjunction/GAFT.v 的 [GAFT] 在 [Incl Top Hausdorff_Subcategory] 上；它被接受。[TopHaus_not_complete] 是 Freyd 的论证 (Structure/Complete/Freyd.v 的 [freyd_no_separated_pair]) 在 [HausdorffSpaces] 上，其中 [Bool_Discrete] 的两个点作为分离对，每个谓词及其分离开集的宇宙中，两个空间都是豪斯多夫 ([tophaus_bool_hausdorff], [tophaus_point_hausdorff]，其开集是命题；Instance/Top/StoneCech.v 的 [Discrete_Hausdorff] 通过开集 [z ≈ x] 分离，这些开集位于点的宇宙中)；[TopHaus_ArrowIndex_of_Top] 将 [Top] 的箭头指标限制到 [HausdorffSpaces]；而 [TopHaus_not_complete_below_IEM] 将 Instance/Top/Complete/Refutations.v 的 [Top_ArrowIndex_transport] 所携带的指数输入到 Instance/Top/StoneCech/Refutations.v 的 [ObjDecEq_of_IEM] 中。所以 [GAFT_TopHaus_vacuous] ：在 [IEM] 下，[GAFT_TopHaus] 的假设不可能在 [GAFT_TopHaus] 的每个宇宙实例（UNIVERSES，下文）中都成立。

 优点。没有声称任何 [eq_refl] 回读。一个 [Defined]，根据数据约定按标记（[tsep_universal]）计数：在一个临时副本中单独翻转为 [Qed]，该文件及 Instance/Top/Separation.v、Instance/Top/Hausdorff.v 和 Test/ProbeHausdorff461.v 的每次回读都保持被接受。17 个 [Qed]，按标记计数。每个常量在全局上下文下都是封闭的（每个 [Print Assumptions]）；[IEM] 是两个反证中的假设，从来都不是公理。UNIVERSES，由 [About] 在 [Set Printing Universes] 下读取本文件 [Print Module] 列表的所有 48 个常量（包括记录构造函数 [Build_TSepLaws]；无 [Program] 义务）。- 前提、定律以及商的关系和等价类：[@{o}]，空块；[TSepPremise@{o}] 的类型是 [Type@{max(Set+1,o+1)}]，它返回的关系为 Prop 值。[TSepQuot] 和 [TSepQuot_sep] 添加了 [o <= projections.u0]、[o <= projections.u1]、[TQuot] 自身的顶点。- 中介（[tsep_ker] 到 [tsep_med]）：[@{o u}] 与 [o < u]，[ContinuousMorphism@{u u0}] 的同态宇宙，其块是 [u0 < u]。- [TSepSub]，[TSep_Full]：[@{o h}] 与 [o < h]，[Top] 自身；[TSepSpaces] 和反射常数添加 [h < u]，Construction/Subcategory.v 的辅助 [Sub] 位于同态宇宙之上，以及 [<=] 相关的辅助；严格的 stdlib 上限 [o < Projections.u0] 首先由 [tsep_universal] 承载。[TopT2_Reflective@{o h u u0 u1 u2}]：[o < h]，[h < u]，没有提及 [Set]。- [IsHausdorff_TSep2_nn@{o u u0 u1}]：[IsHausdorff] 自身的四个宇宙和边界。- [tophaus_bool_hausdorff@{t p q o}]，[tophaus_point_hausdorff]：[IsHausdorff] 的块（[p < t]，[q < t]，[p <= o]，[q <= o]，[o <= t]）。[TopHaus_Bool]、[TopHaus_Point]、[tophaus_pt_bool]：
 [HausdorffSpaces] 的九个宇宙命名为 [@{c hh h t s a o p q}]（它的对象和同态，[Top] 的同态，谓词，两个辅助，点，两个开集），以及 [HausdorffSpaces] 自身模块的十一条约束。[TopHaus_not_complete@{r s c hh h t sh a o p q}] 添加了 [s <= r] 和 [hh <= r]，[Complete] 自身的。[TopHaus_not_complete_below_IEM] 在 [Top] 的同态处读取 [HausdorffSpaces] 及其同态，[h]，以及在任何带有 [h <= c] 的 [c] 处读取其对象：[TopHaus_not_complete] 的约束在 [hh := h] 和 [o < s] 上。-  [GAFT_TopHaus_vacuous@{e h o u u0 u1 u2 u3 u4 u6}]：假设写在 [GAFT_TopHaus] 自己的实例上，它的十个宇宙中有九个被命名（第十个不出现在任何假设中），而 [About] 块承载 [GAFT_TopHaus] 的所有约束，仅添加了八个 stdlib 限制，每个形式为 [h <= _] 或 [o <= _] 在 stdlib 宇宙上（由脚本比较）。特别地，豪斯多夫子类别的对象位于任何带 [h <= u4] 的 [u4]，其谓词位于任何带 [o <= u <= u4] 的 [u]，其分离开的开集位于任何 [u2]，低于 [u] 的 [u3] 以及在 [o] 或以下。Test/ProbeHausdorff461.v 使用严格不等式关闭的约束列表来固定它，因此无法从中推导出任何方程式：[p461_vacuous_apart] 在对象严格高于 [h]、谓词严格介于 [o] 和 [h] 之间、开集严格低于 [o] 时读取定理，而 [p461_not_complete_above] 则是对象严格高于 [h] 的完全性反证。这两个空间自身的引理是用来达到点以下的开集：[Discrete_Hausdorff] 读取时遭拒，该文件的 N11（“无法强制 o = p 因为 p < o”），而 [tophaus_bool_hausdorff] 被接受（[p461_bool_opens_below]）。- 没有区块携带方程。对 48 个常数的 [About] 输出进行 [Set] 的字数统计为 1，[TSepPremise] 的排序。未交付。在 [GAFT] 上方的 [Top] 的反射器（在 [IEM] 下为空；没有 [IEM] 既未获得也未反驳）；通过任何路径的 [HausdorffSpaces] 的反射，负形的子类别；在 [TSepSub tprem_T2] 的 [GAFT]；T0 和 T1 在 [Top] 之上，超出 Instance/Top/Kolmogorov.v 的 T0 反射；将 [TopT2_Reflective] 与 Instance/Top/Hausdorff.v 的反射器在两种编码之间进行比较；[TSepSpaces] 的完备性；在 [Top] 上的练习 4 和 5。
*)

(* * ** Separation premises with Type-valued opens / * ** 带有类型值开集的分离前提 *)

(*
 Only the premise is truncated to a proposition; the opens stay
 Type-valued, as in Instance/Top.v. 

 --------
 只有前提被截断为命题；开放项保持为类型值，如在 Instance/Top.v 中。
*)
Definition TSepPremise@{o} :=
  ∀ S : Type@{o}, ((S → Type@{o}) → Type@{o}) → S → S → Prop.

(* T2: every open about the first point meets every open about the second, the meeting point truncated. / T2：每一个关于第一点的开放都遇到每一个关于第二点的开放，交汇点被截断。 *)
Definition tprem_T2@{o} : TSepPremise@{o} :=
  fun S O x y => ∀ U V, O U → O V → U x → V y →
    inhabited { z : S & (U z * V z)%type }.

Definition TSep@{o} (prem : TSepPremise@{o}) (X : TopSpace@{o}) : Type@{o} :=
  ∀ x y : X, prem _ (IsOpen X) x y → x ≈ y.

Record TSepLaws@{o} (prem : TSepPremise@{o}) : Prop := {
  tl_pull : ∀ (S S' : Type@{o}) (f : S → S') (O : (S → Type@{o}) → Type@{o})
      (O' : (S' → Type@{o}) → Type@{o}),
      (∀ W, O' W → O (fun s => W (f s))) →
      ∀ x y, prem S O x y → prem S' O' (f x) (f y);
  tl_equiv : ∀ (X : TopSpace@{o}) (x y : X), x ≈ y → prem _ (IsOpen X) x y
}.

Lemma tprem_T2_laws@{o} : TSepLaws@{o} tprem_T2@{o}.
Proof.
  constructor.
  - intros S S' f O O' sub x y H W1 W2 H1 H2 w1 w2.
    destruct (H _ _ (sub W1 H1) (sub W2 H2) w1 w2) as [[z [a b]]].
    exact (inhabits (f z; (a, b))).
  - intros X x y e U V HU HV u v.
    exact (inhabits (y; (open_proper X U HU x y e u, v))).
Qed.

(* * ** The largest separated quotient / * ** 最大的分离商 *)

Section TQuotient.

Universe o.

Variable prem : TSepPremise@{o}.
Variable L : TSepLaws@{o} prem.

Context (X : TopSpace@{o}).

Local Notation P := (carrier (top_carrier X)).

Definition tsep_qopen (R : P → P → Prop) (U : P → Type@{o}) : Type@{o} :=
  (IsOpen X U * (∀ a b, R a b → U a → U b))%type.

Definition TSepRel (R : P → P → Prop) : Prop :=
  (∀ a, R a a) /\ (∀ a b, R a b → R b a) /\
  (∀ a b c, R a b → R b c → R a c) /\
  (∀ a b : P, a ≈ b → R a b) /\
  (∀ a b, prem P (tsep_qopen R) a b → R a b).

Definition tsepeq (a b : P) : Prop := ∀ R, TSepRel R → R a b.

Lemma tsepeq_refl (a : P) : tsepeq a a.
Proof. intros R HR. exact (proj1 HR a). Qed.

Lemma tsepeq_sym (a b : P) : tsepeq a b → tsepeq b a.
Proof. intros e R HR. exact (proj1 (proj2 HR) a b (e R HR)). Qed.

Lemma tsepeq_trans (a b c : P) : tsepeq a b → tsepeq b c → tsepeq a c.
Proof.
  intros e1 e2 R HR.
  exact (proj1 (proj2 (proj2 HR)) a b c (e1 R HR) (e2 R HR)).
Qed.

Lemma tsepeq_of_equiv (a b : P) : a ≈ b → tsepeq a b.
Proof. intros e R HR. exact (proj1 (proj2 (proj2 (proj2 HR))) a b e). Qed.

Definition tsep_setoid : SetoidObject@{o o} :=
  {| carrier := P;
     is_setoid := {| equiv := tsepeq;
                     setoid_equiv := Build_Equivalence tsepeq tsepeq_refl
                                       tsepeq_sym tsepeq_trans |} |}.

Definition tsep_q :
  @SetoidMorphism@{o o o} _ (is_setoid (top_carrier X)) _
    (is_setoid tsep_setoid) :=
  @Build_SetoidMorphism _ (is_setoid (top_carrier X)) _ (is_setoid tsep_setoid)
    (fun x => x) tsepeq_of_equiv.

Definition TSepQuot : TopSpace@{o} := TQuot X tsep_setoid tsep_q.

Lemma TSepQuot_sep : TSep prem TSepQuot.
Proof using L.
  intros x y H R HR.
  apply (proj2 (proj2 (proj2 (proj2 HR)))).
  apply (tl_pull _ L P P (fun s => s) (IsOpen TSepQuot) (tsep_qopen R));
    [|exact H].
  intros U [HU HsU]. split.
  - intros t t' e u. exact (HsU t t' (e R HR) u).
  - exact HU.
Qed.

Section TMed.

Context (H : TopSpace@{o}) (HH : TSep prem H) (f : ContinuousMorphism X H).

Definition tsep_ker (a b : P) : Prop :=
  prem _ (IsOpen H) (continuous_map f a) (continuous_map f b).

Lemma tsep_ker_to (a b : P) :
  tsep_ker a b → continuous_map f a ≈ continuous_map f b.
Proof using HH. exact (HH _ _). Qed.

Lemma tsep_ker_of (a b : P) :
  continuous_map f a ≈ continuous_map f b → tsep_ker a b.
Proof using L. exact (tl_equiv _ L H _ _). Qed.

Lemma tsep_ker_TSepRel : TSepRel tsep_ker.
Proof using L HH.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - intro a. apply tsep_ker_of. reflexivity.
  - intros a b e. apply tsep_ker_of. symmetry. exact (tsep_ker_to a b e).
  - intros a b c e1 e2. apply tsep_ker_of.
    transitivity (continuous_map f b);
      [exact (tsep_ker_to _ _ e1)|exact (tsep_ker_to _ _ e2)].
  - intros a b e. apply tsep_ker_of.
    exact (proper_morphism (continuous_map f) a b e).
  - intros a b Hp. unfold tsep_ker.
    apply (tl_pull _ L P _ (fun s => continuous_map f s)
             (tsep_qopen tsep_ker) (IsOpen H)); [|exact Hp].
    intros W HW. split.
    + exact (continuity f W HW).
    + intros a' b' e u.
      exact (open_proper H W HW _ _ (tsep_ker_to a' b' e) u).
Qed.

Lemma tsep_med_resp (a b : P) :
  tsepeq a b → continuous_map f a ≈ continuous_map f b.
Proof using L HH.
  intro e. exact (tsep_ker_to a b (e tsep_ker tsep_ker_TSepRel)).
Qed.

Definition tsep_med_setoid :
  @SetoidMorphism@{o o o} _ (is_setoid tsep_setoid) _
    (is_setoid (top_carrier H)) :=
  @Build_SetoidMorphism _ (is_setoid tsep_setoid) _ (is_setoid (top_carrier H))
    (fun a => continuous_map f a) tsep_med_resp.

Definition tsep_med : ContinuousMorphism TSepQuot H :=
  tquot_desc X tsep_setoid tsep_q H f tsep_med_setoid
    (fun x => reflexivity (continuous_map f x)).

End TMed.

End TQuotient.

Section TReflection.

Universes o h.
Constraint o < h.

Variable prem : TSepPremise@{o}.
Variable L : TSepLaws@{o} prem.

Definition TSepSub : Subcategory@{h h o h} Top@{h o} :=
  @Build_Subcategory@{h h o h} Top@{h o}
    (fun X => TSep prem X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition TSepSpaces : Category := Sub Top@{h o} TSepSub.

Lemma TSep_Full : Construction.Subcategory.Full Top@{h o} TSepSub.
Proof. intros x y ox oy g; exact I. Qed.

Definition TSepObj (X : Top@{h o}) : TSepSpaces :=
  (TSepQuot prem X; TSepQuot_sep prem L X).

Definition tsep_proj (X : Top@{h o}) :
  X ~{Top@{h o}}~> Incl Top@{h o} TSepSub (TSepObj X) :=
  tquot_proj X (tsep_setoid prem X) (tsep_q prem X).

Definition tsep_universal (X : Top@{h o}) :
  ∀ (d : TSepSpaces) (f : X ~{Top@{h o}}~> Incl Top@{h o} TSepSub d),
    ∃! g : TSepObj X ~{TSepSpaces}~> d,
      f ≈ fmap[Incl Top@{h o} TSepSub] g ∘ tsep_proj X.
Proof using L.
  intros d f.
  unshelve eexists.
  - exact (tsep_med prem L X (`1 d) (`2 d) f; I).
  - intro x; simpl; reflexivity.
  - intros g Hg x; simpl. exact (Hg x).
Defined.

Definition tsep_ua (X : Top@{h o}) :
  @UniversalArrow Top@{h o} TSepSpaces X (Incl Top@{h o} TSepSub) :=
  @universal_arrow_from_UMP Top@{h o} TSepSpaces X (Incl Top@{h o} TSepSub)
    (TSepObj X) (tsep_proj X) (tsep_universal X).

Definition TSep_reflector : Top@{h o} ⟶ TSepSpaces :=
  LeftAdjointFunctorFromUniversalArrows (Incl Top@{h o} TSepSub) tsep_ua.

Definition TSep_adj : TSep_reflector ⊣ Incl Top@{h o} TSepSub :=
  AdjunctionFromUniversalArrows (Incl Top@{h o} TSepSub) tsep_ua.

Definition TSep_Reflective : Reflective TSepSub :=
  @Build_Reflective Top@{h o} TSepSub TSep_Full TSep_reflector TSep_adj.

End TReflection.

(* The direct Hausdorff reflection over the Type-valued [Top]. / 在类型值 [Top] 上的直接豪斯多夫反射。 *)
Definition TopT2_Reflective@{o h +| o < h +} :
  Reflective (TSepSub@{o h} tprem_T2@{o}) :=
  TSep_Reflective tprem_T2 tprem_T2_laws.

(* Instance/Top.v's [IsHausdorff], the classical negative form, gives this T2 only under a double negation. / Instance/Top.v 的 [IsHausdorff]，经典的否定形式，只有在双重否定下才给出这个 T2。 *)
Lemma IsHausdorff_TSep2_nn@{o +} (X : TopSpace@{o}) (HX : IsHausdorff X)
  (x y : X) : tprem_T2 _ (IsOpen X) x y → ¬ ¬ inhabited (x ≈ y).
Proof.
  intros Hp Hne.
  destruct (HX x y (fun e => Hne (inhabits e))) as [U [V [[HU HV] [[u v] Hd]]]].
  destruct (Hp U V HU HV u v) as [[z [a b]]].
  exact (Hd z a b).
Qed.

(* * ** The adjoint functor theorem at the Type-valued inclusion / * ** 类型值包含下的伴随函子定理 *)

(*
 The two-point discrete space and the point are Hausdorff at every
 universe of the predicate and of the separating opens, the opens used
 being propositions.  Instance/Top/StoneCech.v's [Discrete_Hausdorff]
 separates by the opens [z ≈ x], which sit at the points' universe. 

 --------
 两点的离散空间和点在谓词的每个宇宙以及分离开集上都是豪斯多夫的，所使用的开集为命题。Instance/Top/StoneCech.v 的 [Discrete_Hausdorff] 通过开集 [z ≈ x] 分离，这些开集位于点的宇宙中。
*)
Lemma tophaus_bool_hausdorff@{t p q o +| p < t, q < t, p <= o, q <= o,
    o <= t +} : IsHausdorff@{t p q o} Bool_Discrete@{o}.
Proof.
  intros x y nxy.
  exists (fun z : bool => z = x). exists (fun z : bool => z = y).
  refine ((_, _), ((_, _), _)); simpl.
  - intros u v Huv Hu. simpl in Huv. congruence.
  - intros u v Huv Hu. simpl in Huv. congruence.
  - reflexivity.
  - reflexivity.
  - intros z Hx Hy. apply nxy. simpl. congruence.
Qed.

Lemma tophaus_point_hausdorff@{t p q o +| p < t, q < t, p <= o, q <= o,
    o <= t +} : IsHausdorff@{t p q o} Point_Top@{o}.
Proof. intros x y nxy. destruct x, y. destruct (nxy (reflexivity _)). Qed.

(*
 The universes of [HausdorffSpaces]: [c], [hh] its objects and homs; [h]
 and [o] those of [Top]; [t] the predicate [IsHausdorff]; [p], [q] its
 separating opens; [s], [a] auxiliaries of the subcategory. 

 --------
 [HausdorffSpaces] 的宇宙：[c]，[hh] 它的对象和态射；[h] 和 [o] [Top] 的那些；[t] 谓词 [IsHausdorff]；[p]，[q] 它的分离开集；[s]，[a] 子范畴的辅助工具。
*)
Definition TopHaus_Bool@{c hh h t s a o p q +} :
  HausdorffSpaces@{c hh h t s a o p q} :=
  (Bool_Discrete@{o}; tophaus_bool_hausdorff@{t p q o}).

Definition TopHaus_Point@{c hh h t s a o p q +} :
  HausdorffSpaces@{c hh h t s a o p q} :=
  (Point_Top@{o}; tophaus_point_hausdorff@{t p q o}).

Definition tophaus_pt_bool@{c hh h t s a o p q +} (b : bool) :
  TopHaus_Point@{c hh h t s a o p q}
    ~{HausdorffSpaces@{c hh h t s a o p q}}~>
  TopHaus_Bool@{c hh h t s a o p q} :=
  (top_point Bool_Discrete@{o} b; I).

(* #455's arrow index of [Top], restricted to the Hausdorff spaces. / #455 的箭头指数 [Top]，限制在豪斯多夫空间上。 *)
Definition TopHaus_ArrowIndex_of_Top@{s h o c +}
  (AIT : ArrowIndex@{s h h} Top@{h o}) :
  ArrowIndex@{s c h} (HausdorffSpaces : Category@{c h h}) :=
  @Build_ArrowIndex (HausdorffSpaces : Category@{c h h}) (ai_index AIT)
    (fun x y f => ai_enc AIT (`1 f))
    (fun x y m d => (ai_dec AIT m (`1 d); I))
    (fun x y f d => ai_dec_enc AIT (`1 f) (`1 d)).

(*
 Freyd's argument: a complete category with an arrow index is thin, and
 the two points of [Bool_Discrete] are two arrows out of the point. 

 --------
 弗雷德的论点：一个带箭头指标的完整范畴是薄的，[Bool_Discrete] 的两个点是该点的两个箭头。
*)
Theorem TopHaus_not_complete@{r s c hh h t sh a o p q +}
  (AI : ArrowIndex@{s c hh} HausdorffSpaces@{c hh h t sh a o p q})
  (comp : @Complete@{r s hh c} HausdorffSpaces@{c hh h t sh a o p q}) :
  False.
Proof.
  exact (freyd_no_separated_pair AI (tophaus_pt_bool true)
           (tophaus_pt_bool false) _ _
           (complete_iprod comp (fun _ : ai_index AI => TopHaus_Bool))
           (fun f => continuous_map (`1 f) ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

Theorem TopHaus_not_complete_below_IEM@{e r s c h t sh a o p q +| o < h,
    o < s, h <= c +} (E : IEM@{e})
  (comp : @Complete@{r s h c} HausdorffSpaces@{c h h t sh a o p q}) :
  False.
Proof.
  exact (TopHaus_not_complete
           (TopHaus_ArrowIndex_of_Top
              (Top_ArrowIndex_transport@{s o s h}
                 (canonical_ArrowIndex
                    (ObjDecEq_of_IEM E Top@{h o} : ObjDecEq Top@{s o}))))
           comp).
Qed.

(* [GAFT] at the Type-valued inclusion is formable ... / [GAFT] 在类型值包含处是可形成的... *)
Definition GAFT_TopHaus@{h o +| o < h +}
  (comp : @Complete (Sub Top@{h o} Hausdorff_Subcategory))
  (cont : @PreservesImageLimit _ _ (Incl Top@{h o} Hausdorff_Subcategory))
  (sols : ∀ X : Top@{h o},
      SolutionSet (Incl Top@{h o} Hausdorff_Subcategory) X) :
  { H : Top@{h o} ⟶ Sub Top@{h o} Hausdorff_Subcategory &
    H ⊣ Incl Top@{h o} Hausdorff_Subcategory } :=
  GAFT (Incl Top@{h o} Hausdorff_Subcategory) comp cont sols.

(* ... and vacuous under informative excluded middle: its completeness premise is refuted. The hypotheses are those of [GAFT_TopHaus] at every one of its universe instances. / ...并且在排中律被排除的情况下空洞无物：它的完备性前提被驳斥。假设是 [GAFT_TopHaus] 在其每一个宇宙实例中的假设。 *)
Theorem GAFT_TopHaus_vacuous@{e h o u u0 u1 u2 u3 u4 u6 +| o < h, h < u1,
    h < u6, u2 < u, u3 < u, u2 <= o, u3 <= o, o <= u, u <= u4, h <= u4,
    u0 <= h, u4 <= u6 +} (E : IEM@{e})
  (comp : @Complete@{h h h u4}
            (Sub@{h h u u0 u4 h u1} Top@{h o}
               Hausdorff_Subcategory@{h u0 o u u2 u3}))
  (cont : @PreservesImageLimit@{u4 h h h u6 h u1 h} _ _
            (Incl@{h h u u0 u4 u1} Top@{h o}
               Hausdorff_Subcategory@{h u0 o u u2 u3}))
  (sols : ∀ X : Top@{h o},
      SolutionSet@{h h u4 h}
        (Incl@{h h u u0 u4 u1} Top@{h o}
           Hausdorff_Subcategory@{h u0 o u u2 u3}) X) :
  False.
Proof.
  pose proof (GAFT_TopHaus@{h o u u0 u1 u2 u3 u4 _ u6} comp cont sols) as _.
  exact (TopHaus_not_complete_below_IEM E comp).
Qed.
