Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.Coalgebra.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Monad.
Require Import Category.Instance.Proset.Monad.Interior.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Cocomplete.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* * * Interior and closure on the subsets of a space / * * 空间子集的内部与闭包 *)

(*
 nLab: https://ncatlab.org/nlab/show/interior
 nLab: https://ncatlab.org/nlab/show/closure
 Book: Riehl, "Category Theory in Context", 2nd ed., SS 5.1,
 Example 5.1.7 with footnote 5, printed p. 186, and SS 5.2,
 Example 5.2.6 (begins p. 189), clause (iv) and footnotes 10–11,
 printed p. 190

 WHAT THE BOOK SAYS.  Example 5.1.7 (p. 186) equips the poset PX of
 subsets of a topological space X with "a closure operator TA = Ā ...
 and a kernel operator KA = A°, where A° is the interior of A ⊂ X",
 and footnote 5 reads: "The closure of A is the smallest closed set
 containing A, equally the intersection of all closed sets containing
 A; the interior is defined dually."  Example 5.2.6 (begins p. 189),
 clause (iv) and footnotes 10–11, printed p. 190: "An algebra for the
 closure closure operator on the poset of subsets of a
 topological space X is exactly a closed subset of X.  Dually, a
 coalgebra for the interior kernel operator is exactly an open
 subset."  Riehl works classically; the constructive content of each
 half is measured below.

 WHERE.  The spaces are Instance/Top/Prop.v's [PTop]: Prop-valued
 opens closed under the union of any Prop-valued family
 ([popen_union]).  That is what makes the interior formable, as the
 union of all the opens inside a subset; Instance/Top/Image.v records
 that over the Type-valued [Top] the same union is not formable and
 delivers no interior operator.  The subsets are
 Instance/Sets/Powerset.v's [Powerset_Prop_obj] (≈-respecting Prop
 predicates), and their inclusion order is Instance/Powerset.v's
 [Subsets].

 THE INTERIOR, CONSTRUCTIVE THROUGHOUT.  [pinterior X S] is the union
 of the opens contained in S ("defined dually" to footnote 5), written
 in exactly the shape of [popen_union], so it is open ([pint_open]).
 It is monotone, deflationary and comultiplicative ([pint_mono],
 [pint_defl], [pint_comult]), hence an
 Instance/Proset/Monad/Interior.v [InteriorOperator] ([pinterior_op])
 with its comonad ([pinterior_comonad]).  [pint_coalgebra_iff_open] is
 the coalgebra half of Example 5.2.6 (iv), with no hypothesis: through
 Interior.v's [wcoalgebra_iff_open] a coalgebra is S ⊆ int S, which
 holds exactly when S is open.  Non-vacuity: {true} in
 Instance/Top/Cocomplete.v's indiscrete two-point space [PTwoIndisc]
 is not open, so not a coalgebra ([true_sub_not_coalgebra]).

 THE CLOSURE, BY FOOTNOTE 5.  A subset is closed when its complement is
 open ([PClosedSub]), and [pclosure X S] is the intersection of the
 closed subsets containing S, a closure operator ([pclosure_op],
 [pclosure_monad]) with no hypothesis.  One direction of the algebra
 half is constructive: a closed subset is an algebra
 ([pcl_talgebra_of_closed]).  The converse, an algebra is closed
 ([pcl_closed_of_talgebra]), takes excluded middle as an EXPLICIT
 hypothesis [lem]; no axiom is assumed.  It is used twice: to pass
 from "not every closed C above S contains z" to a closed C above S
 that misses z, and to get C z from ¬¬ C z.  Some classical principle
 is needed: the converse without [lem] implies ¬¬(∀ q, ¬¬q → q)
 ([pcl_converse_nndne]), which intuitionistic higher-order logic does
 not prove (it stops in the Kripke model on (ω, ≤)); whether ¬¬-LEM
 suffices is not settled.  The witness is [true_or_sub q], {true} ∪ q
 in [PTwoIndisc], which is closed exactly when ¬¬q, so that the point
 false lies in the closure of {true} only if double-negation
 elimination holds ([pcl_true_false_dne]).  Instance/Top/Hausdorff.v's
 adherence closure [PClosureIn] would not avoid the first use: by its
 definition, a point outside an algebra again yields only that not
 every open neighbourhood meets S (¬∀), not one that misses it.

 THE UNCONDITIONAL ROUTE, measured.  Both halves are constructive for
 the closure written as the complement of the interior of the
 complement, ¬ int (¬ S) ([ncl], [nclosure_op], [nclosure_monad]), with
 "closed" read as "the complement of an open" ([PCoOpen]):
 [ncl_talgebra_iff_coopen] is the algebra half with no hypothesis, and
 {true} in [PTwoIndisc] is not such an algebra, constructively
 ([true_sub_not_nclosed]).  Classically this is Riehl's statement:
 under [lem], [pclosure] and [ncl] agree pointwise
 ([pclosure_ncl_lem]) and the two readings of "closed" coincide
 ([closed_of_coopen_lem]; conversely [coopen_of_closed_stable] needs
 only that S be ¬¬-stable).  A complement of an open is ¬¬-stable
 ([coopen_stable]), and no route from [PClosedSub] to [PCoOpen]
 without that stability is given here, so the constructive theorem is
 about the second reading.
 Both routes are delivered, the footnote-5 route with its one
 classical clause disclosed.

 STRENGTHS.  Every statement here is a proposition about subsets, so
 the strengths are logical rather than definitional: the interior
 half and the ¬ int ¬ algebra half are constructive; the footnote-5
 algebra half is constructive in one direction and uses [lem] in the
 other, where without [lem] it implies ¬¬(∀ q, ¬¬q → q)
 ([pcl_converse_nndne]); the bridges between the two closures use
 [lem].  The data
 ([pinterior], [pclosure], [ncl] and the operators) are transparent
 definitions whose respect for ≈ is a [Qed] lemma.

 UNIVERSES, read off [About] with all instances printed.  No constant
 has a level that occurs in its body only.  [Set < o] is first carried
 by Instance/Sets/Powerset.v's [Powerset_Prop_truth_equiv], a relation
 on [Prop] at level o, and reaches this file through
 [Powerset_Prop_obj]; the operators add the caps of stdlib's
 [PreOrder] and [relation], and the interior side the global levels of
 stdlib's [Basics.flip] (see Interior.v).  The two witnesses, and
 [true_or_sub], [pcl_true_false_dne] and [pcl_converse_nndne], carry
 [o <= Logic_lemmas.equality.u0] from [PTwoIndisc]; the equation
 [false = true] is retyped at [bool] before [discriminate], which at
 the carrier type would add a cap [o <= eq_ind.u0] (measured).  The
 biconditionals name their [iffT] level (p), and the one-directional
 algebra lemmas pin the free level of the inner
 [talgebra_iff_closed] to h, so that no level is left in a body
 alone.  Both declarations of [Thin] and of [proset_thin] are loaded
 (measured by [Locate]); this file names neither.

 NOT DELIVERED.  No statement over the Type-valued [Top]; no closure
 as a left adjoint or interior as a right adjoint of an inclusion of
 posets of closed or open subsets; no Kuratowski axioms beyond the
 closure-operator ones (no preservation of finite unions by the
 closure, or of finite intersections by the interior); no proof that
 ¬¬-LEM suffices for [pcl_closed_of_talgebra], and no proof, beyond
 [pcl_converse_nndne], of how much of [lem] it needs. 

 --------
 nLab:  https://ncatlab.org/nlab/show/interior
 nLab:  https://ncatlab.org/nlab/show/closure
 书籍：Riehl，《语境中的范畴论》，第2版，第5.1节，例5.1.7及脚注5，印刷页186；第5.2节，例5.2.6（从第189页开始），条款(iv)及脚注10–11，印刷页190书中所说内容。示例 5.1.7（第 186 页）为拓扑空间 X 的子集的偏序集 PX 配备了“闭包算子 TA = Ā…… 和核算子 KA = A°，其中 A° 是 A ⊂ X 的内部”，脚注 5 说明：“A 的闭包是包含 A 的最小闭集，也就是包含 A 的所有闭集的交集；内部则定义为对偶形式。” 示例 5.2.6（开始于第 189 页）、条款 (iv) 及脚注 10–11（印刷第 190 页）：“在拓扑空间 X 的子集偏序集上，闭包算子的代数恰好是 X 的闭子集。对偶地，内部核算子的余代数恰好是开子集。” Riehl 的处理是经典的；下文将评估每一部分的构造内容。哪里。空间是 Instance/Top/Prop.v 中的 [PTop]：Prop 值的，对任何 Prop 值的族的并闭合（[popen_union]）。这就是为什么内部可以形成，因为它是子集内所有开集的并；Instance/Top/Image.v 记录了在 Type 值的 [Top] 上同样的并不可形成，并且不提供内部算子。子集是 Instance/Sets/Powerset.v 中的 [Powerset_Prop_obj]（≈-保持的 Prop 谓词），它们的包含顺序是 Instance/Powerset.v 中的 [Subsets]。内部，全程构造的。  [pinterior X S] 是包含在 S 中的开集的并集（“通过脚注5进行对偶定义”），完全以 [popen_union] 的形式书写，因此它是开集（[pint_open]）。 它是单调的、减缩的且余乘法性的（[pint_mono]、[pint_defl]、[pint_comult]），因此是 Instance/Proset/Monad/Interior.v 的 [InteriorOperator]（[pinterior_op]），并具有其余幺半群（[pinterior_comonad]）。  [pint_coalgebra_iff_open] 是示例 5.2.6 (iv) 的余代数部分，无需假设：通过 Interior.v 的 [wcoalgebra_iff_open]，余代数是 S ⊆ int S，当且仅当 S 是开集时成立。 非空性：Instance/Top/Cocomplete.v 中的离散两点空间 {true} [PTwoIndisc] 不是开集，因此不是余代数（[true_sub_not_coalgebra]）。闭包，见脚注 5。当一个集合的补集是开集时，该集合是闭集（[PClosedSub]），并且 [pclosure X S] 是包含 S 的闭子集的交集，是一个闭包算子（[pclosure_op]，[pclosure_monad]），不需要假设。代数的一半方向是构造性的：闭子集是一个代数（[pcl_talgebra_of_closed]）。相反，代数是闭集（[pcl_closed_of_talgebra]），需要把排中律作为明确假设（[lem]）；不假设任何公理。它使用了两次：从“并非所有包含 S 的闭集 C 都包含 z”推导出一个包含 S 但不包含 z 的闭集 C，以及从 ¬¬ C z 得到 C z。需要一些经典原理：没有 [lem] 的逆命题意味着 ¬¬(∀ q, ¬¬q → q)（[pcl_converse_nndne]），这是直觉主义高阶逻辑无法证明的（它在 (ω, ≤) 的 Kripke 模型上停下）；是否 ¬¬-LEM 足够尚未确定。见证者是 [true_or_sub q]，在 [PTwoIndisc] 中的 {true} ∪ q，当且仅当 ¬¬q 时它是闭合的，因此，点 false 仅在双重否定消去成立（[pcl_true_false_dne]）时属于 {true} 的闭包。Instance/Top/Hausdorff.v 的 adherent 闭包 [PClosureIn] 并不能避免第一次使用：根据它的定义，代数之外的点仍然只会得出并非每个开邻域都与 S 相交（¬∀），而不是存在一个不相交的邻域。无条件路线，经过测量。两部分对于闭包都是建设性的，闭包写作补集的内部的补集 ¬ int (¬ S) ( [ncl] , [nclosure_op] , [nclosure_monad] )，其中“闭”被理解为“一个开的补集” ( [PCoOpen] )：[ncl_talgebra_iff_coopen] 是没有假设的代数部分，而 {true} 在 [PTwoIndisc] 中从建设性上不是这样的代数 ([true_sub_not_nclosed])。在经典情况下，这就是 Riehl 的陈述：在 [lem] 下，[pclosure] 和 [ncl] 在点上是一致的 ([pclosure_ncl_lem])，并且“闭”的两种理解是一致的 ([closed_of_coopen_lem]；相反，[coopen_of_closed_stable] 仅需要 S 是 ¬¬-稳定的)。一个开的补集是 ¬¬-稳定的 ([coopen_stable])，并且这里没有给出从 [PClosedSub] 到 [PCoOpen] 的不依赖于该稳定性路线，因此建设性定理涉及的是第二种理解。两条路线都已完成，脚注-5 路线公开了它的一个经典条款。

 优势。这里的每个陈述都是关于子集的命题，因此优势是逻辑上的而非定义上的：内部部分和 ¬ int ¬ 代数部分是构造性的；脚注-5 代数部分在一个方向上是构造性的，在另一个方向上使用 [lem]，如果没有 [lem]，它会暗示 ¬¬(∀ q, ¬¬q → q) ([pcl_converse_nndne])；两种闭包之间的桥梁使用 [lem]。数据（[pinterior], [pclosure], [ncl] 和运算符）是透明的定义，其对 ≈ 的遵循是 [Qed] 引理。UNIVERSES，读取所有实例打印的 [About]。没有常量在其主体中仅出现于某一级别。[Set < o] 首次由 Instance/Sets/Powerset.v 的 [Powerset_Prop_truth_equiv] 携带，该关系在 [Prop] 的 o 级，并通过 [Powerset_Prop_obj] 到达此文件；操作符添加了 stdlib 的 [PreOrder] 和 [relation] 的上限，并在内部侧添加了 stdlib 的 [Basics.flip] 的全局级别（参见 Interior.v）。两个证人，以及 [true_or_sub]、[pcl_true_false_dne] 和 [pcl_converse_nndne]，从 [PTwoIndisc] 携带 [o <= Logic_lemmas.equality.u0]；方程 [false = true] 在 [bool] 处重新类型化，然后在 [discriminate] 处使用，在承载类型下将添加上限 [o <= eq_ind.u0]（已测量）。双条件命名它们的 [iffT] 层级 (p)，而单向代数学引理将内部 [talgebra_iff_closed] 的自由层级固定为 h，因此没有层级单独存在于一个体中。[Thin] 和 [proset_thin] 的声明都已加载（由 [Locate] 测量）；该文件未命名任何一个。

 未交付。对类型值 [Top] 没有任何陈述；没有作为左伴随的闭包或作为右伴随的内部，用于包含封闭或开放子集的偏序集合；没有超出闭包算子公理的 Kuratowski 公理（闭包不保持有限并集，或内部不保持有限交集）；没有证明 ¬¬-LEM 足以用于 [pcl_closed_of_talgebra]，也没有在 [pcl_converse_nndne] 之外证明 [lem] 需要多少。
*)

(* The subsets of the points of X: Prop-valued predicates respecting the points' ≈ (Instance/Sets/Powerset.v's [Powerset_Prop_obj]). / X 点的子集：符合点的 ≈ 的 Prop 值谓词（Instance/Sets/Powerset.v 的 [Powerset_Prop_obj]）。 *)
Local Notation PSub X := (carrier (Powerset_Prop_obj (pt_carrier X))).

(* * ** The interior: the union of the opens inside S / * ** 内部：S 内部开集的并集 *)

Definition pint_fun@{o} (X : PTop@{o}) (S : PSub X) (x : pt_carrier X) :
  Prop :=
  ex (fun U : pt_carrier X → Prop => (POpen X U /\ ∀ y, U y → S y) /\ U x).

Lemma pint_proper@{o} (X : PTop@{o}) (S : PSub X) (x y : pt_carrier X) :
  x ≈ y → Powerset_Prop_truth_equiv@{o} (pint_fun X S x) (pint_fun X S y).
Proof.
  intros Hxy; split; intros [U [[HU HS] Ux]]; exists U;
    (split; [split; assumption|]).
  - exact (popen_proper X U HU x y Hxy Ux).
  - apply (popen_proper X U HU y x); [|exact Ux]. symmetry; exact Hxy.
Qed.

Definition pinterior@{o} (X : PTop@{o}) (S : PSub X) : PSub X :=
  @Build_SetoidMorphism@{o o o}
    (carrier (pt_carrier X)) (is_setoid (pt_carrier X))
    Prop (is_setoid Powerset_Prop_truth@{o}) (pint_fun X S)
    (pint_proper X S).

(* The interior is open: it is written in exactly the shape that Instance/Top/Prop.v's [popen_union] closes. / 内部是开放的：它正好写成 Instance/Top/Prop.v 的 [popen_union] 关闭的形状。 *)
Lemma pint_open@{o} (X : PTop@{o}) (S : PSub X) : POpen X (pinterior X S).
Proof.
  apply (popen_union X (fun U => POpen X U /\ ∀ y, U y → S y)).
  intros U [HU _]; exact HU.
Qed.

Definition pint_mono@{o} (X : PTop@{o}) (S T : PSub X)
  (h : subset_le S T) : subset_le (pinterior X S) (pinterior X T) :=
  fun x '(ex_intro _ U (conj (conj HU HS) Ux)) =>
    ex_intro _ U (conj (conj HU (fun y Uy => h y (HS y Uy))) Ux).

Definition pint_defl@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le (pinterior X S) S :=
  fun x '(ex_intro _ U (conj (conj _ HS) Ux)) => HS x Ux.

Definition pint_comult@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le (pinterior X S) (pinterior X (pinterior X S)) :=
  fun x '(ex_intro _ U (conj (conj HU HS) Ux)) =>
    ex_intro _ U (conj (conj HU (fun y Uy =>
      ex_intro _ U (conj (conj HU HS) Uy))) Ux).

(*
 The interior operator: a closure operator on the reversed inclusion
 order (Instance/Proset/Monad/Interior.v). 

 --------
 内部算子：在反向包含顺序上的闭包算子（Instance/Proset/Monad/Interior.v）。
*)
Definition pinterior_op@{o} (X : PTop@{o}) :
  InteriorOperator@{o} (subset_le_preorder@{o} (pt_carrier X)) :=
  {| cl_fun  := flip_mono {| mono_map := pinterior X
                           ; mono_pres := pint_mono X |}
   ; cl_ext  := pint_defl X
   ; cl_mult := pint_comult X |}.

Definition pinterior_comonad@{o h} (X : PTop@{o}) :
  @Comonad (Subsets@{o h} (pt_carrier X))
    (interior_functor@{o h} (pinterior_op X)) :=
  interior_comonad@{o h} (pinterior_op X).

(*
 A subset contained in its interior is open, and an open subset is
 contained in its interior. 

 --------
 包含在其内部的子集是开集，而开子集包含在其内部。
*)
Lemma open_of_sub_pint@{o} (X : PTop@{o}) (S : PSub X)
  (h : subset_le S (pinterior X S)) : POpen X S.
Proof.
  apply (popen_respects X (pinterior X S)); [|exact (pint_open X S)].
  intro x; split; [exact (pint_defl X S x)|exact (h x)].
Qed.

Definition sub_pint_of_open@{o} (X : PTop@{o}) (S : PSub X)
  (HS : POpen X S) : subset_le S (pinterior X S) :=
  fun x Sx => ex_intro _ (fun y => S y) (conj (conj HS (fun y Sy => Sy)) Sx).

(*
 Riehl 5.2.6 (iv), coalgebra half: the coalgebras of the interior
 comonad are exactly the open subsets.  Constructive. 

 --------
 Riehl 5.2.6 (iv)，余代数部分：内余单子的余代数恰好是开子集。构造式的。
*)
Definition pint_coalgebra_iff_open@{o h p} (X : PTop@{o}) (S : PSub X) :
  iffT@{h p}
    (@WCoalgebra (Subsets@{o h} (pt_carrier X))
       (interior_functor (pinterior_op X)) (pinterior_comonad X) S)
    (POpen X S) :=
  let (to_sub, of_sub) :=
    wcoalgebra_iff_open@{o h p} (interior_functor (pinterior_op X))
      (H := pinterior_comonad X) S in
  (fun c => open_of_sub_pint X S (to_sub c),
   fun HS => of_sub (sub_pint_of_open X S HS)).

(*
 Non-vacuity: {true} in the indiscrete two-point space is not open, so
 not a coalgebra. 

 --------
 非空性：在不可分二点空间中 {true} 不是开放的，因此不是余代数。
*)
Definition true_sub@{o} : PSub PTwoIndisc@{o} :=
  @Build_SetoidMorphism@{o o o}
    (carrier (pt_carrier PTwoIndisc@{o})) (is_setoid (pt_carrier PTwoIndisc))
    Prop (is_setoid Powerset_Prop_truth@{o}) (fun b => b = true)
    (fun x y (Hxy : x = y) =>
       match Hxy in _ = z return Powerset_Prop_truth_equiv (x = true)
                                   (z = true) with
       | eq_refl => conj (fun H => H) (fun H => H)
       end).

Lemma true_sub_not_coalgebra@{o h} :
  @WCoalgebra (Subsets@{o h} (pt_carrier PTwoIndisc@{o}))
    (interior_functor (pinterior_op PTwoIndisc))
    (pinterior_comonad PTwoIndisc) true_sub → False.
Proof.
  intro c. destruct (pint_coalgebra_iff_open PTwoIndisc true_sub)
    as [to_open _].
  pose proof (to_open c true false eq_refl) as H.
  change (false = true :> bool) in H. discriminate H.
Qed.

(* * ** The closure: Riehl's footnote 5 / * ** 结语：Riehl 的脚注 5 *)

(* A closed subset is one whose complement is open. / 闭子集是其补集是开集的子集。 *)
Definition PClosedSub@{o} (X : PTop@{o}) (C : PSub X) : Prop :=
  POpen X (fun z => ~ C z).

(* "the intersection of all closed sets containing A" / 包含 A 的所有闭集的交集 *)
Definition pcl_fun@{o} (X : PTop@{o}) (S : PSub X) (x : pt_carrier X) :
  Prop :=
  ∀ C : PSub X, PClosedSub X C → subset_le S C → C x.

Lemma pcl_proper@{o} (X : PTop@{o}) (S : PSub X) (x y : pt_carrier X) :
  x ≈ y → Powerset_Prop_truth_equiv@{o} (pcl_fun X S x) (pcl_fun X S y).
Proof.
  intros Hxy; split; intros H C HC HSC.
  - exact (proj1 (proper_morphism C x y Hxy) (H C HC HSC)).
  - exact (proj2 (proper_morphism C x y Hxy) (H C HC HSC)).
Qed.

Definition pclosure@{o} (X : PTop@{o}) (S : PSub X) : PSub X :=
  @Build_SetoidMorphism@{o o o}
    (carrier (pt_carrier X)) (is_setoid (pt_carrier X))
    Prop (is_setoid Powerset_Prop_truth@{o}) (pcl_fun X S)
    (pcl_proper X S).

Definition pcl_mono@{o} (X : PTop@{o}) (S T : PSub X)
  (h : subset_le S T) : subset_le (pclosure X S) (pclosure X T) :=
  fun x H C HC HTC => H C HC (fun y Sy => HTC y (h y Sy)).

Definition pcl_ext@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le S (pclosure X S) :=
  fun x Sx C _ HSC => HSC x Sx.

Definition pcl_mult@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le (pclosure X (pclosure X S)) (pclosure X S) :=
  fun x H C HC HSC => H C HC (fun y Hy => Hy C HC HSC).

Definition pclosure_op@{o} (X : PTop@{o}) :
  ClosureOperator@{o} (subset_le_preorder@{o} (pt_carrier X)) :=
  {| cl_fun  := {| mono_map := pclosure X; mono_pres := pcl_mono X |}
   ; cl_ext  := pcl_ext X
   ; cl_mult := pcl_mult X |}.

Definition pclosure_monad@{o h} (X : PTop@{o}) :
  @Monad (Subsets@{o h} (pt_carrier X))
    (closure_functor@{o h} (pclosure_op X)) :=
  closure_monad@{o h} (pclosure_op X).

(* A closed subset contains its closure. Constructive. / 闭合集包含它的闭包。构造性。 *)
Definition pcl_sub_of_closed@{o} (X : PTop@{o}) (S : PSub X)
  (HS : PClosedSub X S) : subset_le (pclosure X S) S :=
  fun x H => H S HS (fun y Sy => Sy).

(*
 The converse, under excluded middle supplied as a hypothesis: used
 once to pass from "not every closed C above S contains z" to a closed
 C above S that misses z, and once for C z from ¬¬ C z. 

 --------
 逆命题，在排中律作为假设提供时：使用过一次，从“不是每个包含 S 的闭集 C 都包含 z”推导到一个包含 S 但不包含 z 的闭集 C；另一次用于从 ¬¬ C z 得到 C z。
*)
Lemma pcl_closed_of_sub@{o} (lem : ∀ P : Prop, P \/ ~ P) (X : PTop@{o})
  (S : PSub X) (h : subset_le (pclosure X S) S) : PClosedSub X S.
Proof.
  unfold PClosedSub.
  apply (popen_respects X (fun z => ex (fun U : pt_carrier X → Prop =>
     ex (fun C : PSub X =>
       (PClosedSub X C /\ subset_le S C) /\ ∀ w, U w <-> ~ C w) /\ U z))).
  - intro z; split.
    + intros [U [[C [[_ HSC] HU]] Uz]] Sz.
      exact (proj1 (HU z) Uz (HSC z Sz)).
    + intro nSz.
      destruct (lem (ex (fun C : PSub X =>
                        (PClosedSub X C /\ subset_le S C) /\ ~ C z)))
        as [[C [[HC HSC] nCz]]|none].
      * exists (fun w => ~ C w). split; [|exact nCz].
        exists C. split; [split; assumption|]. intro w; split; intro H; exact H.
      * exfalso. apply nSz, h. intros C HC HSC.
        destruct (lem (C z)) as [Cz|nCz]; [exact Cz|].
        exfalso; apply none; exists C; split; [split; assumption|exact nCz].
  - apply popen_union. intros U [C [[HC _] HU]].
    apply (popen_respects X (fun w => ~ C w)); [|exact HC].
    intro w; split; intro H; [exact (proj2 (HU w) H)|exact (proj1 (HU w) H)].
Qed.

(*
 Riehl 5.2.6 (iv), algebra half, through Instance/Proset/Monad.v's
 [talgebra_iff_closed]: a closed subset is an algebra (constructive),
 and an algebra is closed under the hypothesis [lem]. 

 --------
 Riehl 5.2.6 (iv)，代数部分，通过 Instance/Proset/Monad.v 的
 [talgebra_iff_closed]：一个闭子集是一个代数（构造性的），
 并且根据假设 [lem]，一个代数是封闭的。
*)
Definition pcl_talgebra_of_closed@{o h} (X : PTop@{o}) (S : PSub X)
  (HS : PClosedSub X S) :
  @TAlgebra (Subsets@{o h} (pt_carrier X))
    (closure_functor (pclosure_op X)) (pclosure_monad X) S :=
  let (_, of_closed) :=
    talgebra_iff_closed@{o h h} (closure_functor (pclosure_op X))
      (MM := pclosure_monad X) S in
  of_closed (pcl_sub_of_closed X S HS).

Definition pcl_closed_of_talgebra@{o h} (lem : ∀ P : Prop, P \/ ~ P)
  (X : PTop@{o}) (S : PSub X)
  (a : @TAlgebra (Subsets@{o h} (pt_carrier X))
         (closure_functor (pclosure_op X)) (pclosure_monad X) S) :
  PClosedSub X S :=
  let (to_closed, _) :=
    talgebra_iff_closed@{o h h} (closure_functor (pclosure_op X))
      (MM := pclosure_monad X) S in
  pcl_closed_of_sub lem X S (to_closed a).

(* Without [lem] the converse costs ¬¬(∀ q, ¬¬q → q). The subset {true} ∪ q of the indiscrete two-point space, closed exactly when ¬¬q. / 没有 [lem]，逆命题的代价是 ¬¬(∀ q, ¬¬q → q)。不可分的两点空间的子集 {true} ∪ q，当且仅当 ¬¬q 时闭合。 *)
Definition true_or_sub@{o} (q : Prop) : PSub PTwoIndisc@{o} :=
  @Build_SetoidMorphism@{o o o}
    (carrier (pt_carrier PTwoIndisc@{o})) (is_setoid (pt_carrier PTwoIndisc))
    Prop (is_setoid Powerset_Prop_truth@{o}) (fun b => b = true \/ q)
    (fun x y (Hxy : x = y) =>
       match Hxy in _ = z return Powerset_Prop_truth_equiv (x = true \/ q)
                                   (z = true \/ q) with
       | eq_refl => conj (fun H => H) (fun H => H)
       end).

(* The point false in the closure of {true} is double-negation elimination. / {true} 闭包中的错误点是双重否定消除。 *)
Lemma pcl_true_false_dne@{o} :
  pclosure@{o} PTwoIndisc true_sub false → ∀ q : Prop, ~ ~ q → q.
Proof.
  intros H q nnq.
  assert (HC : PClosedSub PTwoIndisc (true_or_sub q)).
  { intros x y nx ny. apply nnq. intro Hq. exact (nx (or_intror Hq)). }
  destruct (H (true_or_sub q) HC (fun y Hy => or_introl Hy)) as [Hf|Hq].
  - change (false = true :> bool) in Hf. discriminate Hf.
  - exact Hq.
Qed.

(*
 So the converse of [pcl_talgebra_of_closed], with no hypothesis, gives
 ¬¬(∀ q, ¬¬q → q): were that refuted, {true} would be an algebra, and
 {true} is not closed. 

 --------
 所以 [pcl_talgebra_of_closed] 的逆命题，在没有假设的情况下，给出 ¬¬(∀ q, ¬¬q → q)：如果这被驳斥，{true} 将是一个代数，而 {true} 并不是闭合的。
*)
Lemma pcl_converse_nndne@{o h} :
  (∀ (X : PTop@{o}) (S : PSub X),
     @TAlgebra (Subsets@{o h} (pt_carrier X))
       (closure_functor (pclosure_op X)) (pclosure_monad X) S →
     PClosedSub X S) →
  ~ ~ (∀ q : Prop, ~ ~ q → q).
Proof.
  intros conv ndne.
  assert (alg : subset_le (pclosure PTwoIndisc true_sub) true_sub).
  { intros [|] H.
    - reflexivity.
    - exfalso. exact (ndne (pcl_true_false_dne H)). }
  destruct (talgebra_iff_closed@{o h h}
              (closure_functor (pclosure_op PTwoIndisc))
              (MM := pclosure_monad PTwoIndisc) true_sub) as [_ of_closed].
  pose proof (conv PTwoIndisc true_sub (of_closed alg)) as HC.
  exact (HC false true (fun Hf => ltac:(change (false = true :> bool) in Hf;
                                         discriminate Hf)) eq_refl).
Qed.

(* * ** A constructive alternative: the closure as ¬ int (¬ S) / * ** 一个建设性的替代方案：闭包作为 ¬ int (¬ S) *)

(* The pointwise complement of a subset. / 子集的逐点补集。 *)
Lemma pcomp_proper@{o} (X : PTop@{o}) (S : PSub X) (x y : pt_carrier X) :
  x ≈ y → Powerset_Prop_truth_equiv@{o} (~ S x) (~ S y).
Proof.
  intros Hxy; split; intros nS Sy; apply nS.
  - exact (proj2 (proper_morphism S x y Hxy) Sy).
  - exact (proj1 (proper_morphism S x y Hxy) Sy).
Qed.

Definition pcomp@{o} (X : PTop@{o}) (S : PSub X) : PSub X :=
  @Build_SetoidMorphism@{o o o}
    (carrier (pt_carrier X)) (is_setoid (pt_carrier X))
    Prop (is_setoid Powerset_Prop_truth@{o}) (fun x => ~ S x)
    (pcomp_proper X S).

(* The complement of the interior of the complement. / 补集的补集的内部。 *)
Definition ncl@{o} (X : PTop@{o}) (S : PSub X) : PSub X :=
  pcomp X (pinterior X (pcomp X S)).

Definition ncl_mono@{o} (X : PTop@{o}) (S T : PSub X)
  (h : subset_le S T) : subset_le (ncl X S) (ncl X T) :=
  fun x nS '(ex_intro _ U (conj (conj HU HUT) Ux)) =>
    nS (ex_intro _ U (conj (conj HU (fun y Uy Sy => HUT y Uy (h y Sy))) Ux)).

Definition ncl_ext@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le S (ncl X S) :=
  fun x Sx '(ex_intro _ U (conj (conj _ HUS) Ux)) => HUS x Ux Sx.

Definition ncl_mult@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le (ncl X (ncl X S)) (ncl X S) :=
  fun x H Hi =>
    H (pint_mono X (pinterior X (pcomp X S)) (pcomp X (ncl X S))
         (fun y Iy nIy => nIy Iy) x (pint_comult X (pcomp X S) x Hi)).

Definition nclosure_op@{o} (X : PTop@{o}) :
  ClosureOperator@{o} (subset_le_preorder@{o} (pt_carrier X)) :=
  {| cl_fun  := {| mono_map := ncl X; mono_pres := ncl_mono X |}
   ; cl_ext  := ncl_ext X
   ; cl_mult := ncl_mult X |}.

Definition nclosure_monad@{o h} (X : PTop@{o}) :
  @Monad (Subsets@{o h} (pt_carrier X))
    (closure_functor@{o h} (nclosure_op X)) :=
  closure_monad@{o h} (nclosure_op X).

(* Closed in the second sense: the complement of an open subset. / 在第二种意义上封闭：开子集的补集。 *)
Definition PCoOpen@{o} (X : PTop@{o}) (S : PSub X) : Prop :=
  ex (fun U : pt_carrier X → Prop => POpen X U /\ ∀ x, S x <-> ~ U x).

Lemma ncl_sub_iff_coopen@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le (ncl X S) S <-> PCoOpen X S.
Proof.
  split.
  - intro h. exists (pinterior X (pcomp X S)).
    split; [exact (pint_open X (pcomp X S))|].
    intro x; split.
    + intros Sx Hi. exact (pint_defl X (pcomp X S) x Hi Sx).
    + exact (h x).
  - intros [U [HU HS]] x nI. apply (proj2 (HS x)). intro Ux.
    apply (nI : ~ pinterior X (pcomp X S) x).
    exists U. split; [|exact Ux]. split; [exact HU|].
    intros y Uy Sy. exact (proj1 (HS y) Sy Uy).
Qed.

(*
 The algebras of the ¬ int ¬ closure are exactly the complements of
 opens, in both directions with no hypothesis. 

 --------
 ¬ int ¬ 闭包的代数正好是开集的补集，在没有任何假设的情况下，两个方向都成立。
*)
Definition ncl_talgebra_iff_coopen@{o h p} (X : PTop@{o}) (S : PSub X) :
  iffT@{h p}
    (@TAlgebra (Subsets@{o h} (pt_carrier X))
       (closure_functor (nclosure_op X)) (nclosure_monad X) S)
    (PCoOpen X S) :=
  let (to_closed, of_closed) :=
    talgebra_iff_closed@{o h p} (closure_functor (nclosure_op X))
      (MM := nclosure_monad X) S in
  (fun a => proj1 (ncl_sub_iff_coopen X S) (to_closed a),
   fun H => of_closed (proj2 (ncl_sub_iff_coopen X S) H)).

(* Non-vacuity, constructively: {true} in the indiscrete two-point space is not the complement of an open. / 非空性，构造上：在非离散的两点空间中 {true} 不是一个开集的补集。 *)
Lemma true_sub_not_nclosed@{o h} :
  @TAlgebra (Subsets@{o h} (pt_carrier PTwoIndisc@{o}))
    (closure_functor (nclosure_op PTwoIndisc))
    (nclosure_monad PTwoIndisc) true_sub → False.
Proof.
  intro a. destruct (ncl_talgebra_iff_coopen PTwoIndisc true_sub)
    as [to_coopen _].
  destruct (to_coopen a) as [U [HU HS]].
  pose proof (proj1 (HS true) eq_refl) as nUt.
  assert (nUf : ~ U false) by (intro Uf; exact (nUt (HU false true Uf))).
  pose proof (proj2 (HS false) nUf) as H.
  change (false = true :> bool) in H. discriminate H.
Qed.

(* * ** The two routes agree under excluded middle / * ** 这两条路线在排中律下是一致的 *)

(* A complement of an open is ¬¬-stable. / 一个开集的补集是¬¬-稳定的。 *)
Lemma coopen_stable@{o} (X : PTop@{o}) (S : PSub X) (H : PCoOpen X S)
  (x : pt_carrier X) : ~ ~ S x → S x.
Proof.
  destruct H as [U [_ HS]]. intro nnS. apply (proj2 (HS x)). intro Ux.
  apply nnS. intro Sx. exact (proj1 (HS x) Sx Ux).
Qed.

Lemma coopen_of_closed_stable@{o} (X : PTop@{o}) (S : PSub X)
  (HS : PClosedSub X S) (stable : ∀ x, ~ ~ S x → S x) : PCoOpen X S.
Proof.
  exists (fun z => ~ S z). split; [exact HS|].
  intro x; split; [intros Sx nSx; exact (nSx Sx)|exact (stable x)].
Qed.

Lemma closed_of_coopen_lem@{o} (lem : ∀ P : Prop, P \/ ~ P)
  (X : PTop@{o}) (S : PSub X) (H : PCoOpen X S) : PClosedSub X S.
Proof.
  destruct H as [U [HU HS]]. unfold PClosedSub.
  apply (popen_respects X U); [|exact HU].
  intro x; split.
  - intros Ux Sx. exact (proj1 (HS x) Sx Ux).
  - intro nSx. destruct (lem (U x)) as [Ux|nUx]; [exact Ux|].
    exfalso. exact (nSx (proj2 (HS x) nUx)).
Qed.

Lemma pclosure_ncl_lem@{o} (lem : ∀ P : Prop, P \/ ~ P) (X : PTop@{o})
  (S : PSub X) (x : pt_carrier X) : pclosure X S x <-> ncl X S x.
Proof.
  split.
  - intro H.
    assert (HC : PClosedSub X (ncl X S)).
    { unfold PClosedSub.
      apply (popen_respects X (pinterior X (pcomp X S)));
        [|exact (pint_open X (pcomp X S))].
      intro z; split.
      - intros Hi nI. exact (nI Hi).
      - intro nnI.
        destruct (lem (pinterior X (pcomp X S) z)) as [Hi|nI]; [exact Hi|].
        exfalso; exact (nnI nI). }
    exact (H (ncl X S) HC (ncl_ext X S)).
  - intros N C HC HSC. destruct (lem (C x)) as [Cx|nCx]; [exact Cx|].
    exfalso. apply (N : ~ pinterior X (pcomp X S) x).
    exists (fun z => ~ C z). split; [|exact nCx].
    split; [exact HC|]. intros y nCy Sy. exact (nCy (HSC y Sy)).
Qed.
