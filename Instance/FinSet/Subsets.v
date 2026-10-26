Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Topos.
Require Import Category.Instance.FinSet.Powerset.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Powerset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(*
   * * The power set of a finite set, ordered by inclusion, COMPUTING

   Seven Sketches (Fong and Spivak, “An Invitation to Applied Category
   Theory”) §1.2.2 Examples 50 and 51 and §1.4.3 Examples 117 and 118.
   There is no page image for that book here, so the clauses are quoted
   from the catalog issue's own transcription: the power sets of the
   zero-, one- and two-element sets with their inclusion orders drawn
   out, and then the apples-and-buckets function with its preimage, its
   direct image and its dual image evaluated at named subsets.

   nLab: https://ncatlab.org/nlab/show/power+set
   nLab: https://ncatlab.org/nlab/show/subobject+classifier
   nLab: https://ncatlab.org/nlab/show/power+object

   ** WHAT IS DELIVERED, WITH GRADES

   (A) A decidable bounded quantifier pair, [fin_allb] and [fin_anyb],
   with both halves of each specification.  Neither name occurs
   anywhere else in the tree; the three existing [Fin.t]
   enumerations ([all_fins] in Instance/Matr/Determinant.v,
   [fin_enum] in Instance/FinSet/Skeleton.v, [all_fin] in
   Instance/FinSet/Pushout.v) enumerate a LIST, which is a heavier
   instrument than a fold to [bool] and, in the first case, sits in
   a module whose closure is far larger than this file's.

   (B) [finpow_le], its [PreOrder], and [FinSubsets n], the power set of
   the n-element set as a thin category over Instance/Proset.v's
   [Proset].  The objects are EXACTLY the [finpow n] codes
   ([FinSubsets_obj_is_code], [eq_refl]), so the three counts of
   Example 50 are [finpow 0 = 1], [finpow 1 = 2], [finpow 2 = 4],
   all by [eq_refl].  The orders are exhibited: at n = 1 the two
   codes [empty1]/[full1] with the one inclusion inhabited and its
   converse refuted; at n = 2 the four codes with all FIVE
   non-identity inclusions inhabited and BOTH incomparabilities
   refuted ([sub2_01_not_le_10], [sub2_10_not_le_01]), so
   [FinSubsets 2] is provably not a chain -- which is what
   distinguishes the power set of a two-element set from an
   arbitrary four-element order.  Every one of these is [eq_refl] or
   [discriminate], because [finpow_mem] is a decidable test; its
   [Subsets] cousin over an arbitrary Prop-valued predicate could
   not be enumerated constructively at all.

   (C) The comparison with Instance/Powerset.v: [finpow_to_subset] turns
   a code into a Prop-valued subset of the discrete setoid
   [Powerset_Prop_fin_object n], monotone and ORDER-REFLECTING, so
   [FinSubsetsToSubsets n : FinSubsets n ⟶ Subsets _] is proved
   [Full] -- order reflection is exactly what [Full] spends.
   [FinSubsetsToSubsets_Faithful] is shipped beside it but carries
   NO content: the source is thin, so [f ≈ g] there is [True] and
   every functor out of [FinSubsets n] is faithful by the same
   one-line proof.  Essential surjectivity is NOT claimed: it would
   decide an arbitrary Prop-valued predicate.

   (D) [FinSet_Pow_one : Pow 1 = 2] by [eq_refl] -- the missing member of
   Instance/FinSet/Topos.v's [FinSet_Pow_zero]/[FinSet_Pow_two]
   family, which lives here rather than there.  The GENERAL form
   [finpow_is_topos_Pow] is NOT new: Instance/FinSet/Powerset.v
   already proves [Pow n = finpow n] for open [n], and it is cited,
   not duplicated.

   (E) The INTERNAL inclusion order on the power object at [FinSet]:
   [finpow_subseteq] as a [bool] and
   [internal_subseteq n : Pow n × Pow n ~{FinSet}~> Ω] as an arrow
   of the category, with [internal_subseteq_spec] proving the
   internal test EQUIVALENT to the external order [finpow_le] -- so
   the two readings agree, not merely correspond.  The general-topos
   internal inclusion is NOT delivered, and the obstruction is
   measured rather than guessed: it would be the equalizer of the
   first projection against the composite of an internal
   conjunction with the two evaluations, and the tree HAS NO
   internal conjunction on Ω: no constant anywhere has type
   [Ω × Ω ~> Ω], and the characteristic map of ⟨truth, truth⟩
   appears nowhere.  Read that measurement at its scope -- the word
   “meet” DOES occur in Structure/Topos.v, but as prose
   describing what a Lawvere-Tierney topology is, not as a
   constant.

   (F) Example 118, evaluated.  [apples : 3 ~> 2] puts two apples in
   bucket 0 and one in bucket 1.  [finpow_preimage] is
   Instance/FinSet/Powerset.v's [finpow_map] under a name that
   says what it is ([finpow_preimage_is_finpow_map], [eq_refl] --
   the inverse image on codes was ALREADY the arrow action of
   [FinPowerset], and nothing is rebuilt); [finpow_image] and
   [finpow_dual] are new.  Six [eq_refl] evaluations at closed
   inputs chosen so the three operations VISIBLY differ: at {0} the
   image is {0} while the dual is empty (apple 1 is missing), at
   {0,1} both are {0}.  Example 117's left half -- the preimage has
   a LEFT adjoint -- is [finpow_image_preimage_galois]; its right
   half, the dual image as a RIGHT adjoint, is #384's and is NOT
   built here.  The EVALUATIONS of [finpow_dual] are this file's;
   the adjunction it satisfies is not.

   ** WHAT IS NOT DELIVERED

   The dual-image adjunction (#384).  The general-topos internal
   inclusion, for the measured reason above.  No isomorphism between
   [FinSubsets n] and [Subsets (Powerset_Prop_fin_object n)] (only the
   full and faithful comparison).  No link between [finpow_subseteq] and
   [sub_le] on [SubObj n] through [FinSet_Sub_powerset]/[finpow_codec]:
   that would need the classifier round trip carried across the
   subobject setoid, which is a further construction and is only
   cross-referenced.  No [Cartesian]/[Complete] structure on
   [FinSubsets], which would be Instance/Powerset.v's development
   repeated over codes.

   ** UNIVERSES

   [FinSubsets@{u}] carries a [Set] BOUND from [Fin.t n : Set], not an
   identification; everything mentioning [Powerset_Prop_obj] inherits
   [Set < o] from the donor as usual.  Measured per constant in the
   report.

   ** TRANSPARENCY

   [finpow_to_subset] MUST be [Defined] -- measured by flipping it to
   [Qed], which breaks the file, its predicate being read through by
   the two monotonicity lemmas.  [FinSubsetsToSubsets_Full] and the
   inline [FinSubsetsToSubsets_Faithful] each compile as [Qed] and are
   [Defined] for uniformity -- three [Defined]s in this file.

   ** REGISTRATION

   Nothing here is an [Instance]. 

   --------
   * * 有限集的幂集，按包含关系排序，计算中

   《七个草图》（Fong 和 Spivak，《应用范畴论邀请》）§1.2.2 例子 50 和 51 以及 §1.4.3 例子 117 和 118。
   这本书在此没有页面图像，因此条款引用自目录期刊自己的转录：画出零元素、一元素和二元素集合的幂集及其包含顺序，然后评估苹果与桶函数及其原像、直接像和对偶像在命名子集上的值。

   nLab: https://ncatlab.org/nlab/show/power+set
   nLab: https://ncatlab.org/nlab/show/subobject+classifier
   nLab: https://ncatlab.org/nlab/show/power+object

   ** 交付内容及评分(A) 一个可判定的有界量词对，[fin_allb] 和 [fin_anyb]，具有各自规格的两个部分。这两个名称在树中其他地方都没有出现；现有的三个 [Fin.t] 枚举（Instance/Matr/Determinant.v 中的 [all_fins]，Instance/FinSet/Skeleton.v 中的 [fin_enum]，Instance/FinSet/Pushout.v 中的 [all_fin]）枚举的是一个 LIST，这比 [bool] 的折叠要重，并且在第一种情况下，它位于一个闭包远大于此文件的模块中。(B) [finpow_le]、它的 [PreOrder] 和 [FinSubsets n]，作为 Instance/Proset.v 的 [Proset] 上的薄范畴，表示 n 元集合的幂集。对象正好是 [finpow n] 代码 ([FinSubsets_obj_is_code]、[eq_refl])，因此示例 50 的三个计数分别是 [finpow 0 = 1]、[finpow 1 = 2]、[finpow 2 = 4]，全都由 [eq_refl] 得出。阶序展示如下：当 n = 1 时，两个代码 [empty1] / [full1] 的一个包含关系成立，其逆关系被否定；当 n = 2 时，四个代码中所有五个非同一性包含关系都成立，两个不可比关系都被否定 ([sub2_01_not_le_10]、[sub2_10_not_le_01])，因此 [FinSubsets 2] 可证明不是链——这正是区分二元集合的幂集和任意四元有序集的地方。这些每一个都是[eq_refl]或[discriminate]，因为[finpow_mem]是可判定的测试；它的[Subsets]表亲在任意Prop值谓词上的情况根本无法构造性地枚举。

   (C) 与Instance/Powerset.v的比较：[finpow_to_subset]将代码转换为离散集合器[Powerset_Prop_fin_object n]的Prop值子集，单调且顺序反射，因此[FinSubsetsToSubsets n : FinSubsets n ⟶ Subsets _]被证明为[Full]——顺序反射正是[Full]所花费的。[FinSubsetsToSubsets_Faithful]与其一起发布，但不携带任何内容：源代码很少，因此[f ≈ g]在那里是[True]，且每个[FinSubsets n]的函子都通过同样的一行证明是忠实的。不声称基本满射性：它将决定任意Prop值谓词。(D) [FinSet_Pow_one : Pow 1 = 2] 由 [eq_refl] 提出 —— 是 Instance/FinSet/Topos.v 文件中 [FinSet_Pow_zero] / [FinSet_Pow_two] 系列中缺失的成员，它存在于这里而不是那里。一般形式的 [finpow_is_topos_Pow] 不是新的：Instance/FinSet/Powerset.v 已经证明了开集 [n] 的 [Pow n = finpow n]，并且它被引用，而不是重复。(E) 在 [FinSet] 的幂对象上的内部包含顺序：
   将 [finpow_subseteq] 视为 [bool] ，并将
   [internal_subseteq n : Pow n × Pow n ~{FinSet}~> Ω] 视为该范畴的箭头，
   其中 [internal_subseteq_spec] 证明了内部测试与外部顺序 [finpow_le] 等价——因此两种解释相符，而不仅仅是对应。一般拓扑层的内部包含未被实现，其障碍是经过测量而非猜测的：它将是第一个投影与内部结合与两次求值复合的等化器，并且该树在 Ω 上没有内部结合：没有任何常量的类型为 [Ω × Ω ~> Ω]，并且 ⟨真, 真⟩ 的特征映射处处都不存在。在其范围内阅读该测量——单词“meet”确实出现在 Structure/Topos.v 中，但作为描述 Lawvere-Tierney 拓扑是什么的散文，而不是作为常量。（F）示例118，已评估。[apples : 3 ~> 2]放入两个苹果
   桶0和桶1的1。[finpow_preimage]是
   Instance/FinSet/Powerset.v 的 [finpow_map]
   说明它是什么（[finpow_preimage_is_finpow_map]，[eq_refl] --
   码上的反像本身就是箭头作用
   [FinPowerset] ，且不重建）;[finpow_image] 和
   [finpow_dual]是新来的。六[eq_refl]评估已结束
   输入选择使三操作可视不同：在{0}
   图像为{0}，而对偶为空（Apple 1缺失），在
   {0,1} 两者都是{0}。例子117的左半部分——原像有
   左伴随——是[finpow_image_preimage_galois];它的右
   作为右伴随的对偶像，一半是#384的，不是
   这里建的。[finpow_dual] 的评估在此文件中；
   它满足的附加条件不在此。

   ** 未提供的内容

   双图象附加 (#384)。 上述测量原因的通用拓扑内部包含。 [FinSubsets n] 和 [Subsets (Powerset_Prop_fin_object n)] 之间没有同构（只有完全忠实的比较）。[SubObj n] 上通过 [FinSet_Sub_powerset] / [finpow_codec] 的 [finpow_subseteq] 和 [sub_le] 之间没有链接：这需要在子对象等价集合上执行分类器往返，这是一个进一步的构造，仅作交叉引用。 [FinSubsets] 上没有 [Cartesian] / [Complete] 结构，这将是 Instance/Powerset.v 对代码的开发重复。

   ** 宇宙[FinSubsets@{u}] 携带来自 [Fin.t n : Set] 的 [Set] BOUND，而不是身份标识；所有提到 [Powerset_Prop_obj] 的内容都像通常一样继承自捐赠者的 [Set < o]。按报告中的常数测量。

   ** 透明性

   [finpow_to_subset] 必须是 [Defined] ——通过将其翻转到 [Qed] 来测量，这会破坏文件，其前提通过两个单调性引理读取。[FinSubsetsToSubsets_Full] 和内联的 [FinSubsetsToSubsets_Faithful] 各自编译为 [Qed]，并且为了统一性为 [Defined] ——本文件中有三个 [Defined]。

   ** 注册

   这里没有任何内容是 [Instance]。
*)

(* ------------------------------------------------------------------------ *)
(* * ** (A) Bounded decidable quantifiers over [Fin.t] / * **（A）在 [Fin.t] 上有界可判定量词 *)

Fixpoint fin_allb (n : nat) : (Fin.t n → bool) → bool :=
  match n with
  | O    => fun _ => true
  | S m  => fun g => andb (g Fin.F1) (fin_allb m (fun i => g (Fin.FS i)))
  end.

Fixpoint fin_anyb (n : nat) : (Fin.t n → bool) → bool :=
  match n with
  | O    => fun _ => false
  | S m  => fun g => orb (g Fin.F1) (fin_anyb m (fun i => g (Fin.FS i)))
  end.

Lemma fin_allb_forall (n : nat) (g : Fin.t n → bool) :
  fin_allb n g = true → ∀ i : Fin.t n, g i = true.
Proof.
  induction n as [| m IH]; intros H i.
  - exact (Fin.case0 (fun _ => g i = true) i).
  - simpl in H.
    apply Bool.andb_true_iff in H; destruct H as [H1 H2].
    refine (Fin.caseS' i (fun j => g j = true) H1 _).
    intro j; exact (IH (fun p => g (Fin.FS p)) H2 j).
Qed.

Lemma fin_forall_allb (n : nat) (g : Fin.t n → bool) :
  (∀ i : Fin.t n, g i = true) → fin_allb n g = true.
Proof.
  induction n as [| m IH]; intro H; simpl.
  - reflexivity.
  - apply Bool.andb_true_iff; split.
    + exact (H Fin.F1).
    + exact (IH (fun p => g (Fin.FS p)) (fun p => H (Fin.FS p))).
Qed.

Lemma fin_anyb_exists (n : nat) (g : Fin.t n → bool) :
  fin_anyb n g = true → ∃ i : Fin.t n, g i = true.
Proof.
  induction n as [| m IH]; intro H; simpl in H.
  - discriminate H.
  - (* [orb_true_elim] lands in [sumbool], which -- unlike [orb_true_iff]'s [or] -- may be eliminated into the [Type]-valued [∃] the conclusion uses. / [orb_true_elim] 降落在 [sumbool] 上，与 [orb_true_iff] 的 [or] 不同——它可以被消除为结论使用的 [Type] 值的 [∃]。 *)
    destruct (Bool.orb_true_elim _ _ H) as [H1 | H1].
    + exists Fin.F1; exact H1.
    + destruct (IH (fun p => g (Fin.FS p)) H1) as [j Hj].
      exists (Fin.FS j); exact Hj.
Qed.

Lemma fin_exists_anyb (n : nat) (g : Fin.t n → bool) (i : Fin.t n) :
  g i = true → fin_anyb n g = true.
Proof.
  induction n as [| m IH]; intro H.
  - exact (Fin.case0 (fun _ => fin_anyb 0 g = true) i).
  - simpl; apply Bool.orb_true_iff.
    revert H.
    refine (Fin.caseS' i (fun j => g j = true → _) _ _).
    + intro H; left; exact H.
    + intros j H; right.
      exact (IH (fun p => g (Fin.FS p)) j H).
Qed.

(* Membership reads a boolean back through [fin_of_bool] on the nose. / Membership 通过 [fin_of_bool] 直接读取布尔值。 *)
Lemma finpow_mem_of_bool (b : bool) : fin_eqb (fin_of_bool b) fin_true = b.
Proof. destruct b; reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** (B) The inclusion order on codes, and the thin category / * **（B）代码上的包含顺序，以及薄范畴 *)

Definition finpow_le {n : nat} (S T : Fin.t (finpow n)) : Prop :=
  ∀ i : Fin.t n, finpow_mem S i = true → finpow_mem T i = true.

Definition finpow_le_preorder (n : nat) : PreOrder (@finpow_le n) :=
  {| PreOrder_Reflexive  := fun S i Hi => Hi
   ; PreOrder_Transitive :=
       fun S T U HST HTU i Hi => HTU i (HST i Hi) |}.

(*
 A decidable order needs no argument: [fin_allb] settles every one of
 the four codes' comparisons by computation. 

 --------
 一个可判定的顺序不需要论证：[fin_allb] 通过计算解决了四个代码比较中的每一个问题。
*)
Lemma finpow_le_of_allb (n : nat) (S T : Fin.t (finpow n)) :
  fin_allb n (fun i => implb (finpow_mem S i) (finpow_mem T i)) = true →
  finpow_le S T.
Proof.
  intros H i Hi.
  pose proof (fin_allb_forall n
    (fun j => implb (finpow_mem S j) (finpow_mem T j)) H i) as Hj.
  cbv beta in Hj.
  rewrite Hi in Hj; exact Hj.
Qed.

Definition FinSubsets@{u} (n : nat) : Category@{Set u u} :=
  Proset@{Set u} (finpow_le_preorder n).

Example FinSubsets_obj_is_code@{u} (n : nat) :
  obj[FinSubsets@{u} n] = Fin.t (finpow n) := eq_refl.

Example FinSubsets_hom_is_finpow_le@{u} (n : nat)
  (S T : FinSubsets@{u} n) :
  (S ~{FinSubsets@{u} n}~> T) = finpow_le S T := eq_refl.

(* * ** Example 50: the three small power sets, counted and drawn / * ** 示例50：三个小幂集，已计数并绘制 *)

Example finpow_zero_count : finpow 0 = 1%nat := eq_refl.
Example finpow_one_count  : finpow 1 = 2%nat := eq_refl.
Example finpow_two_count  : finpow 2 = 4%nat := eq_refl.

(* n = 1: the two subsets of a one-element set. / n = 1：一个一元素集合的两个子集。 *)
Definition empty1 : Fin.t (finpow 1) := fin_tabulate (fun _ => fin_false).
Definition full1  : Fin.t (finpow 1) := fin_tabulate (fun _ => fin_true).

Example empty1_at_0 : finpow_mem empty1 Fin.F1 = false := eq_refl.
Example full1_at_0  : finpow_mem full1  Fin.F1 = true  := eq_refl.

Definition empty1_le_full1 : finpow_le empty1 full1 :=
  finpow_le_of_allb 1 empty1 full1 eq_refl.

Lemma full1_not_le_empty1 : finpow_le full1 empty1 → False.
Proof. intro H; discriminate (H Fin.F1 eq_refl). Qed.

(* n = 2: the four subsets of a two-element set, and the square. / n = 2：一个二元素集合的四个子集，以及正方形。 *)
Definition sub2_00 : Fin.t (finpow 2) := fin_tabulate (fun _ => fin_false).
Definition sub2_10 : Fin.t (finpow 2) :=
  fin_tabulate (fun i => match i with
                         | Fin.F1 => fin_true
                         | _      => fin_false
                         end).
Definition sub2_01 : Fin.t (finpow 2) :=
  fin_tabulate (fun i => match i with
                         | Fin.F1 => fin_false
                         | _      => fin_true
                         end).
Definition sub2_11 : Fin.t (finpow 2) := fin_tabulate (fun _ => fin_true).

Example sub2_10_at_0 : finpow_mem sub2_10 Fin.F1 = true := eq_refl.
Example sub2_10_at_1 :
  finpow_mem sub2_10 (Fin.FS Fin.F1) = false := eq_refl.
Example sub2_01_at_0 : finpow_mem sub2_01 Fin.F1 = false := eq_refl.
Example sub2_01_at_1 :
  finpow_mem sub2_01 (Fin.FS Fin.F1) = true := eq_refl.

(* The five non-identity inclusions of the square. / 正方形的五个非自同构包含。 *)
Definition sub2_00_le_10 : finpow_le sub2_00 sub2_10 :=
  finpow_le_of_allb 2 sub2_00 sub2_10 eq_refl.
Definition sub2_00_le_01 : finpow_le sub2_00 sub2_01 :=
  finpow_le_of_allb 2 sub2_00 sub2_01 eq_refl.
Definition sub2_00_le_11 : finpow_le sub2_00 sub2_11 :=
  finpow_le_of_allb 2 sub2_00 sub2_11 eq_refl.
Definition sub2_10_le_11 : finpow_le sub2_10 sub2_11 :=
  finpow_le_of_allb 2 sub2_10 sub2_11 eq_refl.
Definition sub2_01_le_11 : finpow_le sub2_01 sub2_11 :=
  finpow_le_of_allb 2 sub2_01 sub2_11 eq_refl.

(* ... and the two incomparabilities that make it a square and not a chain. / ...以及使其成为方形而不是链式的两种不可比性。 *)
Lemma sub2_01_not_le_10 : finpow_le sub2_01 sub2_10 → False.
Proof. intro H; discriminate (H (Fin.FS Fin.F1) eq_refl). Qed.

Lemma sub2_10_not_le_01 : finpow_le sub2_10 sub2_01 → False.
Proof. intro H; discriminate (H Fin.F1 eq_refl). Qed.

(* ------------------------------------------------------------------------ *)
(* * ** (C) The comparison with the Prop-valued power set / * **（C）与取值为 Prop 的幂集的比较 *)

Definition finpow_to_subset@{o +} (n : nat) (S : Fin.t (finpow n)) :
  carrier (Powerset_Prop_obj@{o} (Powerset_Prop_fin_object@{o} n)).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (Fin.t n) (is_setoid (Powerset_Prop_fin_object@{o} n))
       Prop (is_setoid Powerset_Prop_truth@{o})
       (fun i => finpow_mem S i = true) _).
  intros i j Hij; rewrite Hij; split; exact (fun h => h).
Defined.

(*
 Monotone, and ORDER-REFLECTING: both directions are the same
 implication read through the definition of [finpow_to_subset]. 

 --------
 单调，并且反映顺序：两个方向相同的含义，通过 [finpow_to_subset] 的定义阅读。
*)
Lemma finpow_to_subset_mono@{o} (n : nat) (S T : Fin.t (finpow n)) :
  finpow_le S T →
  subset_le (finpow_to_subset@{o} n S) (finpow_to_subset@{o} n T).
Proof. intros H i Hi; exact (H i Hi). Qed.

Lemma finpow_to_subset_reflects@{o} (n : nat) (S T : Fin.t (finpow n)) :
  subset_le (finpow_to_subset@{o} n S) (finpow_to_subset@{o} n T) →
  finpow_le S T.
Proof. intros H i Hi; exact (H i Hi). Qed.

Definition finpow_subset_MonotoneFun@{o +} (n : nat) :
  @MonotoneFun _ (@finpow_le n) _
    (@subset_le@{o} (Powerset_Prop_fin_object@{o} n)) :=
  {| mono_map  := finpow_to_subset@{o} n
   ; mono_pres := finpow_to_subset_mono@{o} n |}.

Definition FinSubsetsToSubsets@{o u +} (n : nat) :
  FinSubsets@{u} n ⟶ Subsets@{o u} (Powerset_Prop_fin_object@{o} n) :=
  Functor_of_monotone (finpow_le_preorder n)
    (subset_le_preorder@{o} (Powerset_Prop_fin_object@{o} n))
    (finpow_subset_MonotoneFun n).

Definition FinSubsetsToSubsets_Faithful@{o u +} (n : nat) :
  Faithful (FinSubsetsToSubsets@{o u} n).
Proof. constructor; intros x y f g _; exact I. Defined.

Definition FinSubsetsToSubsets_Full@{o u +} (n : nat) :
  Full (FinSubsetsToSubsets@{o u} n).
Proof.
  unshelve econstructor.
  - intros x y g; exact (finpow_to_subset_reflects n x y g).
  - intros x y g; exact I.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** (D) The power object at 1 / ** (D) 电源对象在1 *)

(*
 The missing member of Instance/FinSet/Topos.v's family: [Pow 0 = 1] and
 [Pow 2 = 4] are there, [Pow 1 = 2] is here.  The GENERAL statement
 [finpow_is_topos_Pow] is Instance/FinSet/Powerset.v and is cited,
 not duplicated. 

 --------
 Instance/FinSet/Topos.v 家族中缺失的成员：[Pow 0 = 1] 和 [Pow 2 = 4] 已经存在，[Pow 1 = 2] 在这里。通用声明 [finpow_is_topos_Pow] 在 Instance/FinSet/Powerset.v 中，并已被引用，没有重复。
*)
Example FinSet_Pow_one : @Pow FinSet FinSet_Topos 1%nat = 2%nat := eq_refl.

Example FinSet_Omega_is_two :
  @Ω FinSet FinSet_Terminal FinSet_Classifier = 2%nat := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** (E) The internal inclusion order on the power object / * ** (E) 幂对象上的内部包含顺序 *)

Definition finpow_subseteq {n : nat} (S T : Fin.t (finpow n)) : bool :=
  fin_allb n (fun i => implb (finpow_mem S i) (finpow_mem T i)).

Lemma finpow_subseteq_iff (n : nat) (S T : Fin.t (finpow n)) :
  finpow_subseteq S T = true ↔ finpow_le S T.
Proof.
  split.
  - exact (finpow_le_of_allb n S T).
  - intro H.
    apply fin_forall_allb; intro i.
    destruct (finpow_mem S i) eqn:HS; simpl.
    + exact (H i HS).
    + reflexivity.
Qed.

(*
 The underlying function, stated over [finpow] so that the implicit
 arguments of [fin_unpair] are the codes and not the (convertible, but
 syntactically distinct) [Pow] applications.  That distinction is not
 cosmetic: without it, the two occurrences of
 [finpow_subseteq (fst (fin_unpair p)) (snd (fin_unpair p))] in the
 theorem below carry different implicits and no rewrite matches. 

 --------
 底层函数在  [finpow]  上声明，因此  [fin_unpair]  的隐式参数是代码，而不是（可转换的，但语法上不同的） [Pow] 应用。这个区别不是表面的：如果没有它，下述定理中 [finpow_subseteq (fst (fin_unpair p)) (snd (fin_unpair p))] 的两个出现具有不同的隐式参数，并且没有重写匹配。
*)
Definition finpow_subseteq_fn (n : nat)
  (p : Fin.t (finpow n * finpow n)) : Fin.t 2 :=
  fin_of_bool (finpow_subseteq (fst (fin_unpair p)) (snd (fin_unpair p))).

(*
 The internal order as an ARROW of [FinSet], from the product of the
 power object with itself to Ω. 

 --------
 作为[FinSet]的箭头的内部序，从幂对象与自身的积到Ω。
*)
Definition internal_subseteq (n : nat) :
  @product_obj FinSet FinSet_Cartesian
    (@Pow FinSet FinSet_Topos n) (@Pow FinSet FinSet_Topos n)
  ~{FinSet}~> @Ω FinSet FinSet_Terminal FinSet_Classifier :=
  finpow_subseteq_fn n.

Example internal_subseteq_is_fn (n : nat)
  (p : Fin.t (finpow n * finpow n)) :
  internal_subseteq n p = finpow_subseteq_fn n p := eq_refl.

(* THE INTERNAL TEST IS THE EXTERNAL ORDER. / 内部测试就是外部订单。 *)
Theorem internal_subseteq_spec (n : nat)
  (p : Fin.t (finpow n * finpow n)) :
  internal_subseteq n p = fin_true
    ↔ finpow_le (fst (fin_unpair p)) (snd (fin_unpair p)).
Proof.
  change (internal_subseteq n p) with (finpow_subseteq_fn n p).
  unfold finpow_subseteq_fn.
  (* Generalize the boolean first, so that destructing it rewrites the goal and the biconditional together. / 首先对布尔值进行泛化，以便在对其进行析构时，同时重写目标和双条件语句。 *)
  generalize (finpow_subseteq_iff n (fst (fin_unpair p))
                (snd (fin_unpair p))).
  destruct (finpow_subseteq (fst (fin_unpair p)) (snd (fin_unpair p)));
    intro Hiff.
  - split; [ intros _; exact (fst Hiff eq_refl) | intros _; reflexivity ].
  - split.
    + intro Hc; discriminate Hc.
    + intro Hle; discriminate (snd Hiff Hle).
Qed.

(* Non-vacuity: the internal test computes, and separates. / 非空性：内部测试进行计算并进行区分。 *)
Example internal_subseteq_true :
  internal_subseteq 2 (fin_pair sub2_10 sub2_11) = fin_true := eq_refl.

Example internal_subseteq_false :
  internal_subseteq 2 (fin_pair sub2_10 sub2_01) = fin_false := eq_refl.

(* ------------------------------------------------------------------------ *)
(* * ** (F) Example 118: apples and buckets, evaluated / * **（F）示例118：苹果和桶，评估 *)

(* Two apples in bucket 0, one apple in bucket 1. / 桶0里有两个苹果，桶1里有一个苹果。 *)
Definition apples : 3%nat ~{FinSet}~> 2%nat :=
  fun i => match i with
           | Fin.F1        => Fin.F1
           | Fin.FS Fin.F1 => Fin.F1
           | _             => Fin.FS Fin.F1
           end.

Example apples_at_0 : apples Fin.F1 = Fin.F1 := eq_refl.
Example apples_at_1 : apples (Fin.FS Fin.F1) = Fin.F1 := eq_refl.
Example apples_at_2 :
  apples (Fin.FS (Fin.FS Fin.F1)) = Fin.FS Fin.F1 := eq_refl.

(* The preimage on codes ALREADY EXISTS: it is [finpow_map], the arrow action of [FinPowerset]. Named, not rebuilt. / 代码上的原像已经存在：它是 [finpow_map]，[FinPowerset] 的箭头操作。已命名，未重建。 *)
Definition finpow_preimage {m n : nat} (f : Fin.t n → Fin.t m)
  (T : Fin.t (finpow m)) : Fin.t (finpow n) := finpow_map f T.

Example finpow_preimage_is_finpow_map {m n : nat}
  (f : Fin.t n → Fin.t m) (T : Fin.t (finpow m)) :
  finpow_preimage f T = finpow_map f T := eq_refl.

(*
 The direct image: bucket j is occupied when SOME apple in S lands in
 it. 

 --------
 直接映像：当集合 S 中的某个苹果落入桶 j 时，桶 j 被占用。
*)
Definition finpow_image {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow n)) : Fin.t (finpow m) :=
  fin_tabulate (fun j : Fin.t m =>
    fin_of_bool
      (fin_anyb n (fun i => andb (fin_eqb (f i) j) (finpow_mem S i)))).

(*
 The dual image: bucket j is occupied when EVERY apple landing in it is
 already in S.  The EVALUATIONS are this file's; the adjunction it
 satisfies is #384's and is not built here. 

 --------
 双重图像：当每一个落入桶 j 的苹果都已经在 S 中时，桶 j 被占用。评估是本文件的；它满足的附加关系是 #384 的，并非在此构建。
*)
Definition finpow_dual {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow n)) : Fin.t (finpow m) :=
  fin_tabulate (fun j : Fin.t m =>
    fin_of_bool
      (fin_allb n (fun i => implb (fin_eqb (f i) j) (finpow_mem S i)))).

Lemma finpow_image_mem {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow n)) (j : Fin.t m) :
  finpow_mem (finpow_image f S) j
    = fin_anyb n (fun i => andb (fin_eqb (f i) j) (finpow_mem S i)).
Proof.
  unfold finpow_mem, finpow_image.
  rewrite fin_apply_tabulate.
  apply finpow_mem_of_bool.
Qed.

Lemma finpow_dual_mem {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow n)) (j : Fin.t m) :
  finpow_mem (finpow_dual f S) j
    = fin_allb n (fun i => implb (fin_eqb (f i) j) (finpow_mem S i)).
Proof.
  unfold finpow_mem, finpow_dual.
  rewrite fin_apply_tabulate.
  apply finpow_mem_of_bool.
Qed.

(** ** The six evaluations / ** 六个评估 *)

(* The apples: {0} and {0,1} of the three. / 苹果：三颗中的 {0} 和 {0,1}。 *)
Definition apple0 : Fin.t (finpow 3) :=
  fin_tabulate (fun i => match i with
                         | Fin.F1 => fin_true
                         | _      => fin_false
                         end).
Definition apple01 : Fin.t (finpow 3) :=
  fin_tabulate (fun i => match i with
                         | Fin.F1        => fin_true
                         | Fin.FS Fin.F1 => fin_true
                         | _             => fin_false
                         end).

(* Two preimages: the buckets {0} and {1} pulled back to apples. / 两个原像：桶 {0} 和 {1} 被拉回到苹果。 *)
Example preimage_bucket0 :
  finpow_preimage apples sub2_10 = apple01 := eq_refl.

Example preimage_bucket1 :
  finpow_preimage apples sub2_01
    = fin_tabulate (fun i : Fin.t 3 =>
        match i with
        | Fin.F1        => fin_false
        | Fin.FS Fin.F1 => fin_false
        | _             => fin_true
        end) := eq_refl.

(* Two direct images. / 两张直接图像。 *)
Example image_apple0 : finpow_image apples apple0 = sub2_10 := eq_refl.
Example image_apple01 : finpow_image apples apple01 = sub2_10 := eq_refl.

(* Two dual images: at {0} the dual is EMPTY, because bucket 0 also holds apple 1, which is missing; at {0,1} it is {0}. This is where the dual image visibly differs from the direct image. / 两个对偶映像：在 {0}，对偶是空的，因为桶 0 也包含缺失的苹果 1；在 {0,1}，它是 {0}。这就是对偶映像明显不同于直接映像的地方。 *)
Example dual_apple0 : finpow_dual apples apple0 = sub2_00 := eq_refl.
Example dual_apple01 : finpow_dual apples apple01 = sub2_10 := eq_refl.

Example image_ne_dual_at_apple0 :
  finpow_image apples apple0 = finpow_dual apples apple0 → False.
Proof. intro H; discriminate H. Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Example 117, left half: the preimage has a left adjoint / * ** 示例117，左半部分：原像有一个左伴随 *)

Section FinGalois.

Context {m n : nat}.
Context (f : Fin.t n → Fin.t m).

Lemma finpow_image_mono (S T : Fin.t (finpow n)) :
  finpow_le S T → finpow_le (finpow_image f S) (finpow_image f T).
Proof.
  intros H j Hj.
  rewrite finpow_image_mem in Hj |- *.
  destruct (fin_anyb_exists n _ Hj) as [i Hi].
  apply Bool.andb_true_iff in Hi; destruct Hi as [Hfi HSi].
  refine (fin_exists_anyb n _ i _).
  apply Bool.andb_true_iff; split; [ exact Hfi | exact (H i HSi) ].
Qed.

Lemma finpow_preimage_mono (S T : Fin.t (finpow m)) :
  finpow_le S T → finpow_le (finpow_preimage f S) (finpow_preimage f T).
Proof.
  intros H i Hi.
  unfold finpow_preimage in *.
  rewrite finpow_map_mem in Hi |- *.
  exact (H (f i) Hi).
Qed.

Lemma finpow_image_transpose_to (S : Fin.t (finpow n))
  (T : Fin.t (finpow m)) :
  finpow_le (finpow_image f S) T → finpow_le S (finpow_preimage f T).
Proof.
  intros H i Hi.
  unfold finpow_preimage; rewrite finpow_map_mem.
  refine (H (f i) _).
  rewrite finpow_image_mem.
  refine (fin_exists_anyb n _ i _).
  apply Bool.andb_true_iff; split; [ apply fin_eqb_refl | exact Hi ].
Qed.

Lemma finpow_image_transpose_from (S : Fin.t (finpow n))
  (T : Fin.t (finpow m)) :
  finpow_le S (finpow_preimage f T) → finpow_le (finpow_image f S) T.
Proof.
  intros H j Hj.
  rewrite finpow_image_mem in Hj.
  destruct (fin_anyb_exists n _ Hj) as [i Hi].
  apply Bool.andb_true_iff in Hi; destruct Hi as [Hfi HSi].
  pose proof (H i HSi) as Hp.
  unfold finpow_preimage in Hp; rewrite finpow_map_mem in Hp.
  rewrite <- (fin_eqb_eq _ _ Hfi); exact Hp.
Qed.

Definition finpow_image_preimage_galois :
  GaloisConnection (@finpow_le n) (@finpow_le m) :=
  {| gal_l := finpow_image f
   ; gal_r := finpow_preimage f
   ; gal_mono_l := finpow_image_mono
   ; gal_mono_r := finpow_preimage_mono
   ; gal_to   := finpow_image_transpose_to
   ; gal_from := finpow_image_transpose_from |}.

Definition FinDirectImage@{u} : FinSubsets@{u} n ⟶ FinSubsets@{u} m :=
  GaloisFunctor_l (finpow_le_preorder n) (finpow_le_preorder m)
    finpow_image_preimage_galois.

Definition FinInverseImage@{u} : FinSubsets@{u} m ⟶ FinSubsets@{u} n :=
  GaloisFunctor_r (finpow_le_preorder n) (finpow_le_preorder m)
    finpow_image_preimage_galois.

Definition finpow_image_preimage_adjunction :
  FinDirectImage ⊣ FinInverseImage :=
  GaloisAdjunction (finpow_le_preorder n) (finpow_le_preorder m)
    finpow_image_preimage_galois.

End FinGalois.

Example fin_direct_image_obj (S : Fin.t (finpow 3)) :
  fobj[FinDirectImage apples] S = finpow_image apples S := eq_refl.

Example fin_inverse_image_obj (T : Fin.t (finpow 2)) :
  fobj[FinInverseImage apples] T = finpow_map apples T := eq_refl.
