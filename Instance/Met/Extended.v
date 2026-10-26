Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.micromega.Lra.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Met.

Generalizable All Variables.

Open Scope R_scope.

(** * Extended metric spaces / * 扩展度量空间 *)

(*
 nLab:      https://ncatlab.org/nlab/show/extended+metric+space
 nLab:      https://ncatlab.org/nlab/show/Lawvere+metric+space
 Wikipedia: https://en.wikipedia.org/wiki/Metric_space#Extended_metrics
 Book:      Fong & Spivak, “Seven Sketches in Compositionality”,
 §2.3.3, the variant introduced immediately after
 Definition 2.51, printed pp. 59-60 (PDF pp. 71-72)
 Paper:     Lawvere, “Metric spaces, generalized logic, and closed
 categories”, Rend. Sem. Mat. Fis. Milano 43, 1973

 ON THE CITATIONS.  No book was opened for this file; the description of
 what Seven Sketches says is a paraphrase, taken from issue #308's own
 summary of §2.3.3 and from doc/plan/books/seven-sketches/pagemap.md (which
 places §2.3.3, “Lawvere metric spaces”, at printed p. 59).  A reader
 checking this file against the printed book should expect the wording to
 differ.

 Seven Sketches gives Definition 2.51 (Instance/Met.v's [MetricSpace]) and
 then, immediately after it, the variant in which the distance is allowed
 the value ∞.  The variant is not an aside for that book: its whole
 enrichment story runs through the quantale Cost = [0,∞], whose monoidal
 unit is 0 and whose top element ∞ is absorbing for the tensor (addition).
 A Cost-enriched category can therefore record “there is no way from a to
 b” as the hom-object ∞, and without that value the enriched reading has
 nothing to say about spaces that fall into separate pieces.  What is
 asserted here is only that ∞ is needed for the structure to exist; NO
 enriched-category statement is proved in this file, and the identification
 of Cost-categories with extended metric spaces is not formalized anywhere
 in this tree.

 This file supplies the structure and the comparison the book's remark
 needs: [ExtMetricSpace], and the identification of ordinary metric spaces
 among the extended ones as EXACTLY those whose distances are all finite,
 in both directions with the round trips measured.

 SCOPE.  What is NOT here, deliberately: the Lawvere/[Cost]-enriched
 presentation.  Instance/Met.v's header explains the decision at length —
 Lawvere metric spaces drop symmetry and separation, which both records in
 this development keep, so they are a genuinely different structure, and
 no comparison functor between this file's [ExtMetricSpace] and any
 [Enriched] instance is built or claimed.  What this file does is name the
 structure the book's remark is about; connecting it to enrichment is a
 separate piece of work.  Also not here: a category of extended metric
 spaces.  The arrows would be the distance-preserving maps again, and
 nothing in Mac Lane §III.1 or in the issue asks for it; [Met] is
 Instance/Met.v's and is the category the completion lives in.

 [∞] IS AN INDUCTIVE CONSTRUCTOR, not a real number, so [Rinf] below has
 decidable “is it infinite” by construction ([Rinf_finite_dec]) and the
 two presentations of finiteness — a distance that is not ∞, and a
 distance that IS some real — coincide constructively
 ([EFinite_iff_not_infinite]).  Nothing in this file needs the reals to be
 complete, so its constants carry at most the two standard-library real
 axioms and never [sig_not_dec]; contrast Instance/Met/Completion.v. 

 --------
 nLab:       https://ncatlab.org/nlab/show/extended+metric+space 
 nLab:       https://ncatlab.org/nlab/show/Lawvere+metric+space 
 维基百科:  https://en.wikipedia.org/wiki/Metric_space#Extended_metrics 
 书籍:      Fong & Spivak, 《组合性中的七个草图》, 
 §2.3.3, 在定义 2.51 之后立即引入的变体, 打印页 59-60 (PDF 页 71-72)
 论文:     Lawvere, 《度量空间、广义逻辑与闭类目》, Rend. Sem. Mat. Fis. Milano 43, 1973

 关于引用。本文件未翻开书籍；对《七个草图》的内容描述是意译，摘自 issue #308 对 §2.3.3 的总结以及 doc/plan/books/seven-sketches/pagemap.md（该文件将 §2.3.3 “Lawvere 度量空间” 标注在打印页 59）。读者在对照印刷版书籍查看本文件时，应预计措辞会有所不同。《Seven Sketches》给出了定义 2.51（实例/Met.v 的 [MetricSpace]），然后紧接着给出了一个变体，其中允许距离的值为 ∞。这个变体在那本书中并不是一个附录：它的整个丰富化故事都在量化结构 Cost = [0,∞] 中进行，其单元元为 0，且其最大元素 ∞ 对张量（加法）具有吸收性。因此，一个 Cost-丰富类别可以将“从 a 到 b 没有途径”记录为同态对象 ∞，没有这个值，丰富化的读法对落入不同部分的空间毫无说明。这里断言的只是 ∞ 对结构的存在是必要的；这个文件中并未证明任何丰富类别的陈述，并且在此树中也没有将 Cost-类别与扩展度量空间的对应关系形式化的地方。此文件提供了该书评论所需的结构和比较：[ExtMetricSpace]，以及在扩展度量空间中识别普通度量空间，恰好是那些距离均为有限的空间，同时考虑双向及往返测量。范围。这里故意没有包括的内容：Lawvere/[Cost] 丰富化的表述。Instance/Met.v 的头注详细解释了这个决定——Lawvere 度量空间放弃了对称性和分离性，而本开发中的记录都保留了这两者，因此它们是完全不同的结构，并且没有构建或声称存在将本文件的 [ExtMetricSpace] 与任何 [Enriched] 实例进行比较的函子。本文件所做的是为书中评论所涉及的结构命名；将其与丰富化联系起来是另一项工作。同样没有包括在内的还有：扩展度量空间的范畴。箭头将再次是保距映射，而 Mac Lane §III.1 或相关问题中并没有要求这样做；[Met] 是 Instance/Met.v 的，并且是完备化所在的范畴。[∞] 是一个归纳构造器，而不是真实数，因此下面的 [Rinf] 通过构造具有可判定的“是否为无限”([Rinf_finite_dec])，并且有限性的两种表示——一个不是 ∞ 的距离，以及一个是某个实数的距离——在构造上是一致的([EFinite_iff_not_infinite])。这个文件中没有内容需要实数是完备的，因此它的常量至多包含两个标准库的实数公理，从不包含 [sig_not_dec]；参见 Instance/Met/Completion.v 对比。
*)

(** ** The value type [0, ∞] / ** 值类型 [0, ∞] *)

(*
 The non-negativity of [0,∞] is not imposed on the carrier: exactly as in
 Instance/Met.v, the four axioms DERIVE it ([edist_nonneg] below).  So
 [Rinf] is the reals with a point at infinity adjoined, and the metric
 axioms cut it down. 

 --------
 [0,∞] 的非负性并没有强加给载体：正如在 Instance/Met.v 中一样，四个公理推导出了它（下面的 [edist_nonneg]）。所以 [Rinf] 是在实数集合上加上一个无穷点，并且度量公理将其限制。
*)
Inductive Rinf : Type :=
  | RFin : R → Rinf
  | RInf : Rinf.

Definition Rinf_zero : Rinf := RFin 0.

Definition Rinf_plus (a b : Rinf) : Rinf :=
  match a, b with
  | RFin x, RFin y => RFin (x + y)
  | _, _ => RInf
  end.

Definition Rinf_le (a b : Rinf) : Prop :=
  match a, b with
  | RFin x, RFin y => x <= y
  | RFin _, RInf => True
  | RInf, RFin _ => False
  | RInf, RInf => True
  end.

Lemma RFin_inj (x y : R) : RFin x = RFin y → x = y.
Proof. intro H; now inversion H. Qed.

Lemma RFin_neq_RInf (x : R) : RFin x <> RInf.
Proof. discriminate. Qed.

(* Whether a value is infinite is decided by looking at the constructor. / 一个值是否是无限的取决于查看其构造函数。 *)
Definition Rinf_finite_dec (a : Rinf) : ((∃ r : R, a = RFin r) + (a = RInf))%type :=
  match a as z return ((∃ r : R, z = RFin r) + (z = RInf))%type with
  | RFin r => inl (r; eq_refl)
  | RInf   => inr eq_refl
  end.

Lemma Rinf_le_refl (a : Rinf) : Rinf_le a a.
Proof. destruct a; simpl; [ apply Rle_refl | exact I ]. Qed.

Lemma Rinf_le_trans (a b c : Rinf) : Rinf_le a b → Rinf_le b c → Rinf_le a c.
Proof.
  destruct a, b, c; simpl; intros H1 H2;
    solve [ exact I | contradiction | lra ].
Qed.

(*
 [RInf] is the top and absorbs addition — the two facts the triangle
 inequality below is argued with.  The two absorption laws are NOT equally
 strict, and the asymmetry is the match order rather than anything
 mathematical: [Rinf_plus] scrutinises its first argument first, so the
 left law closes by [reflexivity] and the right one needs a case split. 

 --------
 [RInf] 是顶元素并吸收加法 —— 以下讨论的三角不等式就是基于这两个事实。两个吸收律并非同样严格，其不对称性在于匹配顺序，而不是数学上的原因：[Rinf_plus] 先检查它的第一个参数，因此左侧律由 [reflexivity] 闭合，而右侧律则需要分情况讨论。
*)
Lemma Rinf_le_RInf (a : Rinf) : Rinf_le a RInf.
Proof. destruct a; exact I. Qed.

Lemma Rinf_plus_RInf_l (b : Rinf) : Rinf_plus RInf b = RInf.
Proof. reflexivity. Qed.

Lemma Rinf_plus_RInf_r (a : Rinf) : Rinf_plus a RInf = RInf.
Proof. now destruct a. Qed.

(* * ** The four axioms, with distance in [0, ∞] / * ** 四个公理，与 [0, ∞] 中的距离 *)

(*
 Fong & Spivak's Definition 2.51 verbatim, with [R] replaced by [Rinf] and
 [<=] by [Rinf_le].  The clause-for-clause correspondence with
 Instance/Met.v's [MetricSpace] is exact: the same four conditions, the
 same setoid bookkeeping field. 

 --------
 Fong & Spivak 的定义 2.51 原文照抄，其中 [R] 被替换为 [Rinf]，[<=] 被替换为 [Rinf_le]。与 Instance/Met.v 的 [MetricSpace] 逐条对应完全一致：相同的四个条件，相同的等价类簿记字段。
*)
Record ExtMetricSpace := {
  emet_carrier :> SetoidObject;

  edist : emet_carrier → emet_carrier → Rinf;

  edist_proper : ∀ x x' y y', x ≈ x' → y ≈ y' → edist x y = edist x' y';
  edist_refl : ∀ x, edist x x = Rinf_zero;
  edist_separates : ∀ x y, edist x y = Rinf_zero → x ≈ y;
  edist_sym : ∀ x y, edist x y = edist y x;
  edist_triangle : ∀ x y z, Rinf_le (edist x z) (Rinf_plus (edist x y) (edist y z))
}.

Arguments edist {X} _ _ : rename.
Arguments edist_proper {X} _ _ _ _ _ _ : rename.
Arguments edist_refl {X} _ : rename.
Arguments edist_separates {X} _ _ _ : rename.
Arguments edist_sym {X} _ _ : rename.
Arguments edist_triangle {X} _ _ _ : rename.

(* Non-negativity is derived, as in the ordinary case, and it has an extra clause here: an infinite distance is vacuously non-negative. / 非负性是推导出来的，就像在普通情况下那样，并且这里有一个额外的条款：无限距离在逻辑上是非负的。 *)
Lemma edist_nonneg {E : ExtMetricSpace} (x y : E) (r : R) :
  edist x y = RFin r → 0 <= r.
Proof.
  intro Hr.
  pose proof (edist_triangle x y x) as H.
  rewrite (edist_refl x), (edist_sym y x) in H.
  rewrite Hr in H; simpl in H.
  unfold Rinf_zero in H; simpl in H.
  lra.
Qed.

(* * ** Finiteness, and the identification with ordinary metric spaces / * ** 有限性，以及与普通度量空间的对应 *)

(*
 “All distances are finite”.  Stated as data (this library's `∃` is
 [sigT]) so the real value may be read off without a choice principle;
 [EFinite_iff_not_infinite] shows the Prop-shaped alternative is
 equivalent, the case analysis on the constructor doing all the work. 

 --------
 “所有距离都是有限的”。作为数据陈述（这个库的 `∃` 是 [sigT]），因此可以在不使用选择原则的情况下读取真实值；[EFinite_iff_not_infinite] 显示 Prop 型的替代方案是等价的，构造函数上的情况分析完成了所有工作。
*)
Definition EFinite (E : ExtMetricSpace) : Type :=
  ∀ x y : E, ∃ r : R, edist x y = RFin r.

Lemma EFinite_iff_not_infinite (E : ExtMetricSpace) :
  EFinite E ↔ (∀ x y : E, edist x y = RInf → False).
Proof.
  split.
  - intros Hfin x y Hinf.
    destruct (Hfin x y) as [r Hr].
    rewrite Hinf in Hr; discriminate.
  - intros Hnot x y.
    destruct (Rinf_finite_dec (edist x y)) as [[r Hr] | Hinf].
    + exact (r; Hr).
    + now destruct (Hnot x y Hinf).
Qed.

(* * *** Every metric space is an extended metric space / * *** 每个度量空间都是拓展的度量空间 *)

Section OfMetric.

Local Set Default Proof Using "All".

Context (X : MetricSpace).

Definition emet_of_dist (x y : X) : Rinf := RFin (dist x y).

Lemma emet_of_proper : ∀ x x' y y', x ≈ x' → y ≈ y' →
  emet_of_dist x y = emet_of_dist x' y'.
Proof.
  intros a b c d Hab Hcd; unfold emet_of_dist.
  now rewrite (dist_proper a b c d Hab Hcd).
Qed.

Lemma emet_of_refl : ∀ x, emet_of_dist x x = Rinf_zero.
Proof. intro a; unfold emet_of_dist, Rinf_zero; now rewrite dist_refl. Qed.

Lemma emet_of_separates : ∀ x y, emet_of_dist x y = Rinf_zero → x ≈ y.
Proof.
  intros a b H; unfold emet_of_dist, Rinf_zero in H.
  now apply dist_separates, RFin_inj.
Qed.

Lemma emet_of_sym : ∀ x y, emet_of_dist x y = emet_of_dist y x.
Proof. intros a b; unfold emet_of_dist; now rewrite dist_sym. Qed.

Lemma emet_of_triangle : ∀ x y z,
  Rinf_le (emet_of_dist x z) (Rinf_plus (emet_of_dist x y) (emet_of_dist y z)).
Proof. intros a b c; simpl; apply dist_triangle. Qed.

Definition ExtMetric_of_Metric : ExtMetricSpace :=
  {| emet_carrier    := met_carrier X;
     edist           := emet_of_dist;
     edist_proper    := emet_of_proper;
     edist_refl      := emet_of_refl;
     edist_separates := emet_of_separates;
     edist_sym       := emet_of_sym;
     edist_triangle  := emet_of_triangle |}.

(* ... and it is finite, with the real value read off on the nose. / ... 它是有限的，实值可以直接读取。 *)
Definition ExtMetric_of_Metric_EFinite : EFinite ExtMetric_of_Metric :=
  fun x y => (dist x y; eq_refl).

End OfMetric.

Arguments ExtMetric_of_Metric X : clear implicits.
Arguments ExtMetric_of_Metric_EFinite X : clear implicits.

(* * *** Every finite extended metric space is a metric space / * *** 每个有限的扩展度量空间都是一个度量空间 *)

Section OfExtended.

Local Set Default Proof Using "All".

Context (E : ExtMetricSpace).
Context (Hfin : EFinite E).

Definition efin (x y : E) : R := `1 (Hfin x y).

Lemma efin_spec (x y : E) : edist x y = RFin (efin x y).
Proof. exact (`2 (Hfin x y)). Qed.

(* Every clause transfers by pushing [efin_spec] through the constructor and using its injectivity; no new mathematics happens here. / 每个条款通过将 [efin_spec] 推入构造函数并利用其单射性来传递；这里没有发生新的数学内容。 *)
Lemma efin_proper : ∀ x x' y y', x ≈ x' → y ≈ y' → efin x y = efin x' y'.
Proof.
  intros a b c d Hab Hcd.
  apply RFin_inj.
  rewrite <- 2 efin_spec.
  now apply edist_proper.
Qed.

Lemma efin_refl : ∀ x, efin x x = 0.
Proof.
  intro a; apply RFin_inj.
  rewrite <- efin_spec.
  exact (edist_refl a).
Qed.

Lemma efin_separates : ∀ x y, efin x y = 0 → x ≈ y.
Proof.
  intros a b H.
  apply edist_separates.
  rewrite efin_spec, H; reflexivity.
Qed.

Lemma efin_sym : ∀ x y, efin x y = efin y x.
Proof.
  intros a b; apply RFin_inj.
  rewrite <- 2 efin_spec.
  apply edist_sym.
Qed.

Lemma efin_triangle : ∀ x y z, efin x z <= efin x y + efin y z.
Proof.
  intros a b c.
  pose proof (edist_triangle a b c) as H.
  rewrite (efin_spec a c), (efin_spec a b), (efin_spec b c) in H.
  exact H.
Qed.

Definition Metric_of_EFinite : MetricSpace :=
  {| met_carrier    := emet_carrier E;
     dist           := efin;
     dist_proper    := efin_proper;
     dist_refl      := efin_refl;
     dist_separates := efin_separates;
     dist_sym       := efin_sym;
     dist_triangle  := efin_triangle |}.

End OfExtended.

Arguments Metric_of_EFinite E Hfin : clear implicits.

(* * ** The two passages are mutually inverse / * ** 这两个段落是相互逆的 *)

(*
 THE STRICT DIRECTION.  Starting from a metric space, going up to the
 extended world and back down along the canonical finiteness witness
 returns the distance ON THE NOSE — [eq_refl], not merely `≈` — because
 [ExtMetric_of_Metric_EFinite] hands back [dist x y] itself and [efin] is
 its first projection.  The carrier is likewise unchanged definitionally.
 These are convertibility statements, the exception this library allows
 itself; they say nothing about `≈`. 

 --------
 严格方向。从一个度量空间出发，上升到扩展世界，然后沿着典型的有限性证据回到原处，会准确返回距离——[eq_refl]，而不仅仅是`≈`——因为[ExtMetric_of_Metric_EFinite]本身返回[dist x y]，而[efin]是它的第一个投影。载体在定义上同样保持不变。这些是可转换性声明，这是这个库允许自己的例外；它们并不涉及`≈`。
*)
Example Metric_EFinite_roundtrip_carrier (X : MetricSpace) :
  met_carrier (Metric_of_EFinite (ExtMetric_of_Metric X)
                                 (ExtMetric_of_Metric_EFinite X))
    = met_carrier X := eq_refl.

Example Metric_EFinite_roundtrip_dist (X : MetricSpace) (x y : X) :
  dist (X := Metric_of_EFinite (ExtMetric_of_Metric X)
                               (ExtMetric_of_Metric_EFinite X)) x y
    = dist x y := eq_refl.

(*
 THE OTHER DIRECTION IS NOT STRICT, and the reason is worth being precise
 about: [Hfin] is an arbitrary witness, so [RFin (efin x y)] is
 [RFin (`1 (Hfin x y))] and reducing it to [edist x y] needs [`2 (Hfin x
 y)], a proof, not a conversion.  It holds up to [=] and is proved here;
 the corresponding [eq_refl] is pinned as a rejection probe in
 Test/ProbeMet.v, which is where this development's rejection vernacular
 is confined. 

 --------
 另一种方向不是严格的，其原因值得精确说明：[Hfin] 是一个任意的证据，因此 [RFin (efin x y)] 是 [RFin (`1 (Hfin x y))]，并且将其简化为 [edist x y] 需要 [`2 (Hfin x y)]，这是一个证明，而不是一个转换。它在 [=] 上成立，并在此处证明；相应的 [eq_refl] 被固定为 Test/ProbeMet.v 中的拒绝探针，这是此开发的拒绝术语所局限的地方。
*)
Lemma ExtMetric_of_Metric_roundtrip (E : ExtMetricSpace) (Hfin : EFinite E)
      (x y : E) :
  edist (X := ExtMetric_of_Metric (Metric_of_EFinite E Hfin)) x y = edist x y.
Proof. symmetry; exact (efin_spec E Hfin x y). Qed.

(*
 THE IDENTIFICATION Fong & Spivak's remark asks for.

 The comparison is between structures ON ONE CARRIER, which is how the
 book states it and is what makes it content-bearing: an extended metric
 space carries an ordinary metric structure on its own points exactly when
 none of its distances is ∞.  The carrier is deliberately NOT
 existentially quantified — comparing two records with different carriers
 would require transporting along an equality of setoids, which carries no
 mathematical content here and would obscure the statement.

 Note also where the constructive strength sits.  [EFinite] is POINTWISE
 (“for each pair there is a real”) while [MetricPresentation] is GLOBAL
 (“there is a distance function”), and passing from the first to the
 second is exactly a choice step — free here only because this library's
 `∃` is [sigT], so the witness was data all along.  Over a Prop-valued
 existential this direction would be the axiom of choice. 

 --------
 Fong & Spivak 提到的识别。

 比较是在同一个承载体上的结构之间进行的，这也是书中所述的方式，并且正因为如此它才具有承载内容的特性：一个扩展度量空间在其自身的点上承载普通的度量结构，正当且仅当它的所有距离都不是 ∞。承载体特意没有进行存在量化——比较两个具有不同承载体的记录将需要沿着集合同构的等式进行转换，这在这里不承载任何数学内容，并且会模糊该陈述。还要注意构造性强度所在的位置。[EFinite] 是逐点的（“对于每一对都有一个实数”），而 [MetricPresentation] 是全局的（“存在一个距离函数”），从前者到后者的转换恰好是选择步骤——在这里是自由的，仅因为该库的 `∃` 是 [sigT]，所以见证一直是数据。在基于 Prop 值的存在量词上，这个方向将是选择公理。
*)
Definition MetricPresentation (E : ExtMetricSpace) : Type :=
  ∃ d : E → E → R, ∀ x y : E, edist x y = RFin (d x y).

Theorem metric_iff_finite_extended (E : ExtMetricSpace) :
  EFinite E ↔ MetricPresentation E.
Proof.
  split.
  - intro Hfin.
    exact (efin E Hfin; efin_spec E Hfin).
  - intros [d Hd] x y.
    exact (d x y; Hd x y).
Qed.

(* A presentation is a metric space on the same carrier — the upgrade from the bare distance function to a [MetricSpace] record. / 一个表示是在相同载体上的度量空间——从单纯的距离函数升级到 [MetricSpace] 记录。 *)
Definition Metric_of_presentation (E : ExtMetricSpace)
           (P : MetricPresentation E) : MetricSpace :=
  Metric_of_EFinite E (snd (metric_iff_finite_extended E) P).

(* Read the other way: the extended metric spaces arising from ordinary ones are exactly the finite ones. / 反过来看：由普通度量空间产生的扩展度量空间恰好是有限的。 *)
Definition EFinite_of_Metric (X : MetricSpace) :
  EFinite (ExtMetric_of_Metric X) := ExtMetric_of_Metric_EFinite X.

(* * ** Non-vacuity: an extended metric space that is not a metric space / * ** 非空性：一个扩展的度量空间，而不是度量空间 *)

(*
 Two points at infinite distance.  This is the smallest space the ordinary
 definition cannot express, and it is exactly the situation Seven Sketches
 wants ∞ for: a space in two pieces.  Every clause is a two-way case
 analysis on booleans. 

 --------
 两个在无限远的点。这是普通定义无法表达的最小空间，它正是《七个素描》中所需要用 ∞ 表示的情况：一个由两部分组成的空间。每个子句都是关于布尔值的双向情况分析。
*)

Definition bool_setoid_object : SetoidObject :=
  {| carrier := bool; is_setoid := {| equiv := @eq bool |} |}.

Definition two_far_dist (x y : bool) : Rinf :=
  if Bool.eqb x y then RFin 0 else RInf.

Lemma two_far_proper : ∀ x x' y y' : bool_setoid_object,
  x ≈ x' → y ≈ y' → two_far_dist x y = two_far_dist x' y'.
Proof. intros a b c d Hab Hcd; simpl in *; now subst. Qed.

Lemma two_far_refl : ∀ x : bool_setoid_object, two_far_dist x x = Rinf_zero.
Proof. intro a; now destruct a. Qed.

Lemma two_far_separates : ∀ x y : bool_setoid_object,
  two_far_dist x y = Rinf_zero → x ≈ y.
Proof.
  intros a b H; destruct a, b; simpl in *;
    solve [ reflexivity | discriminate ].
Qed.

Lemma two_far_sym : ∀ x y : bool_setoid_object,
  two_far_dist x y = two_far_dist y x.
Proof. intros a b; now destruct a, b. Qed.

Lemma two_far_triangle : ∀ x y z : bool_setoid_object,
  Rinf_le (two_far_dist x z) (Rinf_plus (two_far_dist x y) (two_far_dist y z)).
Proof.
  intros a b c; destruct a, b, c; simpl;
    solve [ exact I | apply Rle_refl | lra ].
Qed.

Definition TwoFar : ExtMetricSpace :=
  {| emet_carrier    := bool_setoid_object;
     edist           := two_far_dist;
     edist_proper    := two_far_proper;
     edist_refl      := two_far_refl;
     edist_separates := two_far_separates;
     edist_sym       := two_far_sym;
     edist_triangle  := two_far_triangle |}.

Example TwoFar_infinite : edist (X := TwoFar) true false = RInf := eq_refl.

(*
 So the inclusion of metric spaces into extended ones is PROPER: [TwoFar]
 is an extended metric space that no ordinary metric space presents. 

 --------
 因此，将度量空间包含到扩展空间中是适当的：[TwoFar] 是一个普通度量空间无法呈现的扩展度量空间。
*)
Theorem TwoFar_not_EFinite : EFinite TwoFar → False.
Proof.
  intro Hfin.
  exact (fst (EFinite_iff_not_infinite TwoFar) Hfin true false eq_refl).
Qed.

Corollary TwoFar_not_a_metric_space : MetricPresentation TwoFar → False.
Proof.
  intro H.
  exact (TwoFar_not_EFinite (snd (metric_iff_finite_extended TwoFar) H)).
Qed.
