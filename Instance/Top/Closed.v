Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Top.

Generalizable All Variables.

(* * * Closed sets, and the complementation duality / * * 闭集与补集对偶性 *)

(*
 Book:      Riehl, “Category Theory in Context”, Example 1.3.14(iv) and
 Example 1.4.4(v)
 nLab:      https://ncatlab.org/nlab/show/closed+subset
 nLab:      https://ncatlab.org/nlab/show/frame
 Wikipedia: https://en.wikipedia.org/wiki/Closed_set

 Riehl's Example 1.3.14(iv) reads the poset of open subsets of a space as
 a category — a thin category, one arrow `U ~> V` exactly when `U ⊆ V` —
 and Example 1.4.4(v) observes that complementation is an isomorphism
 between that category and the OPPOSITE of the poset of closed subsets:
 taking complements reverses inclusions.  This file supplies both, plus
 the functorial form: the opens of a space are contravariantly functorial
 in the space (preimage), the closed sets likewise, and complementation
 is a natural isomorphism between the two presheaves on [Top].

 Opens X          thin category of the opens of X, ordered by ⊆
 Closeds X        thin category of the closed sets of X
 Opens X ≅ (Closeds X)^op            complementation, objectwise
 OpensF, ClosedsF : Top^op ⟶ Sets    preimage presheaves
 OpensF ≅ ClosedsF                   complementation, naturally 

 --------
 书籍：Riehl，《语境中的范畴论》，例子 1.3.14(iv) 及 例子 1.4.4(v)
 nLab：https://ncatlab.org/nlab/show/closed+subset
 nLab：https://ncatlab.org/nlab/show/frame
 维基百科：https://en.wikipedia.org/wiki/Closed_set

 Riehl 的例子 1.3.14(iv) 将空间的开子集的偏序集视为一个范畴——一个薄范畴，恰有一条箭头 `U ~> V` 当且仅当 `U ⊆ V` ——而例子 1.4.4(v) 则观察到补集是该范畴与闭子集偏序集的对偶范畴之间的一个同构：取补集会反转包含关系。该文件提供了两者，以及函子形式：空间的开集在空间变换下是逆变函子（原像），闭集同样如此，而补集是两个关于 [Top] 的预层之间的自然同构。X 的开集          X 的开集的薄范畴，按 ⊆ 排序
 闭集 X        X 的闭集的薄范畴
 X 的开集 ≅ (X 的闭集)^op      补集，对象上
 OpensF, ClosedsF : Top^op ⟶ Sets    原像预层
 OpensF ≅ ClosedsF                 补集，自然地
*)

(*
 Design: closed sets constructively, and why the order is what it is

 nLab: https://ncatlab.org/nlab/show/excluded+middle
 nLab: https://ncatlab.org/nlab/show/double+negation

 Two decisions here need stating plainly, because in both cases the
 classical formulation would silently import excluded middle.

 1. A CLOSED SET CARRIES ITS COMPLEMENTING OPEN AS DATA.  Classically one
 says “C is closed when its complement is open”, and extracts the open
 from the existential when needed.  Constructively that extraction is
 an appeal to choice (from `∃ U, IsOpen U ∧ ...` one cannot in general
 produce `U`), so [ClosedSet] below bundles the complementing open as
 a field, with [closed_agree] recording that the closed predicate IS
 the negation of that open.  The record is therefore not “a predicate
 that happens to be closed” but “a predicate together with a witness
 of its closedness” — the same move the library makes wherever a
 classical existential would otherwise need choice, as with the chosen
 pullbacks of Theory/Subobject/Functor.v or the chosen lifts of
 Theory/Fibration.v's [Cleaving].

 2. THE ORDER IS REVERSE INCLUSION OF THE COMPLEMENTING OPENS, AND THE
 SETOID IS THEIR MUTUAL INCLUSION.  Complementation turns inclusion of
 opens into inclusion of closed predicates constructively: from
 `U ⊆ U'` one gets `¬U' ⊆ ¬U` by composition.  The converse does NOT
 hold — recovering `U ⊆ U'` from `¬U' ⊆ ¬U` needs `¬¬`-stability, i.e.
 excluded middle — so ordering closed sets by inclusion of their
 closed predicates would break the duality in one direction.  Ordering
 them by reverse inclusion of the complementing opens keeps the
 duality exact, implies inclusion of the closed predicates (lemma
 [closed_order_implies_inclusion]), and agrees with it classically.

 The same reasoning fixes the setoid: two closed sets are identified
 when their complementing OPENS agree pointwise.  That implies their
 closed predicates agree ([closed_equiv_implies_pred_equiv]) but is
 not implied by it, for the same `¬¬` reason.  Comparing the closed
 predicates instead would make [closed_interior] — “read off the
 complementing open” — not respect `≈`, and the natural isomorphism
 at the end of this file would have no inverse.  Riehl's statement is
 classical; what is proved below is its constructive rendering, and
 this paragraph is the disclosure of the difference.

 The disclosure has a CONSEQUENCE that must be stated just as
 plainly (the audit of the first commit insisted, correctly): with
 this setoid, [ClosedSets X] is [OpenSets X] carrying an extra field
 the equivalence never inspects, both round trips of the duality
 copy the compared component verbatim, and the natural isomorphism
 at the end of the file is, extensionally, the identity dressed as
 complementation.  The constructive CONTENT of the duality therefore
 lives in the one-directional lemmas
 ([closed_order_implies_inclusion], [closed_equiv_implies_pred_equiv])
 and in the closing section, which prices the classical reading
 exactly: a predicate-comparing setoid is EQUIVALENT to
 double-negation elimination ([pred_comparison_forces_DNE]), and
 under that explicit hypothesis the two-sided classical
 correspondence is recovered
 ([closed_inclusion_implies_order_classical],
 [closed_pred_equiv_implies_equiv_classical]). 

 --------
 设计：闭合集的构造性以及顺序为何如此

 nLab: https://ncatlab.org/nlab/show/excluded+middle
 nLab: https://ncatlab.org/nlab/show/double+negation

 这里需要明确说明两个决策，因为在这两种情况下，经典表述会默默地引入排中律。1. 闭集携带其补集的开集作为数据。经典上有人说“当其补集是开集时，C 是闭的”，并在需要时从存在性中提取开集。在构造方法中，这种提取是一种对选择的诉求（根据 `∃ U, IsOpen U ∧ ...`，一般无法产生 `U`），因此下面的 [ClosedSet] 将补集开集作为一个字段捆绑起来，同时 [closed_agree] 记录闭谓词确实是该开集的否定。因此，该记录不是“恰好为闭的谓词”，而是“一个谓词连同其闭性的证明”——这是库在任何经典存在性本应需要选择的地方使用的相同方法，例如 Theory/Subobject/Functor.v 的选定拉回或 Theory/Fibration.v 的 [Cleaving] 的选定提升。2. 顺序是互补开集的逆向包含，而集合同构是它们的相互包含。补集将开集的包含转化为闭谓词的包含（构造性地）：从 `U ⊆ U'` 可以通过组合得到 `¬U' ⊆ ¬U`。反之则不成立——从 `¬U' ⊆ ¬U` 恢复 `U ⊆ U'` 需要 `¬¬` 稳定性，即排中律——因此按闭集合的闭谓词包含排序会在一个方向上破坏对偶性。按互补开集的逆向包含排序可以保持对偶性精确，意味着闭谓词的包含（引理 [closed_order_implies_inclusion]），并且在经典意义下与其一致。相同的推理确定了集合等价关系：当两个闭集的补集开集在每一点上都相同时，它们被认为是相同的。这意味着它们的闭谓词一致（[closed_equiv_implies_pred_equiv]），但并不由此推得，原因与`¬¬`相同。相反，如果比较闭谓词，会使[closed_interior]——“读取补集的开集”——不尊重`≈`，并且本文件末尾的自然同构将没有逆。Riehl 的表述是经典的；下面证明的是其构造性呈现，并且这一段揭示了它们之间的差异。披露有一个必须同样明确说明的后果（对第一次提交的审计正确地坚持了这一点）：使用这个集合，[ClosedSets X] 是携带额外字段的 [OpenSets X]，但等价关系从不检查该字段，双重复制的两个往返都会逐字复制比较的组件，并且文件末尾的自然同构，本质上是作为补集装扮的恒等式。因此，二元性的建设性内容存在于单向引理（[closed_order_implies_inclusion]，[closed_equiv_implies_pred_equiv]）中，以及在结束部分，它准确地估价了经典解读：一个谓词比较的集合是等价于双重否定消去（[pred_comparison_forces_DNE]），并且在该明确假设下，可以恢复双侧的经典对应关系（[closed_inclusion_implies_order_classical]，[closed_pred_equiv_implies_equiv_classical]）。
*)

(* * ** Opens and closed sets of a space / * ** 空间的开集与闭集 *)

(* An open of X, as an object: the predicate together with its openness. / X 的开放，作为一个对象：谓词及其开放性。 *)
Definition OpenSet (X : TopSpace) : Type := { U : X → Type & IsOpen X U }.

(* A closed set of X: the closed predicate, its complementing open (as data, per design note 1), and the agreement between the two. / X 的闭合集：闭合谓词，它的补集开放（作为数据，根据设计说明 1），以及两者之间的一致性。 *)
Record ClosedSet (X : TopSpace) := {
  closed_pred : X → Type;                       (* the closed predicate / 封闭谓词 *)
  closed_compl : X → Type;                      (* its complementing open / 它正在补充开放 *)
  closed_compl_open : IsOpen X closed_compl;    (* which is indeed open / 这确实是开放的 *)

  (* the closed predicate is the negation of the complementing open / 封闭谓词是否定的补充开放谓词 *)
  closed_agree : ∀ x : X, closed_pred x ↔ ¬ (closed_compl x)
}.

Arguments closed_pred {X} _ _.
Arguments closed_compl {X} _ _.
Arguments closed_compl_open {X} _.
Arguments closed_agree {X} _ _.

(*
 Complementation, object by object.  An open becomes the closed set whose
 predicate is its negation and whose complementing open is the open
 itself; the agreement field is then the identity equivalence. 

 --------
 互补，逐个对象。一个开集变为闭集，其谓词是它的否定，且其互补的开集是开集本身；一致性域随后是恒等等价关系。
*)
Definition open_complement {X : TopSpace} (U : OpenSet X) : ClosedSet X := {|
  closed_pred       := fun x => ¬ (`1 U x);
  closed_compl      := `1 U;
  closed_compl_open := `2 U;
  closed_agree      := fun x => (fun h => h, fun h => h)
|}.

(* ... and back: a closed set already carries its complementing open. / ……反之亦然：一个闭集本身已经包含了它的互补开集。 *)
Definition closed_interior {X : TopSpace} (C : ClosedSet X) : OpenSet X :=
  (closed_compl C; closed_compl_open C).

(*
 The chosen order on closed sets implies inclusion of the closed
 predicates — the direction that survives without excluded middle. 

 --------
 在闭合集上的选定顺序意味着闭合谓词的包含关系——这是在没有排中律时依然成立的方向。
*)
Lemma closed_order_implies_inclusion {X : TopSpace} (C D : ClosedSet X) :
  (∀ x : X, closed_compl D x → closed_compl C x) →
  ∀ x : X, closed_pred C x → closed_pred D x.
Proof.
  intros Hincl x Hc.
  exact (snd (closed_agree D x) (fun hd => fst (closed_agree C x) Hc (Hincl x hd))).
Qed.

(* Likewise for the setoid: agreement of complementing opens implies agreement of the closed predicates. / 同样地，对于等价集合：互补集合的一致性意味着封闭谓词的一致性。 *)
Lemma closed_equiv_implies_pred_equiv {X : TopSpace} (C D : ClosedSet X) :
  (∀ x : X, closed_compl C x ↔ closed_compl D x) →
  ∀ x : X, closed_pred C x ↔ closed_pred D x.
Proof.
  intros Heq x; split.
  - exact (closed_order_implies_inclusion C D (fun y h => snd (Heq y) h) x).
  - exact (closed_order_implies_inclusion D C (fun y h => fst (Heq y) h) x).
Qed.

(** ** The two thin categories / ** 两个薄类别 *)

(*
 The opens of X as a thin category: objects the opens, a unique arrow
 `U ~> V` when `U ⊆ V`.  As in Instance/Proset.v the hom-setoid is
 trivial, since any two parallel arrows are the same arrow. 

 --------
 X 的开集作为一个薄范畴：对象是开集，当 `U ⊆ V` 时，有一个唯一的箭头 `U ~> V`。如同在 Instance/Proset.v 中，hom-集合是平凡的，因为任何两条平行箭头都是相同的箭头。
*)
Program Definition Opens (X : TopSpace) : Category := {|
  obj     := OpenSet X;
  hom     := fun U V => ∀ x : X, `1 U x → `1 V x;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun U x u => u;
  compose := fun U V W g f x u => g x (f x u)
|}.

(*
 The closed sets of X as a thin category, ordered by REVERSE inclusion of
 the complementing opens (design note 2).  By
 [closed_order_implies_inclusion] an arrow `C ~> D` does entail
 `C ⊆ D` on the closed predicates. 

 --------
 作为薄范畴的 X 的闭集，按互补开集的逆包含顺序排列（设计注释 2）。通过 [closed_order_implies_inclusion] 一个箭头 `C ~> D` 的确推出 `C ⊆ D` 在闭谓词上。
*)
Program Definition Closeds (X : TopSpace) : Category := {|
  obj     := ClosedSet X;
  hom     := fun C D => ∀ x : X, closed_compl D x → closed_compl C x;
  homset  := fun _ _ => {| equiv := fun _ _ => True |};
  id      := fun C x u => u;
  compose := fun C D E g f x u => f x (g x u)
|}.

(* * ** Complementation as an isomorphism of categories / * ** 作为范畴同构的补集 *)

(*
 Forward: an open goes to its complement.  An inclusion `U ⊆ V` is
 literally the arrow required in `(Closeds X)^op`, namely the inclusion
 of the complementing opens. 

 --------
 前向：一个开集指向它的补集。一个包含 `U ⊆ V` 字面上就是 `(Closeds X)^op` 中所需的箭头，即补集开的包含。
*)
Program Definition OpenCompl (X : TopSpace) : Opens X ⟶ (Closeds X)^op := {|
  fobj := fun U => open_complement U;
  fmap := fun U V g => g
|}.

(* Backward: a closed set goes to its complementing open. / 反向：一个闭合集合对应于它的补集开集。 *)
Program Definition ClosedCompl (X : TopSpace) : (Closeds X)^op ⟶ Opens X := {|
  fobj := fun C => closed_interior C;
  fmap := fun C D g => g
|}.

(*
 Riehl, CTiC Example 1.4.4(v), constructively: the opens of X and the
 opposite of its closed sets are isomorphic categories.  Both round trips
 are the identity on the complementing opens, which is exactly what the
 chosen order compares — note that the closed predicate of a
 round-tripped closed set is the negation of its complementing open,
 equivalent to the original predicate by [closed_agree] but not literally
 it.  Both naturality conditions hold trivially, the categories being
 thin. 

 --------
 Riehl，CTiC 示例 1.4.4(v)，构造性地：X 的开集与其闭集的对偶是同构范畴。两次往返都是在互补开集上的恒等，这正是所选顺序所比较的——注意经过往返的闭集的闭性谓词是其互补开集的否定，通过 [closed_agree] 等价于原始谓词，但不完全相同。两个自然性条件显然成立，因为这些范畴是稀范畴。
*)
Program Definition Opens_Closeds_iso (X : TopSpace) :
  Opens X ≅[Cat] (Closeds X)^op := {|
  to   := OpenCompl X;
  from := ClosedCompl X
|}.
Next Obligation.
  unshelve eexists.
  - intro C; unshelve econstructor.
    + exact (fun x h => h).
    + exact (fun x h => h).
    + exact I.
    + exact I.
  - intros A B g; exact I.
Defined.
Next Obligation.
  unshelve eexists.
  - intro U; unshelve econstructor.
    + exact (fun x h => h).
    + exact (fun x h => h).
    + exact I.
    + exact I.
  - intros A B g; exact I.
Defined.

(** ** The two presheaves on Top / ** 拓扑上的两个预层 *)

(* Preimage of an open along a continuous map is open — that IS continuity, and it is what makes the opens contravariantly functorial. / 沿着连续映射的开集的原像是开集——这就是连续性， 它使得开集具有逆变函子性。 *)
Definition open_preimage {X Y : TopSpace} (g : Y ~{Top}~> X) (U : OpenSet X) :
  OpenSet Y :=
  (fun y => `1 U (g y); continuity g (`1 U) (`2 U)).

(* Preimage of a closed set: both components are pulled back, the complementing open stays open by continuity, and the agreement field transports pointwise. / 闭集的原像：两个分量都被拉回，补集通过连续性保持开放，并且一致性场逐点传递。 *)
Definition closed_preimage {X Y : TopSpace} (g : Y ~{Top}~> X)
           (C : ClosedSet X) : ClosedSet Y := {|
  closed_pred       := fun y => closed_pred C (g y);
  closed_compl      := fun y => closed_compl C (g y);
  closed_compl_open := continuity g (closed_compl C) (closed_compl_open C);
  closed_agree      := fun y => closed_agree C (g y)
|}.

(*
 The setoid of opens of X, as an object of [Sets]: two opens are
 identified when their predicates agree pointwise (up to the library's
 Type-valued `↔`). 

 --------
 X 的开集的集合作为 [Sets] 的一个对象：当两个开集的谓词在每一点上都相同时（相对于库的类型值 `↔`），它们被认为是相同的。
*)
Definition OpenSets (X : TopSpace) : obj[Sets].
Proof.
  refine {| carrier   := OpenSet X
          ; is_setoid := {| equiv := fun U V => ∀ x : X, `1 U x ↔ `1 V x |} |}.
  constructor.
  - intros U x; split; exact (fun h => h).
  - intros U V H x; split; [ exact (snd (H x)) | exact (fst (H x)) ].
  - intros U V W H1 H2 x; split.
    + exact (fun h => fst (H2 x) (fst (H1 x) h)).
    + exact (fun h => snd (H1 x) (snd (H2 x) h)).
Defined.

(*
 The setoid of closed sets of X, compared through their complementing
 opens (design note 2). 

 --------
 通过它们的补集开集比较的 X 的闭合集的集合体（设计说明 2）。
*)
Definition ClosedSets (X : TopSpace) : obj[Sets].
Proof.
  refine {| carrier   := ClosedSet X
          ; is_setoid := {| equiv := fun C D => ∀ x : X,
                              closed_compl C x ↔ closed_compl D x |} |}.
  constructor.
  - intros C x; split; exact (fun h => h).
  - intros C D H x; split; [ exact (snd (H x)) | exact (fst (H x)) ].
  - intros C D E H1 H2 x; split.
    + exact (fun h => fst (H2 x) (fst (H1 x) h)).
    + exact (fun h => snd (H1 x) (snd (H2 x) h)).
Defined.

(*
 From here on the obligations are discharged explicitly rather than by the
 library's default [cat_simpl], because every one of them is a pointwise
 equivalence of predicates and the automation has no reason to prefer one
 direction of an [iffT] to the other. 

 --------
 从这里开始，义务是明确地履行的，而不是由库的默认 [cat_simpl] 履行，因为它们中的每一个都是谓词的逐点等价，自动化没有理由偏好 [iffT] 的一个方向而非另一个方向。
*)
Local Obligation Tactic := idtac.

(* The presheaf of opens: contravariant on [Top], acting by preimage. / 开集的预层：在 [Top] 上是逆变的，通过原像作用。 *)
Program Definition OpensF : Top^op ⟶ Sets := {|
  fobj := fun X => OpenSets X;
  fmap := fun X Y f => {| morphism := open_preimage (unop f) |}
|}.
Next Obligation.
  (* the preimage map respects `≈` of opens / 原像映射保留开集的 `≈` *)
  intros X Y f U V H y; exact (H (unop f y)).
Qed.
Next Obligation.
  (*
 fmap respects `≈` of morphisms: equivalent maps have, pointwise,
 equivalent preimages, because an open respects the carrier's `≈` 

 --------
 fmap 遵守态射的 `≈`：等价的映射在逐点上具有等价的原像，因为开集遵守承载的 `≈`
*)
  intros X Y f g Hfg U y; split.
  - exact (open_proper X (`1 U) (`2 U) (unop f y) (unop g y) (Hfg y)).
  - exact (open_proper X (`1 U) (`2 U) (unop g y) (unop f y)
             (symmetry (Hfg y))).
Qed.
Next Obligation.
  (* the preimage along the identity is the identity / 沿着恒等映射的原像是恒等映射 *)
  intros X U y; split; exact (fun h => h).
Qed.
Next Obligation.
  (* preimages compose contravariantly, definitionally / 原像构成反变，按定义 *)
  intros X Y Z f g U y; split; exact (fun h => h).
Qed.

(* The presheaf of closed sets, likewise. Everything happens on the complementing open, which is exactly the component the setoid compares. / 闭集的上前层也是如此。一切都发生在补集的开集上，这正是集合论比较的组成部分。 *)
Program Definition ClosedsF : Top^op ⟶ Sets := {|
  fobj := fun X => ClosedSets X;
  fmap := fun X Y f => {| morphism := closed_preimage (unop f) |}
|}.
Next Obligation.
  intros X Y f C D H y; exact (H (unop f y)).
Qed.
Next Obligation.
  intros X Y f g Hfg C y; split.
  - exact (open_proper X (closed_compl C) (closed_compl_open C)
             (unop f y) (unop g y) (Hfg y)).
  - exact (open_proper X (closed_compl C) (closed_compl_open C)
             (unop g y) (unop f y) (symmetry (Hfg y))).
Qed.
Next Obligation.
  intros X C y; split; exact (fun h => h).
Qed.
Next Obligation.
  intros X Y Z f g C y; split; exact (fun h => h).
Qed.

(** ** Complementation is natural / ** 补充是自然的 *)

(*
 The two components, at each space.  Complementation respects `≈`
 because the setoid on closed sets compares exactly the complementing
 open, which the forward map copies verbatim; the inverse respects `≈`
 for the same reason, and this is where design note 2 is cashed in — with
 the closed predicates as the setoid there would be no inverse. 

 --------
 这两个组件，在每个空间上。补集遵循 `≈`，因为闭集上的集合等价关系正好比较补集的开集，而正向映射逐字复制该开集；逆映射出于相同原因遵循 `≈`，这就是设计注释 2 得以实现的地方——如果闭谓词作为集合等价关系，则不会有逆映射。
*)
Program Definition complement_at (X : TopSpace) :
  OpenSets X ~{Sets}~> ClosedSets X := {|
  morphism := @open_complement X
|}.
Next Obligation. intros X U V H x; exact (H x). Qed.

Program Definition interior_at (X : TopSpace) :
  ClosedSets X ~{Sets}~> OpenSets X := {|
  morphism := @closed_interior X
|}.
Next Obligation. intros X C D H x; exact (H x). Qed.

(*
 Naturality is the statement that the preimage of a complement is the
 complement of the preimage — which here holds definitionally, both
 sides carrying the complementing open `fun y => U (g y)`. 

 --------
 自然性是指补集的原像是原像的补集——在这里这是按定义成立的，双方都带有补的开集 `fun y => U (g y)`。
*)
Program Definition complement_transform : OpensF ⟹ ClosedsF := {|
  transform := complement_at
|}.
Next Obligation. intros X Y f U y; split; exact (fun h => h). Qed.
Next Obligation. intros X Y f U y; split; exact (fun h => h). Qed.

Program Definition interior_transform : ClosedsF ⟹ OpensF := {|
  transform := interior_at
|}.
Next Obligation. intros X Y f C y; split; exact (fun h => h). Qed.
Next Obligation. intros X Y f C y; split; exact (fun h => h). Qed.

(*
 The natural isomorphism `OpensF ≅ ClosedsF` in `[Top^op, Sets]`: Riehl's
 Example 1.4.4(v) in its functorial form.  Both round trips are the
 identity pointwise — one because [closed_interior] just reads off the
 complementing open that [open_complement] stored, the other because a
 closed set is determined, for the chosen setoid, by that same open. 

 --------
 在 ` [Top^op, Sets]ZZ ` 中的自然同构 `OpensF ≅ ClosedsF`：Riehl 的例子 1.4.4(v) 的函子形式。两个往返都是按点的恒等映射——一个是因为 [closed_interior] 只是读取 [open_complement] 存储的补开集，另一个是因为对于所选择的集合体，闭集由相同的开集确定。
*)
Program Definition complement_natural : OpensF ≅[Fun] ClosedsF := {|
  to   := complement_transform;
  from := interior_transform
|}.
Next Obligation. intros X C y; split; exact (fun h => h). Qed.
Next Obligation. intros X U y; split; exact (fun h => h). Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The exact price of the classical reading / * ** 古典阅读的确切价格 *)

(*
 Design note 2 chose to compare closed sets through their complementing
 opens and disclosed what that choice buys and what it costs.  This
 closing section (its first theorem supplied by the audit of the first
 commit) makes the cost precise rather than rhetorical.

 If agreement of the closed PREDICATES implied agreement of the
 complementing opens — the respectfulness a predicate-comparing setoid
 would need — then double negation would be eliminable at every Type.
 The probe is the one-point space with the constant predicates `P` and
 `¬¬P`: their negations are equivalent outright, so the hypothetical
 implication hands back `P ↔ ¬¬P` at the point. 

 --------
 设计笔记2选择通过互补的开集来比较闭合集，并揭示了这种选择的收益与代价。本章节的结尾（其第一个定理由第一次提交的审计提供）使代价明确，而非仅停留在修辞上。

 如果闭合谓词的一致性意味着互补开集的一致性——即谓词比较集合所需要的尊重性——那么在每种类型中都可以消除双重否定。探测对象是一点空间，其常量谓词为`P`和`¬¬P`：它们的否定本身就是等价的，所以假设的蕴含在该点返回`P ↔ ¬¬P`。
*)
Theorem pred_comparison_forces_DNE :
  (∀ (X : TopSpace) (C D : ClosedSet X),
      (∀ x : X, closed_pred C x ↔ closed_pred D x) →
      (∀ x : X, closed_compl C x ↔ closed_compl D x)) →
  ∀ P : Type, ¬ ¬ P → P.
Proof.
  intros Hconv P.
  pose (CP := open_complement (X:=Point_Top)
                ((fun _ : Point_Top => P); open_const Point_Top P)).
  pose (CN := open_complement (X:=Point_Top)
                ((fun _ : Point_Top => (¬ ¬ P : Type));
                 open_const Point_Top (¬ ¬ P : Type))).
  assert (Hpred : ∀ x : Point_Top, closed_pred CP x ↔ closed_pred CN x).
  { intro x; split.
    - intros np nnp; exact (nnp np).
    - intros nnnp p; exact (nnnp (fun np => np p)). }
  exact (snd (Hconv Point_Top CP CN Hpred ttt)).
Qed.

(*
 Under double-negation elimination as an EXPLICIT HYPOTHESIS — taken as a
 hypothesis and never as an axiom, the same discipline the library
 applies to UIP and to choice — the two constructively one-directional
 implications become equivalences, and Riehl's classical statement is
 recovered in full. 

 --------
 在作为明确假设使用的双重否定消除下——被作为假设而从不作为公理使用，正如库对 UIP 和选择所采用的相同原则——两个构造性单向蕴含变为等价关系，并且 Riehl 的经典表述得以完全恢复。
*)
Section Classical.

Hypothesis DNE : ∀ P : Type, ¬ ¬ P → P.

Lemma closed_inclusion_implies_order_classical
  {X : TopSpace} (C D : ClosedSet X) :
  (∀ x : X, closed_pred C x → closed_pred D x) →
  (∀ x : X, closed_compl D x → closed_compl C x).
Proof using DNE.
  intros Hincl x Hd.
  apply (DNE (closed_compl C x)).
  intro Hnc.
  exact (fst (closed_agree D x) (Hincl x (snd (closed_agree C x) Hnc)) Hd).
Qed.

Lemma closed_pred_equiv_implies_equiv_classical
  {X : TopSpace} (C D : ClosedSet X) :
  (∀ x : X, closed_pred C x ↔ closed_pred D x) →
  (∀ x : X, closed_compl C x ↔ closed_compl D x).
Proof using DNE.
  intros H x; split.
  - intro Hc; exact (closed_inclusion_implies_order_classical D C
                       (fun y => snd (H y)) x Hc).
  - intro Hd; exact (closed_inclusion_implies_order_classical C D
                       (fun y => fst (H y)) x Hd).
Qed.

End Classical.
