Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Section Morphisms.

Context {C : Category}.

Open Scope type_scope.

(*
Special classes of morphisms and their relationships: idempotents and
   involutions, sections and retractions (split mono/epi), epimorphisms and
   monomorphisms, and the implications between them. Throughout, the laws use
   the hom-setoid equivalence `≈` rather than Coq's `=`.

--------
特殊态射类及其关系：幂等元与对合、截面与收缩（分裂 mono/epi）、满射与单射，
   以及它们之间的蕴含。全程定律使用 hom-setoid 等价 `≈` 而非 Coq 的 `=`。
*)

(*
nLab: https://ncatlab.org/nlab/show/idempotent
   Wikipedia: https://en.wikipedia.org/wiki/Idempotence

   An endomorphism `f : x ~> x` is idempotent when `f ∘ f ≈ f` (idem).

--------
nLab：https://ncatlab.org/nlab/show/idempotent
Wikipedia：https://en.wikipedia.org/wiki/Idempotence

当 `f ∘ f ≈ f`（幂等）时，内同态 `f : x ~> x` 是幂等的。
*)


(*
   【Morphisms 各 Class 语法与字段展开】/ Syntax & field walkthrough
   （口吻对齐 Category @ b81c379、Functor @ c826572；本文件是「态射上的性质」合集）

   1) 这是什么 / What this is
      不定义新运算，只给已有态射贴标签：幂等、对合、分裂 mono/epi、满/单…
      Tags on existing morphisms: idempotent, involution, split mono/epi, epi/mono…
      Class ≈ Haskell class（一次对照）：这里 Instance 常是证明义务，不是实现代码。
      Class ≈ Haskell class (said once): Instances here are mostly proof obligations.

   2) 共同前提 / Shared preamble
      Section 里 Context {C : Category}；定律一律用 ≈，不用 =。
      All laws use ≈, never definitional =.

   3) 几组字段怎么读 / How to read the field groups
      - Idempotent / Involutive：只一条律（f∘f ≈ f 或 f∘f ≈ id）。
      - Section f / Retraction f：分裂单/满；字段 section/retract 是另一侧逆，
        *_comp 是证明义务。注意命名：Section f 说的是「f 本身可裂」。
        / split mono/epi; the other inverse is data, *_comp is the law.
      - SplitIdempotent：幂等经 y 分解；sr 与 rs 两条律缺一不可。
      - Epic / Monic：右/左消去；Epic f 恰是 C^op 里的 Monic f。
      - Bimorphic ≈ Epic + Monic（见后文）。

   4) 与教科书差在哪 / Differs from textbooks
      分裂版本携带具体逆（计算相关）；纯 Epic/Monic 只给消去性质。
      Split forms carry a concrete inverse (computational); Epic/Monic are properties.

   阅读顺序：Idempotent → Section/Retraction → Epic/Monic → 后文蕴含引理。
   Reading order: Idempotent → Section/Retraction → Epic/Monic → implication lemmas.
*)

Class Idempotent `(f : x ~> x) := {
  idem : f ∘ f ≈ f             (* idempotency law: f ∘ f ≈ f / 幂等律：f ∘ f ≈ f *)
}.

(*
nLab: https://ncatlab.org/nlab/show/involution
   Wikipedia: https://en.wikipedia.org/wiki/Involution_(mathematics)

   An endomorphism `f : x ~> x` is involutive when it is its own inverse,
   `f ∘ f ≈ id` (invol).

--------
nLab: https://ncatlab.org/nlab/show/involution
   维基百科: https://en.wikipedia.org/wiki/Involution_(mathematics)

   当一个内射 `f : x ~> x` 是其自身的逆时，它是自反的，
   `f ∘ f ≈ id` (自反)。
*)

Class Involutive `(f : x ~> x) := {
  invol : f ∘ f ≈ id           (* involution law: f ∘ f ≈ id / 自反律：f ∘ f ≈ id *)
}.

(*
For an involution g, precomposition by g is its own inverse, so it may be
   moved across an equation: f ≈ g ∘ h  iff  g ∘ f ≈ h.

--------
对于一个自反映射 g，先与 g 合成是它自身的逆，因此它可以在方程中移动：f ≈ g ∘ h 当且仅当 g ∘ f ≈ h。
*)
Lemma flip_invol {x y} (f h : x ~> y) (g : y ~> y) `{@Involutive _ g} :
  f ≈ g ∘ h ↔ g ∘ f ≈ h.
Proof.
  split; intros.
  - rewrite X, comp_assoc, invol; cat.
  - rewrite <- X, comp_assoc, invol; cat.
Qed.

(*
nLab: https://ncatlab.org/nlab/show/split+monomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Section_(category_theory)

   `Section f` witnesses that `f : x ~> y` is a split monomorphism: it has a
   left inverse `section : y ~> x` with `section ∘ f ≈ id` (section_comp).
   Equivalently, f is a section of the retraction `section`. Every such f is
   monic (sections_are_monic). Note the naming convention used here: a value
   of `Section f` records that f itself splits, the field `section` being the
   accompanying retraction.

--------
nLab: https://ncatlab.org/nlab/show/split+monomorphism
   维基百科: https://en.wikipedia.org/wiki/Section_(category_theory)

   `Section f` 证明 `f : x ~> y` 是一个分裂单态：它有一个左逆 `section : y ~> x`，满足 `section ∘ f ≈ id`（section_comp）。
   等价地，f 是重traction `section` 的一个截面。每个这样的 f 都是单态的（sections_are_monic）。注意这里使用的命名约定：`Section f` 的值记录了 f 本身是分裂的，字段 `section` 是相应的重traction。
*)

Class Section `(f : x ~> y) := {
  section : y ~> x;               (* the retraction (left inverse) of f / f 的收缩（左逆） *)
  section_comp : section ∘ f ≈ id (* left inverse law: section ∘ f ≈ id / 左逆律：section ∘ f ≈ id *)
}.

(*
nLab: https://ncatlab.org/nlab/show/split+epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Section_(category_theory)

   `Retraction f` witnesses that `f : x ~> y` is a split epimorphism: it has a
   right inverse `retract : y ~> x` with `f ∘ retract ≈ id` (retract_comp).
   Equivalently, f is a retraction of the section `retract`. Every such f is
   epic (retractions_are_epic). As with `Section`, a value of `Retraction f`
   records that f itself splits, the field `retract` being its section.

--------
nLab: https://ncatlab.org/nlab/show/split+epimorphism
   维基百科: https://en.wikipedia.org/wiki/Section_(category_theory)

   `Retraction f` 证明 `f : x ~> y` 是一个分裂的上射：它有一个右逆 `retract : y ~> x` 并且 `f ∘ retract ≈ id`（retract_comp）。
   等价地，f 是截面 `retract` 的重traction。每个这样的 f 都是上射（retractions_are_epic）。和 `Section` 一样，`Retraction f` 的一个值记录了 f 本身是可分裂的，字段 `retract` 是它的截面。
*)

Class Retraction `(f : x ~> y) := {
  retract : y ~> x;               (* the section (right inverse) of f / f 的部分（右逆） *)
  retract_comp : f ∘ retract ≈ id (* right inverse law: f ∘ retract ≈ id / 右逆律：f ∘ retract ≈ id *)
}.

(*
nLab: https://ncatlab.org/nlab/show/split+idempotent
   Wikipedia: https://en.wikipedia.org/wiki/Karoubi_envelope

   A split idempotent `split_idem : x ~> x` factors through an object y as a
   retraction `split_idem_r : x ~> y` followed by a section
   `split_idem_s : y ~> x`, with `split_idem_s ∘ split_idem_r ≈ split_idem`
   (split_idem_sr) and `split_idem_r ∘ split_idem_s ≈ id` (split_idem_rs). The
   two laws TOGETHER force `split_idem` to be idempotent, and neither does so
   alone: `split_idem_rs` does not mention `split_idem` at all, and
   `split_idem_sr` only names it. The derivation is `split_idem_Idempotent`
   below, and it uses both. The mediating object y is exposed as
   `split_idem_retract`.

--------
nLab: https://ncatlab.org/nlab/show/split+idempotent
   维基百科: https://en.wikipedia.org/wiki/Karoubi_envelope

   一个分裂幂等 `split_idem : x ~> x` 通过对象 y 分解为一个收缩 `split_idem_r : x ~> y` 后跟一个截面 `split_idem_s : y ~> x`，具有 `split_idem_s ∘ split_idem_r ≈ split_idem`（split_idem_sr）和 `split_idem_r ∘ split_idem_s ≈ id`（split_idem_rs）。这两条定律一起强制 `split_idem` 成为幂等的，而单独的任何一条都不能做到：`split_idem_rs` 根本没有提到 `split_idem`，`split_idem_sr` 只是提到它。推导在下面的 `split_idem_Idempotent` 中，并且使用了两者。媒介对象 y 表示为 `split_idem_retract`。
*)

Class SplitIdempotent {x y : C} := {
  split_idem_retract := y;                  (* the splitting object y / 分割对象 y *)

  split_idem    : x ~> x;                   (* the idempotent on x / x 上的幂等元 *)
  split_idem_r  : x ~> split_idem_retract;  (* retraction x ~> y / 回缩 x ~> y *)
  split_idem_s  : split_idem_retract ~> x;  (* section y ~> x / 节 y ~> x *)
  split_idem_sr : split_idem_s ∘ split_idem_r ≈ split_idem;
                                            (* s ∘ r ≈ split_idem / s ∘ r ≈ 分裂幂等 *)
  split_idem_rs : split_idem_r ∘ split_idem_s ≈ id
                                            (* r ∘ s ≈ id on y / r ∘ s ≈ 在 y 上的 id *)
}.

(*
nLab: https://ncatlab.org/nlab/show/epimorphism
   Wikipedia: https://en.wikipedia.org/wiki/Epimorphism

   `Epic f` witnesses that `f : x ~> y` is an epimorphism: f is
   right-cancellable, `g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2` for all parallel
   `g1 g2 : y ~> z` (epic). This is exactly `Monic f` in `C^op`.

--------
nLab: https://ncatlab.org/nlab/show/epimorphism
   维基百科: https://en.wikipedia.org/wiki/Epimorphism

   `Epic f` 证明 `f : x ~> y` 是一个满同态：f 是可右约化的，`g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2` 对于所有平行的 `g1 g2 : y ~> z`（史诗的）。这正是 `Monic f` 在 `C^op` 中的情况。
*)

Class Epic {x y} (f : x ~> y) := {
  epic : ∀ z (g1 g2 : y ~> z), g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2
                                  (* right cancellation: g1∘f ≈ g2∘f → g1 ≈ g2 / 右消去：g1∘f ≈ g2∘f → g1 ≈ g2 *)
}.

(*
nLab: https://ncatlab.org/nlab/show/monomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Monomorphism

   `Monic f` witnesses that `f : x ~> y` is a monomorphism: f is
   left-cancellable, `f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2` for all parallel
   `g1 g2 : z ~> x` (monic). This is exactly `Epic f` in `C^op`.

--------
nLab: https://ncatlab.org/nlab/show/monomorphism
   维基百科: https://en.wikipedia.org/wiki/Monomorphism

   `Monic f` 见证 `f : x ~> y` 是单同态：f 是可左约掉的，`f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2` 对所有平行的 `g1 g2 : z ~> x`（单射）成立。这正是 `Epic f` 在 `C^op` 中的意思。
*)

Class Monic {x y} (f : x ~> y) := {
  monic : ∀ z (g1 g2 : z ~> x), f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2
                                  (* left cancellation: f∘g1 ≈ f∘g2 → g1 ≈ g2 / 左消去：f∘g1 ≈ f∘g2 → g1 ≈ g2 *)
}.

(*
A bimorphism is both epic and monic; a split epi is a retraction and a
   split mono is a section (the converse implications above hold via
   retractions_are_epic and sections_are_monic).

--------
双态射既是满射又是单射；分裂满射是一个收缩，分裂单射是一个截面（上述逆向蕴涵通过 retractions_are_epic 和 sections_are_monic 成立）。
*)

Definition Bimorphic `(f : x ~> y) := (Epic f * Monic f)%type.
Definition SplitEpi  `(f : x ~> y) := Retraction f.
Definition SplitMono `(f : x ~> y) := Section f.

Corollary id_idem : ∀ x, Idempotent (id (x:=x)).
Proof. intros; constructor; cat. Qed.

Corollary id_invol : ∀ x, Involutive (id (x:=x)).
Proof. intros; constructor; cat. Qed.

Corollary id_monic : ∀ x, Monic (id (x:=x)).
Proof.
  intros; constructor; intros.
  rewrite !id_left in X.
  assumption.
Qed.

Corollary id_epic : ∀ x, Epic (id (x:=x)).
Proof.
  intros; constructor; intros.
  rewrite !id_right in X.
  assumption.
Qed.

#[local] Hint Unfold Bimorphic : core.
#[local] Hint Unfold SplitEpi : core.
#[local] Hint Unfold SplitMono : core.

Section Lemmas.

Variables x y : C.
Variable f : x ~> y.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); try f_equiv; cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); try f_equiv; cat.

(* Every split epimorphism is an epimorphism. / 每个分裂的满射都是满射。 *)
Lemma retractions_are_epic : Retraction f → Epic f.
Proof.
  autounfold.
  intros.
  destruct X.
  constructor; intros.
  rewrite <- id_right.
  symmetry.
  rewrite <- id_right.
  transitivity (g2 ∘ (f ∘ retract0));
    [ now apply compose_respects |];
  transitivity (g1 ∘ (f ∘ retract0));
    [| now apply compose_respects ].
  reassociate_right.
Qed.

(* Every split monomorphism is a monomorphism. / 每个分裂单射都是单射。 *)
Lemma sections_are_monic : Section f → Monic f.
Proof.
  autounfold.
  intros.
  destruct X.
  constructor; intros.
  rewrite <- id_left.
  symmetry.
  rewrite <- id_left.
  transitivity ((section0 ∘ f) ∘ g2);
    [ now apply compose_respects |];
  transitivity ((section0 ∘ f) ∘ g1);
    [| now apply compose_respects ].
  reassociate_left.
Qed.

End Lemmas.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); cat.

(* Epimorphisms are closed under composition. / 上同态在复合下是封闭的。 *)
Definition epi_compose {x y z : C} {f : y ~> z} {g : x ~> y} :
  Epic f → Epic g → Epic (f ∘ g).
Proof.
  autounfold; intros X Y.
  destruct X, Y.
  constructor; intros.
  apply epic0, epic1.
  reassociate_left.
Qed.

(*
Epimorphisms cancel on the LEFT: if a composite is epic, the arrow applied
   LAST is epic.  (Mac Lane, CWM 2nd ed., §I.5 Exercise 1; Riehl, CTiC, Lemma
   1.2.11(ii'); Awodey §2.9 Exercise 2(c).)  Anything g1, g2 agreeing after f
   already agrees after f ∘ g, and the composite cancels.

   Note the asymmetry: nothing follows about g.  A composite can be epic with
   its FIRST factor far from epic -- see [sets_epic_left_factor_only] in
   Instance/Sets.v for a witness.

--------
上射在左侧可约：如果一个复合箭头是上射，则最后应用的箭头也是上射。（Mac Lane, 《范畴论基础》第二版，第I.5节练习1；Riehl, 《范畴理论导引》，引理1.2.11(ii')；Awodey §2.9练习2(c)）任何在f之后相等的g1, g2在f ∘ g之后已经相等，因此复合箭头可约。

注意这种不对称性：关于g没有任何结论。一个复合箭头可能是上射，但它的第一个因子离上射还很远——参见 Instance/Sets.v 中的 [sets_epic_left_factor_only]，作为例子。
*)
Definition epic_cancel {x y z : C} {f : y ~> z} {g : x ~> y} :
  Epic (f ∘ g) → Epic f.
Proof.
  intro H; constructor; intros w g1 g2 Hgg.
  apply (@epic x z (f ∘ g) H w g1 g2).
  rewrite !comp_assoc.
  now rewrite Hgg.
Qed.

(*
Monomorphisms cancel on the RIGHT: if a composite is monic, the arrow
   applied FIRST is monic.  (Mac Lane §I.5 Exercise 1; Riehl Lemma 1.2.11(ii);
   Awodey §2.9 Exercise 2(b), and §5.1 for the subobject reading -- a
   factorization between subobjects is automatically monic, recorded as
   [sub_le_monic] in Theory/Subobject.v.)

   This is the exact dual of [epic_cancel], and Riehl's section is about
   deriving one from the other through C^op rather than proving both.  That
   derivation cannot be performed HERE: Construction/Opposite.v requires
   Theory/Isomorphism.v, which requires this file, so importing the opposite
   category into it is a cycle (verified).  The dual route is carried out one
   layer up instead, in Theory/Morphisms/Duality.v, where [monic_cancel_op]
   re-derives this statement from [epic_cancel] with no second argument.

--------
单态射在右侧可以消去：如果一个复合是单态的，那么最先应用的箭头是单态的。（Mac Lane §I.5 练习 1；Riehl 引理 1.2.11(ii)；Awodey §2.9 练习 2(b)，以及 §5.1 关于子对象的理解——子对象之间的分解自动是单态的，在 Theory/Subobject.v 中记录为 [sub_le_monic]。）

这是 [epic_cancel] 的确切对偶，Riehl 的章节是关于如何通过 C^op 从一个导出另一个，而不是证明两个。这个推导不能在这里进行：Construction/Opposite.v 需要 Theory/Isomorphism.v，而它又需要这个文件，因此将对偶范畴导入其中会形成循环（已验证）。对偶路径在高一层实现，即在 Theory/Morphisms/Duality.v 中，[monic_cancel_op] 从 [epic_cancel] 重新导出此命题，无需第二个参数。
*)
Definition monic_cancel {x y z : C} {f : y ~> z} {g : x ~> y} :
  Monic (f ∘ g) → Monic g.
Proof.
  intro H; constructor; intros w g1 g2 Hgg.
  apply (@monic x z (f ∘ g) H w g1 g2).
  rewrite <- !comp_assoc.
  now rewrite Hgg.
Qed.

(* Monomorphisms are closed under composition. / 单射在复合运算下是封闭的。 *)
Definition monic_compose {x y z : C} {f : y ~> z} {g : x ~> y} :
  Monic f → Monic g → Monic (f ∘ g).
Proof.
  autounfold; intros X Y.
  destruct X, Y.
  constructor; intros.
  apply monic1, monic0.
  reassociate_right.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Split pairs and the idempotents they produce / ** 分裂对及它们产生的幂等元 *)

(*
Mac Lane, CWM 2nd ed., §I.5 (“Monics, Epis, and Zeros”), printed p. 19.
   CITED BY LOCATION; the printed text was not consulted and no sentence of
   it is reproduced here.  The in-tree catalog entry indexes the item as
   [maclane:I.5:def5] and summarizes it as: “When g h = 1_a, g is called a
   split epi, h a split monic, and the composite f = h g is an idempotent”
   (doc/plan/books/maclane/inventory/I.json, id maclane:I.5:def5) -- the
   letter names of the lemma below are that summary's.
   nLab: https://ncatlab.org/nlab/show/split+epimorphism
   nLab: https://ncatlab.org/nlab/show/idempotent

   The nLab page on split epimorphisms records the same fact in the form
   “the pair (e,s) is a splitting of the idempotent s∘e : A→A” (retrieved
   2026-08).

   Half of a one-sided inverse pair is an idempotent.  If g ∘ h ≈ id then the
   OTHER composite h ∘ g absorbs itself, because the inner g ∘ h cancels:

     (h ∘ g) ∘ (h ∘ g) ≈ h ∘ (g ∘ h) ∘ g ≈ h ∘ id ∘ g ≈ h ∘ g.

   Nothing forces h ∘ g to be the identity in turn; when it is not, the
   idempotent is a genuinely non-trivial one.  Two files exhibit such a pair
   and REFUTE the identity for the other composite, so this lemma is not
   witnessed by identities alone: Instance/FinSet/Regular.v
   ([finset_point]/[finset_bang], with [finset_collapse_not_id]) and
   Instance/Sets/Split.v ([sets_incl23]/[sets_retr32], with
   [sets_incl_retr_not_id]).

--------
Mac Lane, CWM 第二版，第 I.5 节（“单态、射态与零元”），印刷版第 19 页。  
   引用位置；未查阅印刷文本，也未在此处复现其中任何句子。树状目录条目将该条目索引为 [maclane:I.5:def5]，并总结为：“当 g h = 1_a 时，g 称为分裂射态，h 称为分裂单态，且复合 f = h g 是幂等的”（doc/plan/books/maclane/inventory/I.json，ID maclane:I.5:def5）——以下引理的字母名称即该总结的名称。  
   nLab: https://ncatlab.org/nlab/show/split+epimorphism  
   nLab: https://ncatlab.org/nlab/show/idempotent

nLab 上关于分裂上同态的页面以如下形式记录了相同的事实：
“对 (e, s) 是幂等元 s∘e : A→A 的一个分裂”（检索于 2026-08）。

一个单边逆元对的一半是幂等的。如果 g ∘ h ≈ id，那么另一个复合 h ∘ g 会吸收自身，因为内部的 g ∘ h 相互抵消：

(h ∘ g) ∘ (h ∘ g) ≈ h ∘ (g ∘ h) ∘ g ≈ h ∘ id ∘ g ≈ h ∘ g.

没有任何东西迫使 h ∘ g 反过来成为恒等映射；当它不是时，该幂等元是真正非平凡的。两个文件显示了这样的一对，并且否定了另一个复合的恒等性，因此这个引理不能仅通过恒等式来证明：Instance/FinSet/Regular.v（[finset_point]/[finset_bang]，带 [finset_collapse_not_id]）和 Instance/Sets/Split.v（[sets_incl23]/[sets_retr32]，带 [sets_incl_retr_not_id]）。
*)

Lemma split_pair_idempotent {x y : C} (g : x ~> y) (h : y ~> x) :
  g ∘ h ≈ id → Idempotent (h ∘ g).
Proof.
  intro Hgh.
  constructor.
  rewrite <- comp_assoc.
  rewrite (comp_assoc g h g).
  rewrite Hgh, id_left.
  reflexivity.
Qed.

(* Idempotence transports along `≈`, the hom-setoid equivalence. / 幂等性沿着 `≈`，即同集合等价，传输。 *)
Lemma idempotent_respects {x : C} (f g : x ~> x) :
  f ≈ g → Idempotent f → Idempotent g.
Proof.
  intros Hfg [Hf].
  constructor.
  rewrite <- Hfg.
  exact Hf.
Qed.

(*
[SplitIdempotent] above states the two splitting laws, and its header
   points here for the idempotence they force.  This is that derivation: the
   retraction/section pair r, s satisfies r ∘ s ≈ id, so s ∘ r is idempotent
   by [split_pair_idempotent], and s ∘ r ≈ split_idem transports it -- one
   splitting law for each step, which is why neither law alone would do.
   Before this lemma nothing in the tree derived the idempotence of a
   [SplitIdempotent]'s [split_idem] field.
   The class was CONCLUDED in exactly two places -- [id_idem] in this
   file and [Extend_idem] (Construction/Karoubi/Universal.v, the image of
   a Karoubi object's idempotent under a functor) -- and every remaining
   occurrence of it was a HYPOTHESIS (Construction/Karoubi.v,
   Construction/Karoubi/Universal.v and three sites in
   Instance/Sets/Karoubi.v).

--------
[SplitIdempotent] 上述陈述了两个分裂定律，其标题在此指向它们所强制的幂等性。这就是推导：收缩/截面对 r、s 满足 r ∘ s ≈ id，因此 s ∘ r 按 [split_pair_idempotent] 是幂等的，并且 s ∘ r ≈ split_idem 传递它——每一步一个分裂定律，这就是为什么单独一个定律不足以实现。在这个引理之前，树中没有任何东西推导出 [SplitIdempotent] 的 [split_idem] 字段的幂等性。该类仅在两个地方被终结——此文件中的 [id_idem] 和 [Extend_idem]（Construction/Karoubi/Universal.v，一个 Karoubi 对象在函子下的幂等元的像）——其余所有出现都是假设（Construction/Karoubi.v、Construction/Karoubi/Universal.v 以及 Instance/Sets/Karoubi.v 中的三个位置）。
*)
Lemma split_idem_Idempotent {x y : C} (S : @SplitIdempotent x y) :
  Idempotent (@split_idem x y S).
Proof.
  apply (idempotent_respects (@split_idem_s x y S ∘ @split_idem_r x y S)).
  - exact (@split_idem_sr x y S).
  - exact (split_pair_idempotent _ _ (@split_idem_rs x y S)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Regular (von Neumann regular) arrows / ** 正则（冯·诺伊曼正则）箭头 *)

(*
Mac Lane, CWM 2nd ed., §I.5 Exercise 7, printed p. 21 -- again CITED BY
   LOCATION, not quoted; the printed text was not consulted.  The in-tree
   catalog summarizes the exercise as: “Call an arrow f : a -> b in a
   category C regular when there exists g : b -> a with f g f = f.  Show f is
   regular whenever it has either a left or a right inverse, and prove that
   in Set every arrow f : a -> b with a nonempty is regular”
   (doc/plan/books/maclane/inventory/I.json, id maclane:I.5:ex7).
   Wikipedia: https://en.wikipedia.org/wiki/Regular_semigroup
   Wikipedia: https://en.wikipedia.org/wiki/Von_Neumann_regular_ring

   An arrow f is REGULAR when some g runs backwards along it well enough to
   reproduce f, i.e. f ∘ g ∘ f ≈ f.  The equation is von Neumann's, from
   ring theory: a ring is regular when for every a there is an x with
   a = a x a (von Neumann, “On Regular Rings”, Proc. Natl. Acad. Sci. USA
   22(12), 1936, pp. 707-713), and modern usage says VON NEUMANN REGULAR to
   keep the notion apart from the unrelated regular rings of commutative
   algebra (Wikipedia, “Von Neumann regular ring”, retrieved 2026-08).  The
   semigroup version -- an element a with a x a = a -- was adapted from that
   ring condition and introduced by J. A. Green, “On the structure of
   semigroups” (1951), at David Rees's suggestion (Wikipedia, “Regular
   semigroup”, retrieved 2026-08).  The two articles name the witness x
   differently: “weak inverse” for rings, “pseudoinverse” for semigroups.
   Neither calls it a quasi-inverse, so PSEUDOINVERSE is the word used
   throughout this development.

   The pseudoinverse g need not be unique, and neither composite f ∘ g nor
   g ∘ f need be an identity.  What they are is idempotent, which is the
   content of [regular_composites_idempotent] below -- a direct computation
   from the regularity law, NOT an instance of [split_pair_idempotent] above
   (that lemma wants one of the composites to be the identity outright, which
   is precisely what regularity drops).

   Regularity is weaker than either one-sided invertibility:
   [regular_of_section] and [regular_of_retraction] below give both
   implications, and Instance/FinSet/Regular.v exhibits an arrow that is
   regular yet neither a section nor a retraction ([finset_shift3]).  It is
   also a real restriction on an arrow rather than a triviality, and two
   categories witness that: Instance/Two.v exhibits an arrow of the interval
   category that is monic and epic and NOT regular ([TwoXY_not_regular]), and
   Instance/FinSet/Regular.v refutes regularity for the unique arrow 0 → 1
   ([finset_empty_to_one_not_regular]).  Both work for the same blunt reason,
   that the only candidate pseudoinverse would be an arrow the category does
   not have; Instance/Sets/Regular.v shows the bluntness is forced rather
   than convenient, since over [Sets] regularity can be undecided
   ([sets_coarsen_not_regular_absurd]).

   The definition is stated with the library's `∃`, which is Type-valued
   (`sigT`, Lib/Foundation.v), so a regularity witness is DATA: the
   pseudoinverse can be projected out and computed with.  That is what makes
   the FinSet result of Instance/FinSet/Regular.v an executable finite search
   rather than a bare existence claim, and it is why the four constructions
   below that PRODUCE such data -- [regular_of_section],
   [regular_of_retraction], [regular_epic_retraction] and
   [regular_monic_section] -- end in [Defined] rather than [Qed].

--------
Mac Lane, CWM 第二版, §I.5 练习 7, 印刷页 21 -- 再次由位置引用，而非直接引用；未参考印刷文本。树内目录将该练习总结为：“在一个范畴 C 中，如果存在 g : b -> a 使得 f g f = f，则称箭头 f : a -> b 为正规。证明若 f 有左逆或右逆，则 f 是正规；并证明在 Set 中，当 a 非空时，每个箭头 f : a -> b 都是正规。” (doc/plan/books/maclane/inventory/I.json, id maclane:I.5:ex7)。 Wikipedia: https://en.wikipedia.org/wiki/Regular_semigroup Wikipedia: https://en.wikipedia.org/wiki/Von_Neumann_regular_ring

当某个 g 足够沿着箭头 f 向后运行以重现 f，即 f ∘ g ∘ f ≈ f 时，箭头 f 是常规的。这个方程是冯·诺依曼的，来自环论：当每个 a 存在一个 x 使得 a = a x a 时，这个环是正规环（von Neumann，“On Regular Rings”，Proc. Natl. Acad. Sci. USA 22(12), 1936, 第707-713页）。现代用法称之为冯·诺依曼正规，以将这一概念与交换代数中无关的正规环区分开来（维基百科，“Von Neumann regular ring”，检索于2026-08）。半群版本——一个元素 a 满足 a x a = a——是从环条件改编的，由 J. A. Green 在 David Rees 的建议下引入，《On the structure of semigroups》（1951）（维基百科，“Regular semigroup”，检索于2026-08）。这两篇文章对见证元素 x 的命名不同：环中称为“弱逆”，半群中称为“伪逆”。没有一个称其为准逆，因此在整个发展过程中使用的词是 PSEUDOINVERSE（伪逆）。

伪逆 g 不必是唯一的，复合函数 f ∘ g 或 g ∘ f 也不必是恒等映射。它们的性质是幂等的，这就是下面 [regular_composites_idempotent] 的内容——直接根据正则律计算，而不是上面 [split_pair_idempotent] 的例子（那个引理要求其中一个复合函数直接是恒等映射，而这正是正则律所放弃的）。

正则性比单边可逆性弱：下面的 [regular_of_section] 和 [regular_of_retraction] 给出了两种蕴含关系，而 Instance/FinSet/Regular.v 展示了一个既是正则箭头又既不是截面也不是收缩的箭头（[finset_shift3]）。它还是箭头的一个真正限制，而非平凡性，并且有两个范畴可以证明这一点：Instance/Two.v 展示了区间范畴中的一个既是单射又是满射但不是正则的箭头（[TwoXY_not_regular]），并且 Instance/FinSet/Regular.v 反驳了从 0 到 1 的唯一箭头的正则性（[finset_empty_to_one_not_regular]）。它们都有同一个直接的原因，即唯一的候选伪逆是范畴中不存在的箭头；Instance/Sets/Regular.v 表明这种直接性是必然的而非方便的，因为在 [Sets] 上正则性可能是未决定的（[sets_coarsen_not_regular_absurd]）。

该定义在库的 `∃` 中给出，它是类型值 (`sigT`, Lib/Foundation.v)，因此一个规则性见证是 DATA：伪逆可以被投影出来并计算。这就是为什么 Instance/FinSet/Regular.v 的 FinSet 结果是可执行的有限搜索，而不是一个单纯的存在性声明，并且这也是下面四个生成此类数据的构造 —— [regular_of_section]、[regular_of_retraction]、[regular_epic_retraction] 和 [regular_monic_section] —— 以 [Defined] 结尾而不是 [Qed] 的原因。
*)

Definition RegularMorphism `(f : x ~> y) := ∃ g : y ~> x, f ∘ g ∘ f ≈ f.

(*
An arrow with a LEFT inverse is regular: the left inverse is already a
   pseudoinverse, since f ∘ (s ∘ f) ≈ f ∘ id ≈ f.

--------
具有左逆的箭头是可逆的：左逆已经是伪逆，因为 f ∘ (s ∘ f) ≈ f ∘ id ≈ f。
*)
Definition regular_of_section `(f : x ~> y) : Section f → RegularMorphism f.
Proof.
  intros [s Hs].
  exists s.
  rewrite <- comp_assoc, Hs.
  apply id_right.
Defined.

(* An arrow with a RIGHT inverse is regular: dually, (f ∘ r) ∘ f ≈ id ∘ f. / 具有右逆的箭头是正规箭头：对偶地，(f ∘ r) ∘ f ≈ id ∘ f。 *)
Definition regular_of_retraction `(f : x ~> y) :
  Retraction f → RegularMorphism f.
Proof.
  intros [r Hr].
  exists r.
  rewrite Hr.
  apply id_left.
Defined.

(*
Both composites built from a pseudoinverse are idempotent:
     (f ∘ g) ∘ (f ∘ g) ≈ ((f ∘ g) ∘ f) ∘ g ≈ f ∘ g,
     (g ∘ f) ∘ (g ∘ f) ≈ g ∘ ((f ∘ g) ∘ f) ≈ g ∘ f.
   Proved here from the regularity law alone.  (The Wikipedia “Regular
   semigroup” article states the corresponding semigroup fact for a PROPER
   inverse b -- one satisfying both a b a = a and b a b = b -- rather than
   for an arbitrary pseudoinverse; the computation above shows the weaker
   hypothesis already suffices, so no claim is being borrowed here.)

--------
由伪逆构建的两个复合都是幂等的：
     (f ∘ g) ∘ (f ∘ g) ≈ ((f ∘ g) ∘ f) ∘ g ≈ f ∘ g,
     (g ∘ f) ∘ (g ∘ f) ≈ g ∘ ((f ∘ g) ∘ f) ≈ g ∘ f。
   这里仅从正则律中证明。（维基百科“正则半群”文章陈述了对应半群事实适用于一个真正的逆 b —— 一个满足 a b a = a 和 b a b = b 的逆 —— 而不是任意伪逆；上面的计算显示较弱的假设已足够，因此这里没有借用任何论断。）
*)
Lemma regular_composites_idempotent {x y : C} (f : x ~> y) (g : y ~> x) :
  f ∘ g ∘ f ≈ f → Idempotent (f ∘ g) ∧ Idempotent (g ∘ f).
Proof.
  intro Hg.
  split; constructor.
  - rewrite (comp_assoc (f ∘ g) f g), Hg.
    reflexivity.
  - rewrite <- comp_assoc, (comp_assoc f g f), Hg.
    reflexivity.
Qed.

(*
Under a cancellation hypothesis the converses hold.  These two lemmas are
   what make the choice discussion of Instance/FinSet/Regular.v and
   Instance/Sets/Regular.v precise rather than hand-waved:
   [regular_epic_retraction], quantified over the arrows of [Sets], IS the
   implication [blanket_regularity_entails_splitting] from the blanket
   principle “every arrow with inhabited domain is regular” to “every such
   epimorphism splits”, and over [Sets] the latter already decides every
   proposition ([blanket_splitting_entails_LEM]).  A regular EPI splits:
   cancel f on the right of (f ∘ g) ∘ f ≈ id ∘ f.

--------
在消去假设下，逆命题成立。这两个引理使得 Instance/FinSet/Regular.v 和 Instance/Sets/Regular.v 中的选择讨论变得精确，而不是含糊其辞：[regular_epic_retraction]，对 [Sets] 的箭头进行量化，正是从通用原则“每个有非空域的箭头都是正则的”推导到“每个这样的上同态都可分解”的蕴含 [blanket_regularity_entails_splitting]，并且在 [Sets] 上，后者已经决定了每个命题（[blanket_splitting_entails_LEM]）。一个正则上同态可分解：在 (f ∘ g) ∘ f ≈ id ∘ f 的右边消去 f。
*)
Definition regular_epic_retraction `(f : x ~> y) :
  RegularMorphism f → Epic f → Retraction f.
Proof.
  intros [g Hg] E.
  exists g.
  apply (@epic x y f E y (f ∘ g) id).
  rewrite Hg.
  symmetry.
  apply id_left.
Defined.

(*
Dually, a regular MONO splits: cancel f on the left of
   f ∘ (g ∘ f) ≈ f ∘ id.

--------
类似地，一个正规的单射分解：在 f ∘ (g ∘ f) ≈ f ∘ id 的左边消去 f。
*)
Definition regular_monic_section `(f : x ~> y) :
  RegularMorphism f → Monic f → Section f.
Proof.
  intros [g Hg] M.
  exists g.
  apply (@monic x y f M x (g ∘ f) id).
  rewrite comp_assoc, Hg.
  symmetry.
  apply id_right.
Defined.

End Morphisms.

#[export] Hint Unfold Bimorphic : core.
#[export] Hint Unfold SplitEpi : core.
#[export] Hint Unfold SplitMono : core.

(*
Section/retraction duality: if `section` is the left inverse witnessing
   that f is a split mono, then f exhibits `section` as a split epi.

--------
截/收缩二重性：如果 `section` 是证明 f 是分裂单射的左逆，那么 f 显示 `section` 是分裂满射。
*)
Definition flip_Section {C : Category} `(f : x ~> y)
           (s : @Section C x y f) : @Retraction C y x section.
Proof.
  autounfold.
  destruct s.
  exists f.
  assumption.
Qed.

(*
Dual of flip_Section: if `retract` is the right inverse witnessing that f
   is a split epi, then f exhibits `retract` as a split mono.

--------
flip_Section 的对偶：如果 `retract` 是证明 f 是分裂满射的右逆，那么 f 将 `retract` 显示为分裂单射。
*)
Definition flip_Retraction {C : Category} `(f : x ~> y)
           (s : @Retraction C x y f) : @Section C y x retract.
Proof.
  autounfold.
  destruct s.
  exists f.
  assumption.
Qed.
