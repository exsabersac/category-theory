Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Concrete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Concrete.

Generalizable All Variables.

(** * Underlying injections and surjections in a concrete category *)

(*
 nLab:      https://ncatlab.org/nlab/show/concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Concrete_category
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.6,

   本文件给出态射类/性质相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ConcreteMorphisms.

Context {C : Category}.
Context `{Con : @Concrete C}.

(*
   本节说明相关定义、性质与动机。 Injective underlying function implies monic. This IS corollary of.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma concrete_injective_monic {x y : C} (f : x ~> y) :
  injective (concrete_fun f) → Monic f.
Proof.
  intros Hinj.
  apply (faithful_reflects_monic underlying (H:=underlying_faithful) f).
  apply (fst (injectivity_is_monic (fmap[underlying] f))).
  intros a b Hab.
  exact (inj (injective:=Hinj) Hab).
Qed.

(*
   本节说明相关定义、性质与动机。 Surjective underlying function implies epic: mirror image. A point of. underlying set TARGET is hit some point `a` source, two composites agree at `a`;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma concrete_surjective_epic {x y : C} (f : x ~> y) :
  surjective (concrete_fun f) → Epic f.
Proof.
  intros Hsur.
  constructor; intros z g1 g2 Hg.
  apply concrete_arrow_eq; intro b.
  destruct (@surj _ _ _ _ Hsur b) as [a Ha].
  rewrite <- Ha.
  transitivity (concrete_fun (g1 ∘ f) a).
  { symmetry; exact (fmap_comp (Functor:=underlying) g1 f a). }
  transitivity (concrete_fun (g2 ∘ f) a).
  { exact (concrete_fun_respects _ _ Hg a). }
  exact (fmap_comp (Functor:=underlying) g2 f a).
Qed.

End ConcreteMorphisms.

(** ** The corollary at work: [Coq], via [Coq_Concrete] *)

(*
   Non-vacuity of both lemmas at a real concrete 范畴.  `Coq`

   本节说明相关定义、性质与动机。 (Instance/Coq.v) is concrete via [Coq_Concrete] (Instance/Concrete.v), whose underlying-set 函子 reads type setoid under Leibniz equality.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition bool_to_nat (b : bool) : nat := if b then 1%nat else 0%nat.

(*
   本节说明相关定义、性质与动机。 This one statement is `=` rather than `≈`, deliberately so: it relates. ELEMENTS `bool` `nat`, not 态射.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma bool_to_nat_inj (a b : bool) : bool_to_nat a = bool_to_nat b → a = b.
Proof.
  destruct a, b; simpl; solve [ reflexivity | discriminate ].
Qed.

#[local] Instance bool_to_nat_injective :
  injective (concrete_fun (Con:=Coq_Concrete) (bool_to_nat : bool ~{Coq}~> nat)).
Proof.
  constructor; intros a b Hab.
  exact (bool_to_nat_inj a b Hab).
Qed.

(*
   本节说明相关定义、性质与动机。 Predecessor is surjective: every `y` is `pred (S y)`. It is not injective.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Instance Coq_pred_surjective :
  surjective (concrete_fun (Con:=Coq_Concrete) (Nat.pred : nat ~{Coq}~> nat)).
Proof.
  constructor; intro y.
  exists (S y); reflexivity.
Qed.

Definition Coq_bool_to_nat_Monic : Monic (bool_to_nat : bool ~{Coq}~> nat) :=
  concrete_injective_monic (Con:=Coq_Concrete) bool_to_nat bool_to_nat_injective.

Definition Coq_pred_Epic : Epic (Nat.pred : nat ~{Coq}~> nat) :=
  concrete_surjective_epic (Con:=Coq_Concrete) Nat.pred Coq_pred_surjective.

(** ** The same two conclusions through the reflection lemmas *)

(*
   本节说明相关定义、性质与动机。 The corollary can also be reached first establishing property in. `Sets` then reflecting it along 忠实 函子, which is what Riehl's exercise proper supplies.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Coq_bool_to_nat_Monic_reflected :
  Monic (bool_to_nat : bool ~{Coq}~> nat) :=
  faithful_reflects_monic Coq_Underlying bool_to_nat
    (fst (injectivity_is_monic (fmap[Coq_Underlying] bool_to_nat))
       (fun a b (Hab : bool_to_nat a = bool_to_nat b) => bool_to_nat_inj a b Hab)).

(*
   本节说明相关定义、性质与动机。 For epis `Sets`-side ingredient comes from this file's own. [concrete_surjective_epic] at [Sets_Concrete] (Theory/Concrete.v), whose underlying-set 函子 is identity: there `concrete_fun h` IS `h`, so lemma reads "a surjective setoid map is epic `Sets`".

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_surjective_epic {X Y : SetoidObject} (h : X ~{Sets}~> Y) :
  surjective h → Epic h :=
  concrete_surjective_epic (Con:=Sets_Concrete) h.

Definition Coq_pred_Epic_reflected : Epic (Nat.pred : nat ~{Coq}~> nat) :=
  faithful_reflects_epic Coq_Underlying Nat.pred
    (Sets_surjective_epic (fmap[Coq_Underlying] Nat.pred) Coq_pred_surjective).
