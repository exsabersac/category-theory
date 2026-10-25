Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Equivalence.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Karoubi.
Require Import Category.Construction.Karoubi.Universal.

Generalizable All Variables.

(** Sets is Cauchy complete: every idempotent splits. / 集合是柯西完备的：每个幂等元都可以分解。 *)

(*
 nLab:      https://ncatlab.org/nlab/show/Cauchy+complete+category
 nLab:      https://ncatlab.org/nlab/show/split+idempotent
 Wikipedia: https://en.wikipedia.org/wiki/Karoubi_envelope

 An idempotent setoid map e : X ~> X in [Sets] — pointwise,
 e (e a) ≈ e a — splits through the sub-setoid of its fixed points,

 { a : X & e a ≈ a },  compared under X's ≈ on underlying elements.

 The retraction X ~> Y sends a to e a, a fixed point by idempotency; the
 section Y ~> X is the underlying-element projection.  Section after
 retraction on X is a ↦ e a, which is e on the nose; retraction after
 section carries (a; h) to (e a; _), equal to (a; h) in Y because
 e a ≈ a is exactly h.  Both splitting laws thus hold pointwise.

 Packaged through the [IdempotentsSplit] class of
 Construction/Karoubi/Universal.v this makes [Sets] Cauchy complete
 ([Sets_IdempotentsSplit]), whence by [cauchy_complete_embed_equiv] the
 embedding of [Sets] into its own Karoubi envelope is an equivalence of
 categories ([Sets_Cauchy]). 

 --------
 nLab：       https://ncatlab.org/nlab/show/Cauchy+complete+category 
 nLab：       https://ncatlab.org/nlab/show/split+idempotent 
 维基百科：  https://en.wikipedia.org/wiki/Karoubi_envelope 

 在 [Sets] 中，一个幂等集类映射 e : X ~> X — 对每一点而言，
 e (e a) ≈ e a — 通过其不动点子集类分裂，

 { a : X & e a ≈ a }，在底层元素上根据 X 的 ≈ 进行比较。

 收缩映射 X ~> Y 将 a 送到 e a，由于幂等性它是一个不动点；
 截面映射 Y ~> X 是底层元素投影。在 X 上先收缩再截面得到 a ↦ e a，即完全等于 e；
 先截面再收缩将 (a; h) 送到 (e a; _)，在 Y 中等于 (a; h)，因为 e a ≈ a 恰好是 h。两条分裂律因此都对每一点成立。通过  [IdempotentsSplit] 类的 Construction/Karoubi/Universal.v 打包，这使得  [Sets] 是柯西完备的 ( [Sets_IdempotentsSplit] )，因此根据  [cauchy_complete_embed_equiv]，  [Sets] 嵌入其自身的 Karoubi 包络是范畴等价的 ( [Sets_Cauchy] )。
*)

#[local] Obligation Tactic := idtac.

(*
 The splitting object for an idempotent e on X: the sub-setoid of elements
 held fixed by e, compared under X's equivalence on underlying elements
 (the fixedness proofs are irrelevant). 

 --------
 对 X 上的幂等元 e 的分裂对象：由被 e 保持不变的元素组成的子集合体，根据 X 在底层元素上的等价关系进行比较（固定性证明是无关的）。
*)
Program Definition sets_split_obj {X : SetoidObject} (e : X ~{Sets}~> X) :
  SetoidObject := {|
  carrier := ∃ a : X, e a ≈ a;
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation.
  intros X e.
  equivalence.
Qed.

(* The idempotent law of e, read pointwise through the hom-setoid of Sets: e a is a fixed point of e. / 幂等律 e，通过集合的同态集合从逐点角度解读： e a 是 e 的一个不动点。 *)
Lemma sets_split_fixed {X : SetoidObject} (e : X ~{Sets}~> X)
      (H : Idempotent e) (a : X) : e (e a) ≈ e a.
Proof.
  exact (@idem Sets X e H a).
Qed.

(* The retraction X ~> Y: send a to the fixed point e a. / 收缩 X ~> Y：将 a 发送到固定点 e a。 *)
Program Definition sets_split_r {X : SetoidObject} (e : X ~{Sets}~> X)
        (H : Idempotent e) : X ~{Sets}~> sets_split_obj e := {|
  morphism := fun a => (e a; sets_split_fixed e H a)
|}.
Next Obligation.
  intros X e H a b Hab; simpl.
  now rewrite Hab.
Qed.

(* The section Y ~> X: the underlying element, discarding fixedness. / Y ~> X 部分：底层元素，舍弃固定性。 *)
Program Definition sets_split_s {X : SetoidObject} (e : X ~{Sets}~> X) :
  sets_split_obj e ~{Sets}~> X := {|
  morphism := fun p => `1 p
|}.
Next Obligation.
  intros X e p q Hpq.
  exact Hpq.
Qed.

(* The splitting of e through its fixed-point object. / 通过其不动点对象对 e 的分裂。 *)
Program Definition sets_split {X : SetoidObject} (e : X ~{Sets}~> X)
        (H : Idempotent e) :
  @SplitIdempotent Sets X (sets_split_obj e) := {|
  split_idem   := e;
  split_idem_r := sets_split_r e H;
  split_idem_s := sets_split_s e
|}.
Next Obligation.
  (* s ∘ r ≈ e : pointwise, the underlying element of (e a; _) is e a / s ∘ r ≈ e：逐点来说，(e a; _) 的底层元素是 e a *)
  intros X e H a; simpl.
  reflexivity.
Qed.
Next Obligation.
  (* r ∘ s ≈ id : pointwise on (a; h), the goal e a ≈ a is exactly h / r ∘ s ≈ id ：在 (a; h) 上逐点，目标 e a ≈ a 正好是 h *)
  intros X e H p; simpl.
  exact (`2 p).
Qed.

(* Every idempotent of Sets splits: Sets is Cauchy complete. The splitting chosen for e has e itself as the split idempotent, so agreement with e is reflexivity. / 集合的每个幂等元都可以分解：集合是柯西完备的。为 e 选择的分解使 e 本身成为分解后的幂等元，因此与 e 的一致性是自反的。 *)
#[export] Instance Sets_IdempotentsSplit : IdempotentsSplit Sets.
Proof.
  constructor.
  intros X e H.
  exists (sets_split_obj e).
  exists (sets_split e H).
  reflexivity.
Defined.

(*
 Since Sets has split idempotents, its embedding into its own Karoubi
 envelope is full, faithful and essentially surjective, hence an
 equivalence of categories: Sets is equivalent to Split(Sets). 

 --------
 由于集合（Sets）具有可分裂幂等子，集合嵌入其自身的卡鲁比包（Karoubi envelope）是充满（full）、忠实（faithful）且本质上是满射（essentially surjective）的，因此是范畴等价的：集合（Sets）与 Split(Sets) 是等价的。
*)
Corollary Sets_Cauchy : EquivalenceOfCategories (@Karoubi_Embed Sets).
Proof.
  exact (cauchy_complete_embed_equiv Sets_IdempotentsSplit).
Defined.
