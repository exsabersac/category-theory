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

(** Sets is Cauchy complete: every idempotent splits. *)

(*
 nLab:      https://ncatlab.org/nlab/show/split+idempotent
 Wikipedia: https://en.wikipedia.org/wiki/Karoubi_envelope

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* The splitting 对象 idempotent e X: sub-setoid elements
 held fixed e, compared under X's 等价 underlying elements
 (the fixedness proofs irrelevant). （已译） *)
Program Definition sets_split_obj {X : SetoidObject} (e : X ~{Sets}~> X) :
  SetoidObject := {|
  carrier := ∃ a : X, e a ≈ a;
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation.
  intros X e.
  equivalence.
Qed.

(* 相关说明。 （已译） *)
Lemma sets_split_fixed {X : SetoidObject} (e : X ~{Sets}~> X)
      (H : Idempotent e) (a : X) : e (e a) ≈ e a.
Proof.
  exact (@idem Sets X e H a).
Qed.

(* 相关说明。 （已译） *)
Program Definition sets_split_r {X : SetoidObject} (e : X ~{Sets}~> X)
        (H : Idempotent e) : X ~{Sets}~> sets_split_obj e := {|
  morphism := fun a => (e a; sets_split_fixed e H a)
|}.
Next Obligation.
  intros X e H a b Hab; simpl.
  now rewrite Hab.
Qed.

(* 相关说明。 （已译） *)
Program Definition sets_split_s {X : SetoidObject} (e : X ~{Sets}~> X) :
  sets_split_obj e ~{Sets}~> X := {|
  morphism := fun p => `1 p
|}.
Next Obligation.
  intros X e p q Hpq.
  exact Hpq.
Qed.

(* The splitting of e through its fixed-point object. *)
Program Definition sets_split {X : SetoidObject} (e : X ~{Sets}~> X)
        (H : Idempotent e) :
  @SplitIdempotent Sets X (sets_split_obj e) := {|
  split_idem   := e;
  split_idem_r := sets_split_r e H;
  split_idem_s := sets_split_s e
|}.
Next Obligation.
  (* s ∘ r ≈ e : pointwise, the underlying element of (e a; _) is e a *)
  intros X e H a; simpl.
  reflexivity.
Qed.
Next Obligation.
  (* r ∘ s ≈ id : pointwise on (a; h), the goal e a ≈ a is exactly h *)
  intros X e H p; simpl.
  exact (`2 p).
Qed.

(* 相关说明。 （已译） *)
#[export] Instance Sets_IdempotentsSplit : IdempotentsSplit Sets.
Proof.
  constructor.
  intros X e H.
  exists (sets_split_obj e).
  exists (sets_split e H).
  reflexivity.
Defined.

(* Since Sets has split idempotents, its embedding into its own Karoubi
   envelope is full, faithful and essentially surjective, hence an
   equivalence of categories: Sets is equivalent to Split(Sets). *)
Corollary Sets_Cauchy : EquivalenceOfCategories (@Karoubi_Embed Sets).
Proof.
  exact (cauchy_complete_embed_equiv Sets_IdempotentsSplit).
Defined.
