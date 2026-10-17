(** * Set-indexed products of categories *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Two.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   nLab:      https://ncatlab.org/nlab/show/product+category

   本文件给出积（分量）构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The product category *)

Program Definition PiCat {I : Type} (C : I → Category) : Category := {|
  obj := ∀ i : I, C i;
  hom := fun f g => ∀ i : I, f i ~> g i;
  homset := fun f g =>
    {| equiv := fun η θ => ∀ i : I, η i ≈ θ i |};
  id := fun f i => id;
  compose := fun f g h η θ i => η i ∘ θ i
|}.
Next Obligation.
  intros I C f g; constructor.
  - intros η i; reflexivity.
  - intros η θ Hηθ i; symmetry; apply Hηθ.
  - intros η θ ρ H1 H2 i.
    transitivity (θ i); [ apply H1 | apply H2 ].
Qed.
Next Obligation.
  intros I C f g h η η' Hη θ θ' Hθ i.
  exact (compose_respects _ _ (Hη i) _ _ (Hθ i)).
Qed.
Next Obligation.
  intros I C f g η i; exact (id_left (η i)).
Qed.
Next Obligation.
  intros I C f g η i; exact (id_right (η i)).
Qed.
Next Obligation.
  intros I C f g h k η θ ρ i; exact (comp_assoc (η i) (θ i) (ρ i)).
Qed.
Next Obligation.
  intros I C f g h k η θ ρ i; exact (comp_assoc_sym (η i) (θ i) (ρ i)).
Qed.

(** ** Projections *)

Program Definition PiCat_Proj {I : Type} (C : I → Category) (i : I) :
  PiCat C ⟶ C i := {|
  fobj := fun f => f i;
  fmap := fun f g η => η i
|}.
Next Obligation.
  intros I C i f g η θ Hηθ; exact (Hηθ i).
Qed.
Next Obligation.
  intros I C i f; reflexivity.
Qed.
Next Obligation.
  intros I C i f g h η θ; reflexivity.
Qed.

(** ** The universal property *)

(* Pairing: a family of functors into the components assembles into one
   functor into the product, componentwise. *)
Program Definition PiCat_Pair {I : Type} {C : I → Category}
  {D : Category} (R : ∀ i : I, D ⟶ C i) : D ⟶ PiCat C := {|
  fobj := fun d i => R i d;
  fmap := fun x y h i => fmap[R i] h
|}.
Next Obligation.
  intros I C D R x y h h' Hh i.
  exact (fmap_respects _ _ _ _ Hh).
Qed.
Next Obligation.
  intros I C D R x i; exact (@fmap_id _ _ (R i) x).
Qed.
Next Obligation.
  intros I C D R x y z h h' i; exact (@fmap_comp _ _ (R i) _ _ _ h h').
Qed.

(* The triangle: projecting the pairing IS the component, definitionally
   on both objects and arrows, so the natural isomorphism is the
   identity family. *)
Lemma PiCat_Pair_Proj {I : Type} {C : I → Category}
  {D : Category} (R : ∀ i : I, D ⟶ C i) (i : I) :
  PiCat_Proj C i ◯ PiCat_Pair R ≈ R i.
Proof.
  simpl; exists (fun d => iso_id).
  intros x y h; simpl.
  rewrite id_left, id_right; reflexivity.
Qed.

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma PiCat_ump_unique {I : Type} {C : I → Category} {D : Category}
  (R : ∀ i : I, D ⟶ C i) (H : D ⟶ PiCat C) :
  (∀ i : I, PiCat_Proj C i ◯ H ≈ R i) →
  H ≈ PiCat_Pair R.
Proof.
  intros HP; simpl.
  unshelve eexists.
  - intro d.
    unshelve refine
      (@Build_Isomorphism (PiCat C) (H d) (fun i => R i d)
         (fun i => to (projT1 (HP i) d))
         (fun i => from (projT1 (HP i) d)) _ _).
    + intro i; exact (iso_to_from (projT1 (HP i) d)).
    + intro i; exact (iso_from_to (projT1 (HP i) d)).
  - intros x y h i; simpl.
    exact (projT2 (HP i) x y h).
Qed.

(* The whole universal property, bundled: existence is the pairing with
   its triangle, uniqueness the lemma above. *)
Lemma PiCat_ump {I : Type} {C : I → Category} {D : Category}
  (R : ∀ i : I, D ⟶ C i) :
  ∃! F : D ⟶ PiCat C, ∀ i : I, PiCat_Proj C i ◯ F ≈ R i.
Proof.
  unshelve eapply Build_Unique.
  - exact (PiCat_Pair R).
  - exact (fun i => PiCat_Pair_Proj R i).
  - intros H HP; symmetry; exact (PiCat_ump_unique R H HP).
Qed.

(* F6-style sanity: the product over a constant two-member family
   projects a choice function to its component, by computation. *)
Example PiCat_witness :
  fobj[PiCat_Proj (fun _ : bool => _2) true] (fun _ => TwoX) = TwoX
  := eq_refl.
