(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Subcategory.
Require Import Category.Functor.Diagonal.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Rng.

Generalizable All Variables.

#[local] Set Transparent Obligations.

(*
   nLab: https://ncatlab.org/nlab/show/category
   nLab: https://ncatlab.org/nlab/show/under+category
   nLab: https://ncatlab.org/nlab/show/associative+algebra
   Wikipedia: https://en.wikipedia.org/wiki/Associative_algebra

   本节说明 Algebras 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The direct definition *)

(* 相关说明。 （已译） *)
Record KAlgObject (K : CRng) := {
  kalg_ring : RingObject;
  kalg_comm : ∀ a b, rig_mul kalg_ring a b ≈ rig_mul kalg_ring b a;
  kalg_unit : `1 K ~{Rng}~> kalg_ring
}.

Arguments kalg_ring {K} _.
Arguments kalg_comm {K} _ _ _.
Arguments kalg_unit {K} _.

(*
   本节说明 Algebras 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition KAlgHom {K : CRng} (A B : KAlgObject K) : Type :=
  ∃ f : kalg_ring A ~{Rng}~> kalg_ring B, kalg_unit B ≈ f ∘ kalg_unit A.

(* Two K-algebra 态射 equal underlying ring
 homomorphisms are; triangle 证明 irrelevant. This matches
 [Coslice]'s convention (Construction/Slice.v). （已译） *)
Program Definition KAlgHom_Setoid {K : CRng} (A B : KAlgObject K) :
  Setoid (KAlgHom A B) := {|
  equiv := fun f g => `1 f ≈ `1 g
|}.
Next Obligation.
  constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a; transitivity (`1 g a); [ apply Hfg | apply Hgh ].
Defined.

Lemma kalg_id_triangle {K : CRng} (A : KAlgObject K) :
  kalg_unit A ≈ id ∘ kalg_unit A.
Proof. now rewrite id_left. Defined.

Lemma kalg_comp_triangle {K : CRng} {A B C : KAlgObject K}
      (f : KAlgHom B C) (g : KAlgHom A B) :
  kalg_unit C ≈ (`1 f ∘ `1 g) ∘ kalg_unit A.
Proof.
  rewrite <- comp_assoc.
  rewrite <- (`2 g).
  exact (`2 f).
Defined.

Program Definition KAlg (K : CRng) : Category := {|
  obj     := KAlgObject K;
  hom     := @KAlgHom K;
  homset  := @KAlgHom_Setoid K;
  id      := fun A => (id; kalg_id_triangle A);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; kalg_comp_triangle f g)
|}.
Next Obligation.
  intros f1 f2 Hf g1 g2 Hg a.
  transitivity (rig_map (`1 f1) (rig_map (`1 g2) a)).
  - apply (proper_morphism (rig_map (`1 f1))), Hg.
  - apply Hf.
Defined.

(*
   本节说明 Algebras 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example kalg_comm_is_CRng_membership (K : CRng) (A : KAlgObject K) :
  sobj Rng CRng_Sub (kalg_ring A) := kalg_comm A.

(** ** The comparison *)

(*
   本节说明 Algebras 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition KAlg_to_Coslice (K : CRng) : KAlg K ⟶ Coslice CRng K := {|
  fobj := fun A => ((kalg_ring A; kalg_comm A); (kalg_unit A; I));
  fmap := fun A B f => ((`1 f; I); `2 f)
|}.

(* 相关说明。 （已译） *)
Program Definition Coslice_to_KAlg (K : CRng) : Coslice CRng K ⟶ KAlg K := {|
  fobj := fun x => {| kalg_ring := `1 (`1 x);
                      kalg_comm := `2 (`1 x);
                      kalg_unit := `1 (`2 x) |};
  fmap := fun x y g => (`1 (`1 g); `2 g)
|}.

(** ** The round trips *)

(* KAlg → Coslice → KAlg 恒等 对象 DEFINITIONALLY: the
 round trip rebuilds record three projections, records
 have eta here. （已译） *)
Example KAlg_Coslice_round_obj (K : CRng) (A : KAlg K) :
  fobj[Coslice_to_KAlg K] (fobj[KAlg_to_Coslice K] A) = A := eq_refl.

(*
   本节说明 Algebras 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Coslice_KAlg_round_obj (K : CRng) (x : Coslice CRng K) :
  fobj[KAlg_to_Coslice K] (fobj[Coslice_to_KAlg K] x) = x.
Proof.
  destruct x as [[R comm] [u t]]; destruct t; reflexivity.
Defined.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma KAlg_Coslice_round_hom (K : CRng) (A B : KAlg K) (f : A ~> B) :
  fmap[Coslice_to_KAlg K] (fmap[KAlg_to_Coslice K] f) ≈ f.
Proof. intro a; reflexivity. Qed.

Lemma Coslice_KAlg_round_hom (K : CRng) (x y : Coslice CRng K) (g : x ~> y) :
  `1 (`1 (fmap[KAlg_to_Coslice K] (fmap[Coslice_to_KAlg K] g))) ≈ `1 (`1 g).
Proof. reflexivity. Qed.

(** ** The isomorphism *)

(*
   本节说明函子、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition KAlg_Coslice_strict_iso (K : CRng) :
  KAlg K ≅[StrictCat] Coslice CRng K.
Proof.
  unshelve refine (@Build_Isomorphism StrictCat (KAlg K) (Coslice CRng K)
    (KAlg_to_Coslice K) (Coslice_to_KAlg K) _ _).
  - (* to ∘ from ≈ id, on the coslice *)
    exists (Coslice_KAlg_round_obj K).
    intros x y f.
    destruct x as [[Rx cx] [ux tx]], y as [[Ry cy] [uy ty]].
    destruct tx, ty.
    simpl.
    reflexivity.
  - (* from ∘ ≈ id, algebras; 对象 component [eq_refl] （已译） *)
    exists (fun _ => eq_refl).
    intros A B f; simpl.
    reflexivity.
Defined.

(* The two composites, named: each strictly equal 恒等
 函子. These round trips at FUNCTOR level, 对象- and
 hom-level statements above being components. （已译） *)
Definition KAlg_Coslice_to_from (K : CRng) :
  @equiv _ (@homset StrictCat (Coslice CRng K) (Coslice CRng K))
    (@compose StrictCat _ _ _ (KAlg_to_Coslice K) (Coslice_to_KAlg K))
    (@id StrictCat (Coslice CRng K)) :=
  iso_to_from (KAlg_Coslice_strict_iso K).

Definition KAlg_Coslice_from_to (K : CRng) :
  @equiv _ (@homset StrictCat (KAlg K) (KAlg K))
    (@compose StrictCat _ _ _ (Coslice_to_KAlg K) (KAlg_to_Coslice K))
    (@id StrictCat (KAlg K)) :=
  iso_from_to (KAlg_Coslice_strict_iso K).

(*
   本节说明函子、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition KAlg_Coslice_iso (K : CRng) : KAlg K ≅[Cat] Coslice CRng K :=
  @Build_Isomorphism Cat (KAlg K) (Coslice CRng K)
    (KAlg_to_Coslice K) (Coslice_to_KAlg K)
    (strict_equiv_implies_fun_equiv _ _ (KAlg_Coslice_to_from K))
    (strict_equiv_implies_fun_equiv _ _ (KAlg_Coslice_from_to K)).

(* 相关说明。 （已译） *)
Definition KAlg_Comma_iso (K : CRng) : KAlg K ≅[Cat] (=(K) ↓ Id) :=
  iso_compose (Comma_Coslice CRng K) (KAlg_Coslice_iso K).

(** ** Witnesses *)

(* ℤ is a ℤ-algebra by way of the identity structure map. *)
Definition Int_KAlg : KAlgObject Int_CRng :=
  Build_KAlgObject Int_CRng Int_Ring Int_Ring_commutative (@id Rng Int_Ring).

Example Int_KAlg_unit_computes :
  rig_map (kalg_unit Int_KAlg) 3%Z = 3%Z := eq_refl.

(* ℚ is commutative, hence an object of [CRng]... *)
Lemma Q_Ring_commutative : ∀ a b, rig_mul Q_Ring a b ≈ rig_mul Q_Ring b a.
Proof. intros a b; simpl; apply Qmult_comm. Qed.

Definition Q_CRng : CRng := (Q_Ring; Q_Ring_commutative).

(* ...and a ℤ-algebra by the inclusion ℤ → ℚ, a genuinely non-identity
   structure map: Instance/Rng.v's [ZtoQ_not_surjective] shows it misses
   1/2, so this algebra is not its own base ring in disguise. *)
Definition Q_KAlg : KAlgObject Int_CRng :=
  Build_KAlgObject Int_CRng Q_Ring Q_Ring_commutative ZtoQ.

Example Q_KAlg_unit_computes :
  rig_map (kalg_unit Q_KAlg) 3%Z = inject_Z 3 := eq_refl.

Corollary Q_KAlg_unit_not_surjective :
  (∀ q : Q, exists z : Z, rig_map (kalg_unit Q_KAlg) z == q)%Q → False.
Proof. exact ZtoQ_not_surjective. Qed.

(* A non-identity morphism of ℤ-algebras: the inclusion itself. *)
Lemma Int_to_Q_triangle : kalg_unit Q_KAlg ≈ ZtoQ ∘ kalg_unit Int_KAlg.
Proof. now rewrite id_right. Qed.

Definition Int_to_Q_KAlg : Int_KAlg ~{KAlg Int_CRng}~> Q_KAlg :=
  (ZtoQ; Int_to_Q_triangle).

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Z_KAlg (A : CRng) : KAlgObject Int_CRng :=
  Build_KAlgObject Int_CRng (`1 A) (`2 A) (rng_from_Z (`1 A)).

(* 相关说明。 （已译） *)
Lemma Z_KAlg_unit_unique (A : KAlgObject Int_CRng) (z : Z) :
  rig_map (kalg_unit A) z ≈ rig_map (kalg_unit (Z_KAlg (kalg_ring A; kalg_comm A))) z.
Proof. apply rng_from_Z_unique. Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Q_KAlg_is_canonical (z : Z) :
  rig_map (kalg_unit Q_KAlg) z ≈ rig_map (kalg_unit (Z_KAlg Q_CRng)) z.
Proof. exact (Z_KAlg_unit_unique Q_KAlg z). Qed.

(* 相关说明。 （已译） *)
Example Q_KAlg_in_Coslice :
  fobj[KAlg_to_Coslice Int_CRng] Q_KAlg = ((Q_Ring; Q_Ring_commutative); (ZtoQ; I))
  := eq_refl.
