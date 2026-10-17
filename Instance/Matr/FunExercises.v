Require Import Coq.ZArith.ZArith.
Require Import Coq.Vectors.Fin.
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Two.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Shapes.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Matr.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 nLab:      https://ncatlab.org/nlab/show/category+of+matrices
 Wikipedia: https://en.wikipedia.org/wiki/Matrix_equivalence
 Wikipedia: https://en.wikipedia.org/wiki/Matrix_similarity

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ---------------------------------------------------------------------- *)
(** ** Powers of an endomorphism *)
(* ---------------------------------------------------------------------- *)

(* The construction is a matrix power when C is [Matr R] -- which is the
   only use made of it below -- but nothing in it is about matrices, so
   it is developed once for an arbitrary endomorphism.  The recursion
   peels a factor off on the LEFT, [A ∘ Aʲ], because that is the
   orientation in which the monoid homomorphism law below is the functor
   composition law read forwards. *)

Section Powers.

Context {C : Category}.

Fixpoint mat_pow {x : C} (A : x ~> x) (k : nat) : x ~> x :=
  match k with
  | O   => id
  | S j => A ∘ mat_pow A j
  end.

Lemma mat_pow_respects {x : C} (A B : x ~> x) (k : nat) :
  A ≈ B → mat_pow A k ≈ mat_pow B k.
Proof.
  intro H.
  induction k as [| j IH]; simpl.
  - reflexivity.
  - rewrite IH.                  (* the tail first: A still occurs under
                                    [mat_pow], which has no [Proper] *)
    now rewrite H.
Qed.

(* The zeroth power is the identity -- by computation, so [reflexivity]
   rather than a unit law. *)
Lemma mat_pow_zero {x : C} (A : x ~> x) : mat_pow A 0%nat ≈ id.
Proof. reflexivity. Qed.

(* The first power is A itself, up to the unit law -- [A ∘ id] and not
   [A] syntactically, which is why this is a lemma and not [eq_refl]. *)
Lemma mat_pow_one {x : C} (A : x ~> x) : mat_pow A 1%nat ≈ A.
Proof. simpl; apply id_right. Qed.

(* Exponents add.  This is the whole homomorphism content of [pow_hom]:
   the induction moves one factor across an associativity. *)
Lemma mat_pow_add {x : C} (A : x ~> x) (j k : nat) :
  mat_pow A (j + k)%nat ≈ mat_pow A j ∘ mat_pow A k.
Proof.
  induction j as [| i IH]; simpl.
  - now rewrite id_left.
  - now rewrite IH, comp_assoc.
Qed.

(** ** The inverse of a commuting square *)

(* If the front square of an isomorphism pair commutes then so does the
   back one.  This is the only content in either direction of the two
   characterizations below: everything else is projection. *)
Lemma iso_square_from {a b a' b' : C} (f : a ~> b) (g : a' ~> b')
  (P : a ≅ a') (Q : b ≅ b') :
  g ∘ to P ≈ to Q ∘ f → f ∘ from P ≈ from Q ∘ g.
Proof.
  intro Hsq.
  rewrite <- (id_left (f ∘ from P)).
  rewrite <- (iso_from_to Q).
  rewrite <- (comp_assoc (from Q) (to Q) (f ∘ from P)).
  rewrite (comp_assoc (to Q) f (from P)).
  rewrite <- Hsq.
  rewrite <- (comp_assoc g (to P) (from P)).
  rewrite (iso_to_from P).
  now rewrite id_right.
Qed.

End Powers.

(* ---------------------------------------------------------------------- *)
(** ** Part one: the walking arrow, and matrix equivalence *)
(* ---------------------------------------------------------------------- *)

Section ArrowIso.

Context {C : Category}.

(* A morphism, as an object of the arrow category.  [Arrow C] is the
   comma (Id ↓ Id), so its objects are triples (a, b, f) and this is
   just the packaging. *)
Definition arrow_pack {a b : C} (f : a ~> b) : @Arrow C := ((a, b); f).

(* Two morphisms are isomorphic in the arrow category exactly when they
   are conjugate by a pair of isomorphisms, one at each end.

   The forward direction is projection: the two components of an
   isomorphism of [Arrow C] are morphisms of C, its two inverse laws are
   componentwise by Construction/Comma.v's hom-equivalence, and the
   commuting square is literally the second projection of the forward
   morphism -- so every field of the two isomorphisms produced below is
   an existing subterm, and the last line is an [exact].  The backward
   direction is where [iso_square_from] is spent, on the square that the
   inverse pair owes. *)
Theorem arrow_iso_iff {a b a' b' : C} (f : a ~> b) (g : a' ~> b') :
  (arrow_pack f ≅[@Arrow C] arrow_pack g)
    ↔ (∃ P : a ≅ a', ∃ Q : b ≅ b', g ∘ to P ≈ to Q ∘ f).
Proof.
  split.
  - intro H.
    destruct (iso_to_from H) as [Ht1 Ht2].
    destruct (iso_from_to H) as [Hf1 Hf2].
    exists (@Build_Isomorphism C a a'
              (fst `1 (to H)) (fst `1 (from H)) Ht1 Hf1).
    exists (@Build_Isomorphism C b b'
              (snd `1 (to H)) (snd `1 (from H)) Ht2 Hf2).
    exact (`2 (to H)).
  - intros [P [Q Hsq]].
    unshelve refine (@Build_Isomorphism (@Arrow C) _ _ _ _ _ _).
    + exact ((to P, to Q); Hsq).
    + exact ((from P, from Q); iso_square_from f g P Q Hsq).
    + split; simpl; apply iso_to_from.
    + split; simpl; apply iso_from_to.
Qed.

End ArrowIso.

(* ---------------------------------------------------------------------- *)
(** ** Matrix equivalence *)
(* ---------------------------------------------------------------------- *)

Section MatrixEquivalence.

Context {R : RigObject}.

(* Two matrices are EQUIVALENT when one is carried to the other by an
   invertible change of basis in the source and, independently, one in
   the target.  The definition is the categorical spelling B P ≈ Q A;
   the classical B ≈ Q A P⁻¹ is [matrix_equivalence_classical]. *)
Definition MatrixEquivalent {n1 m1 n2 m2 : nat}
  (A : n1 ~{Matr R}~> m1) (B : n2 ~{Matr R}~> m2) : Type :=
  ∃ P : n1 ≅[Matr R] n2, ∃ Q : m1 ≅[Matr R] m2,
    B ∘ to P ≈ to Q ∘ A.

(* Mac Lane's answer for the walking arrow: isomorphic objects of the
   arrow category of [Matr R] are exactly the equivalent matrices.  No
   universe restriction: the arrow category is a comma category, and
   nothing here forms a functor category. *)
Theorem matrix_equivalence_iso {n1 m1 n2 m2 : nat}
  (A : n1 ~{Matr R}~> m1) (B : n2 ~{Matr R}~> m2) :
  (arrow_pack A ≅[@Arrow (Matr R)] arrow_pack B) ↔ MatrixEquivalent A B.
Proof. exact (arrow_iso_iff A B). Qed.

(* The classical form, for a fixed pair of changes of basis: the square
   B P ≈ Q A and the solved form B ≈ Q A P⁻¹ say the same thing. *)
Lemma matrix_equivalence_classical {n1 m1 n2 m2 : nat}
  (A : n1 ~{Matr R}~> m1) (B : n2 ~{Matr R}~> m2)
  (P : n1 ≅[Matr R] n2) (Q : m1 ≅[Matr R] m2) :
  (B ∘ to P ≈ to Q ∘ A) ↔ (B ≈ to Q ∘ A ∘ from P).
Proof.
  split; intro H.
  - rewrite <- H.
    rewrite <- (comp_assoc B (to P) (from P)).
    rewrite (iso_to_from P).
    now rewrite id_right.
  - rewrite H.
    rewrite <- (comp_assoc (to Q ∘ A) (from P) (to P)).
    rewrite (iso_from_to P).
    now rewrite id_right.
Qed.

End MatrixEquivalence.

(* ---------------------------------------------------------------------- *)
(** ** The same statement read in the functor category [_2, C] *)
(* ---------------------------------------------------------------------- *)

(* Mac Lane writes the exercise about the functor category, so the
   reading is supplied -- by TRANSPORT along Theory/Shapes.v's
   comparison rather than by a second proof.  [Arrow_of_Fun] carries a
   functor F to [arrow_pack (arrow_of F)] definitionally, so the forward
   leg is [fobj_iso] followed by [arrow_iso_iff]; the backward leg goes
   out through [Fun_of_Arrow], whose value at [Arrow_of_Fun F] is
   [Walk (arrow_of F)], and returns along [Walk_arrow_of_iso].

   The universe restriction [Category@{o Set Set}] is inherited verbatim
   from [Two_Fun_Arrow] and is disclosed in the header. *)

Section TwoFunIso.

Universe o.

Context {C : Category@{o Set Set}}.

Theorem two_fun_iso_iff (F G : _2 ⟶ C) :
  (@Isomorphism ([_2, C]) F G)
    ↔ (∃ P : F TwoX ≅ G TwoX, ∃ Q : F TwoY ≅ G TwoY,
          arrow_of G ∘ to P ≈ to Q ∘ arrow_of F).
Proof.
  split.
  - intro H.
    apply arrow_iso_iff.
    exact (fobj_iso Arrow_of_Fun F G H).
  - intro H.
    refine (iso_compose (Walk_arrow_of_iso G)
              (iso_compose _ (iso_sym (Walk_arrow_of_iso F)))).
    exact (fobj_iso Fun_of_Arrow _ _ (snd (arrow_iso_iff _ _) H)).
Qed.

End TwoFunIso.

(* ---------------------------------------------------------------------- *)
(** ** Part two: the delooped free monoid, and matrix similarity *)
(* ---------------------------------------------------------------------- *)

(* EVERYTHING BELOW IS PINNED, and by three mechanisms rather than one:
   [MonHom M N] takes its two monoids at ONE universe instance, and so
   does [Functor_Setoid] -- so already [pow_hom]'s type and the round
   trip [functor_of_endo (endo_of_functor F) ≈ F] require C's hom and
   proof universes to be [Set], before any functor category is
   mentioned; the functor category then requires it a third time.  The
   powers themselves ([mat_pow] and its four laws above), the
   arrow-category characterization, and matrix equivalence are free of
   the restriction. *)

(* Two lemmas that need nothing from the delooping live OUTSIDE the
   pinned section, at an arbitrary category: the fess audit measured
   that keeping them inside cost them a needless [Set] pin. *)
Section Intertwining.

Context {C : Category}.

(* A morphism S intertwining A with B intertwines every power with the
   corresponding power; the induction is the same associativity shuffle
   as [mat_pow_add].  This is what makes a natural transformation
   between two of these functors a single unconstrained morphism
   together with ONE equation instead of a family of them. *)
Lemma pow_intertwine {x y : C} (A : x ~> x) (B : y ~> y) (S : x ~> y)
  (H : S ∘ A ≈ B ∘ S) (k : nat) :
  S ∘ mat_pow A k ≈ mat_pow B k ∘ S.
Proof.
  induction k as [| j IH]; simpl.
  - now rewrite id_left, id_right.
  - rewrite comp_assoc, H.
    rewrite <- comp_assoc, IH.
    now rewrite comp_assoc.
Qed.

(* An endomorphism conjugate to an identity is an identity: the
   similarity class of [id] is a singleton.  This is what makes the
   negative witnesses below cheap, and it is the categorical content of
   "only the identity matrix is similar to the identity matrix". *)
Lemma similar_to_id {x y : C} (B : y ~> y) :
  (∃ P : x ≅ y, to P ∘ id ≈ B ∘ to P) → B ≈ id.
Proof.
  intros [P H].
  rewrite id_right in H.
  assert (Heq : B ∘ (to P ∘ from P) ≈ to P ∘ from P).
  { rewrite (comp_assoc B (to P) (from P)).
    now rewrite <- H. }
  rewrite (iso_to_from P) in Heq.
  rewrite id_right in Heq.
  exact Heq.
Qed.

End Intertwining.

Section Similarity.

Universe u.

Context {C : Category@{u Set Set}}.

(** *** The dictionary: endomorphisms versus functors out of B (ℕ, +) *)

(* Powers of A, as a homomorphism from the free monoid on one generator
   into the endomorphism monoid of x.  [mon_map_unit] is [mat_pow_zero]
   and [mon_map_op] is [mat_pow_add]; nothing else is required, which is
   the sense in which (ℕ, +) is free on one generator. *)
Program Definition pow_hom {x : C} (A : x ~> x) :
  MonHom Nat_Plus (hom_monoid C x) := {|
  mon_map := mat_pow A
|}.
(* [mon_map_respects] does not appear as an obligation: the source
   setoid is [nat_setoid], whose `≈` is Leibniz equality, so instance
   resolution discharges it -- the same economy Construction/Deloop.v
   records for [Nat_Plus]'s own [mon_op_respects]. *)
Next Obligation. intros x A; reflexivity. Qed.
Next Obligation. intros x A j k; exact (mat_pow_add A j k). Qed.

(* The functor named by an endomorphism, through the spine of
   Construction/Deloop/Functors.v.  Its object action is constantly x
   and its arrow action is [mat_pow A]. *)
Definition functor_of_endo {x : C} (A : x ~> x) : Deloop Nat_Plus ⟶ C :=
  functor_of_hom_monoid x (pow_hom A).

(* ...and the endomorphism named by a functor: the image of the
   generator.  (The objects of [Deloop Nat_Plus] must be given
   explicitly: its hom is the same setoid at every pair, so a natural
   number carries no information about the endpoints.) *)
Definition endo_of_functor (F : Deloop Nat_Plus ⟶ C) : F ttt ~> F ttt :=
  @fmap _ _ F ttt ttt 1%nat.

(* FREENESS, as a theorem: the image of k is the k-th power of the image
   of the generator.  The base case is [fmap_id] -- the identity of
   [Deloop Nat_Plus] IS the natural number 0 -- and the step is
   [fmap_comp] at [1 ∘ k], the composite in the delooping being [1 + k],
   which is [S k] by computation. *)
Lemma fmap_is_pow (F : Deloop Nat_Plus ⟶ C) (k : nat) :
  @fmap _ _ F ttt ttt k ≈ mat_pow (endo_of_functor F) k.
Proof.
  induction k as [| j IH]; simpl.
  - exact (@fmap_id _ _ F ttt).
  - rewrite <- IH.
    exact (@fmap_comp _ _ F ttt ttt ttt 1%nat j).
Qed.

(* One round trip, up to the unit law only. *)
Lemma endo_of_functor_of_endo {x : C} (A : x ~> x) :
  endo_of_functor (functor_of_endo A) ≈ A.
Proof. exact (mat_pow_one A). Qed.

(* The other, at the strength Instance/Cat.v's hom-equivalence supplies:
   a natural isomorphism with identity components, which is what
   [Functor_Setoid] asks for.  A strict equality of functor records is
   NOT available and is not claimed -- the two records differ in how
   [fmap] is presented, exactly as in Theory/Shapes.v's
   [Walk_arrow_of_strict] discussion. *)
Lemma functor_of_endo_round (F : Deloop Nat_Plus ⟶ C) :
  functor_of_endo (endo_of_functor F) ≈ F.
Proof.
  exists (fun z => match z as z0 return (F ttt ≅ F z0) with
                   | ttt => iso_id
                   end).
  intros [] [] k; simpl.
  rewrite id_left, id_right.
  symmetry; exact (fmap_is_pow F k).
Qed.

(** *** Naturality collapses to the generator *)

(* An intertwiner IS a natural transformation, its single component
   repeated at the single object ([pow_intertwine], hoisted above the
   section, supplies naturality at every power from the one square). *)
Program Definition transform_of_intertwiner {x y : C}
  (A : x ~> x) (B : y ~> y) (S : x ~> y) (H : S ∘ A ≈ B ∘ S) :
  functor_of_endo A ⟹ functor_of_endo B := {|
  transform := fun _ => S
|}.
Next Obligation.
  intros x y A B S H z w k; simpl.
  symmetry; exact (pow_intertwine A B S H k).
Qed.
Next Obligation.
  intros x y A B S H z w k; simpl.
  exact (pow_intertwine A B S H k).
Qed.

(* Mac Lane's answer for the delooped free monoid, at the level of an
   arbitrary category: the functors named by two endomorphisms are
   isomorphic exactly when the endomorphisms are conjugate.

   Forward, the isomorphism's component at the single object is the
   conjugator, its two inverse laws are that component's, and the
   conjugation equation is naturality AT THE GENERATOR -- the only
   instance of naturality used.  Backward, the transformation is built
   from the conjugator by [transform_of_intertwiner], its inverse from
   the inverse conjugator through the square [iso_square_from] derives,
   and the two isomorphism laws are checked at the single object. *)
Theorem endo_iso_iff {x y : C} (A : x ~> x) (B : y ~> y) :
  (@Isomorphism ([Deloop Nat_Plus, C])
     (functor_of_endo A) (functor_of_endo B))
    ↔ (∃ P : x ≅ y, to P ∘ A ≈ B ∘ to P).
Proof.
  split.
  - intro H.
    exists (@Build_Isomorphism C x y
              (transform (to H) ttt) (transform (from H) ttt)
              (iso_to_from H ttt) (iso_from_to H ttt)).
    pose proof (naturality (to H) ttt ttt 1%nat) as Hn.
    simpl in Hn.
    rewrite !id_right in Hn.
    now symmetry.
  - intros [P Hsq].
    unshelve refine (@Build_Isomorphism ([Deloop Nat_Plus, C]) _ _ _ _ _ _).
    + exact (transform_of_intertwiner A B (to P) Hsq).
    + unshelve refine (transform_of_intertwiner B A (from P) _).
      symmetry.
      apply iso_square_from.
      now symmetry.
    + intros [ ]; simpl; apply iso_to_from.
    + intros [ ]; simpl; apply iso_from_to.
Qed.

End Similarity.

(* ---------------------------------------------------------------------- *)
(** ** Matrix similarity *)
(* ---------------------------------------------------------------------- *)

Section MatrixSimilarity.

Context {R : RigObject@{Set Set Set}}.

(* The two legs of the dictionary at [Matr R], named as the exercise
   names them: a functor out of B (ℕ, +) IS a square matrix. *)
Definition square_of_functor (F : Deloop Nat_Plus ⟶ Matr R) :
  F ttt ~{Matr R}~> F ttt := endo_of_functor F.

Definition functor_of_square {n : nat} (A : n ~{Matr R}~> n) :
  Deloop Nat_Plus ⟶ Matr R := functor_of_endo A.

(* Two square matrices are SIMILAR when a single invertible change of
   basis conjugates one into the other.  Categorical spelling P A ≈ B P;
   the classical B ≈ P A P⁻¹ is [matrix_similarity_classical]. *)
Definition MatrixSimilar {n n' : nat}
  (A : n ~{Matr R}~> n) (B : n' ~{Matr R}~> n') : Type :=
  ∃ P : n ≅[Matr R] n', to P ∘ A ≈ B ∘ to P.

(* The headline: isomorphic objects of [[Deloop Nat_Plus, Matr R]] are
   exactly the similar square matrices. *)
Theorem matrix_similarity_iso {n n' : nat}
  (A : n ~{Matr R}~> n) (B : n' ~{Matr R}~> n') :
  (@Isomorphism ([Deloop Nat_Plus, Matr R])
     (functor_of_square A) (functor_of_square B))
    ↔ MatrixSimilar A B.
Proof. exact (endo_iso_iff A B). Qed.

Lemma matrix_similarity_classical {n n' : nat}
  (A : n ~{Matr R}~> n) (B : n' ~{Matr R}~> n')
  (P : n ≅[Matr R] n') :
  (to P ∘ A ≈ B ∘ to P) ↔ (B ≈ to P ∘ A ∘ from P).
Proof.
  split; intro H.
  - rewrite H.
    rewrite <- (comp_assoc B (to P) (from P)).
    rewrite (iso_to_from P).
    now rewrite id_right.
  - rewrite H.
    rewrite <- (comp_assoc (to P ∘ A) (from P) (to P)).
    rewrite (iso_from_to P).
    now rewrite id_right.
Qed.

(* Similar matrices are equivalent -- take Q := P -- and the converse
   is refuted by the witnesses below. *)
Lemma similar_implies_equivalent {n n' : nat}
  (A : n ~{Matr R}~> n) (B : n' ~{Matr R}~> n') :
  MatrixSimilar A B → MatrixEquivalent A B.
Proof.
  intros [P H].
  exists P, P.
  now symmetry.
Qed.

End MatrixSimilarity.

(* Mac Lane's part one written where he writes it -- over [_2] rather
   than over the arrow category.  [Walk A] is the functor that names A,
   and [arrow_of (Walk A)] is A back again definitionally, so this is
   [two_fun_iso_iff] read at that functor and costs no proof.  The
   price is a universe restriction on R's FIRST TWO universes only
   (the [_2] side pins object and hom levels to [Set]; the fess audit
   measured that the third stays free, which is why this corollary
   lives in its own section rather than the similarity section, whose
   [RigObject@{Set Set Set}] context would over-pin it), and it is why
   the [Arrow] form is the one stated for an arbitrary rig. *)
Section MatrixEquivalenceFun.

Universe q.

(* The instance is written [@{q Set Set}], not [@{Set Set q}]: since the PR
   "algebraic carriers are sets" (2026-09-17) the record's AUXILIARY universe
   -- the one bounding the [rig_prop] field's own sort, which carries the
   [Set+1] -- is the FIRST argument rather than the third.  The roles are
   unchanged: the carrier and proof levels are still pinned at [Set] and the
   third is still free. *)
Context {R : RigObject@{q Set Set}}.

Corollary matrix_equivalence_iso_Fun {n1 m1 n2 m2 : nat}
  (A : n1 ~{Matr R}~> m1) (B : n2 ~{Matr R}~> m2) :
  (@Isomorphism ([_2, Matr R]) (Walk A) (Walk B)) ↔ MatrixEquivalent A B.
Proof. exact (two_fun_iso_iff (Walk A) (Walk B)). Qed.

End MatrixEquivalenceFun.

(* ---------------------------------------------------------------------- *)
(** ** The universe restriction is not empty *)
(* ---------------------------------------------------------------------- *)

(* Every rig in the tree lives at the restricted universes, so the
   similarity theorem applies to all of them. *)
Definition Nat_Rig_pinned : RigObject@{Set Set Set} := Nat_Rig.
Definition Bool_Rig_pinned : RigObject@{Set Set Set} := Bool_Rig.
Definition Int_Rig_pinned : RigObject@{Set Set Set} := Int_Rig.

(* ---------------------------------------------------------------------- *)
(** ** Witnesses over the integers *)
(* ---------------------------------------------------------------------- *)

(* A two-element case analysis, so that entrywise equations between 2 × 2
   matrices are discharged by computation.  [Fin.t 0] is empty, which is
   what closes the third branch. *)
Lemma fin2_rect (P : Fin.t 2%nat → Type)
  (h1 : P Fin.F1) (h2 : P (Fin.FS Fin.F1)) : ∀ i, P i.
Proof.
  intro i.
  pattern i; apply (Fin.caseS' i); [ exact h1 |].
  intro j; pattern j; apply (Fin.caseS' j); [ exact h2 |].
  intro k; inversion k.
Qed.

(* Every equation between 2 × 2 integer matrices below is closed, so
   the four entries reduce; [Local] keeps the tactic out of the exported
   name space. *)
Local Ltac entrywise :=
  intro; match goal with
         | [ i : Fin.t 2%nat |- _ ] => pattern i; apply fin2_rect
         end;
  intro; match goal with
         | [ j : Fin.t 2%nat |- _ ] => pattern j; apply fin2_rect
         end;
  reflexivity.

(* The position of an index, so a small matrix can be written as a
   table.  (Instance/Matr/Determinant.v's [fidx] is the same function;
   it is re-declared here rather than requiring that file, whose
   1600-line determinant development nothing below consumes.) *)
Definition fin_index {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (Fin.to_nat i).

Definition zmat22 (a b c d : Z) : 2%nat ~{Matr Int_Rig}~> 2%nat :=
  fun i j => match fin_index i, fin_index j with
             | O, O => a
             | O, _ => b
             | _, O => c
             | _, _ => d
             end.

(* The three matrices used below: the two rank-one diagonal idempotents
   and the transposition. *)
Definition zmat_e11 : 2%nat ~{Matr Int_Rig}~> 2%nat := zmat22 1 0 0 0.
Definition zmat_e22 : 2%nat ~{Matr Int_Rig}~> 2%nat := zmat22 0 0 0 1.
Definition zmat_swap : 2%nat ~{Matr Int_Rig}~> 2%nat := zmat22 0 1 1 0.

(* The transposition is its own inverse, entry by entry. *)
Program Definition zswap_iso : 2%nat ≅[Matr Int_Rig] 2%nat := {|
  to   := zmat_swap;
  from := zmat_swap
|}.
Next Obligation. entrywise. Qed.
Next Obligation. entrywise. Qed.

(* Both products are [[0,0],[1,0]], as computation checks at the one
   entry that is not zero.  (Matrix ENTRIES, so [=] rather than [≈]:
   these are elements of the rig's carrier, the convertibility
   exception, and the equation between the matrices themselves is the
   [≈] of [zmat_e11_similar_e22] below.) *)
Example zswap_e11_entry :
  (@compose (Matr Int_Rig) 2%nat 2%nat 2%nat zmat_swap zmat_e11)
    (Fin.FS Fin.F1) Fin.F1 = 1%Z := eq_refl.

Example ze22_zswap_entry :
  (@compose (Matr Int_Rig) 2%nat 2%nat 2%nat zmat_e22 zmat_swap)
    (Fin.FS Fin.F1) Fin.F1 = 1%Z := eq_refl.

(* diag(1,0) and diag(0,1) are similar, conjugated by the
   transposition -- so they are also equivalent, and the two functor
   categories agree on this pair. *)
Theorem zmat_e11_similar_e22 : MatrixSimilar zmat_e11 zmat_e22.
Proof.
  exists zswap_iso.
  entrywise.
Qed.

Corollary zmat_e11_equivalent_e22 : MatrixEquivalent zmat_e11 zmat_e22.
Proof. exact (similar_implies_equivalent _ _ zmat_e11_similar_e22). Qed.

(* And the corresponding isomorphisms, in the two functor categories. *)
Definition zmat_e11_e22_arrow_iso :
  arrow_pack zmat_e11 ≅[@Arrow (Matr Int_Rig)] arrow_pack zmat_e22 :=
  snd (matrix_equivalence_iso zmat_e11 zmat_e22) zmat_e11_equivalent_e22.

Definition zmat_e11_e22_deloop_iso :
  @Isomorphism ([Deloop Nat_Plus, Matr Int_Rig])
    (functor_of_square zmat_e11) (functor_of_square zmat_e22) :=
  snd (matrix_similarity_iso zmat_e11 zmat_e22) zmat_e11_similar_e22.

Definition zmat_e11_e22_two_iso :
  @Isomorphism ([_2, Matr Int_Rig]) (Walk zmat_e11) (Walk zmat_e22) :=
  snd (matrix_equivalence_iso_Fun zmat_e11 zmat_e22)
    zmat_e11_equivalent_e22.

(** *** The two relations are genuinely different *)

(* The shear [[1,1],[0,1]] is invertible, so it is equivalent to the
   identity; but it is not the identity, so by [similar_to_id] it is not
   similar to it.  This is the separation the exercise turns on: over
   the walking arrow the two matrices are isomorphic, and over the
   delooped free monoid they are not. *)
Definition zmat_shear : 2%nat ~{Matr Int_Rig}~> 2%nat := zmat22 1 1 0 1.
Definition zmat_shear_inv : 2%nat ~{Matr Int_Rig}~> 2%nat :=
  zmat22 1 (-1) 0 1.

Program Definition zshear_iso : 2%nat ≅[Matr Int_Rig] 2%nat := {|
  to   := zmat_shear;
  from := zmat_shear_inv
|}.
Next Obligation. entrywise. Qed.
Next Obligation. entrywise. Qed.

Example zshear_inverse_entry :
  (@compose (Matr Int_Rig) 2%nat 2%nat 2%nat zmat_shear zmat_shear_inv)
    Fin.F1 (Fin.FS Fin.F1) = 0%Z := eq_refl.

Theorem zmat_id_equivalent_shear :
  MatrixEquivalent (@id (Matr Int_Rig) 2%nat) zmat_shear.
Proof.
  exists (iso_sym zshear_iso), (@iso_id (Matr Int_Rig) 2%nat).
  entrywise.
Qed.

(* The shear moves the (0,1) entry, so it is not the identity matrix. *)
Lemma zmat_shear_not_id : zmat_shear ≈ @id (Matr Int_Rig) 2%nat → False.
Proof.
  intro H.
  pose proof (H Fin.F1 (Fin.FS Fin.F1)) as H1.
  simpl in H1.
  discriminate H1.
Qed.

Theorem zmat_id_not_similar_shear :
  MatrixSimilar (@id (Matr Int_Rig) 2%nat) zmat_shear → False.
Proof.
  intro H.
  exact (zmat_shear_not_id (similar_to_id zmat_shear H)).
Qed.

(* Packaged: one pair of matrices, isomorphic over the walking arrow and
   not isomorphic over the delooped free monoid. *)
Definition equivalence_is_weaker_than_similarity :
  MatrixEquivalent (@id (Matr Int_Rig) 2%nat) zmat_shear
  * (MatrixSimilar (@id (Matr Int_Rig) 2%nat) zmat_shear → False) :=
  (zmat_id_equivalent_shear, zmat_id_not_similar_shear).

(* The cheapest negative of all, at one dimension: the identity and the
   zero matrix are not similar, because 1 and 0 are distinct integers. *)
Definition zmat_zero : 1%nat ~{Matr Int_Rig}~> 1%nat := fun _ _ => 0%Z.

Lemma zmat_zero_not_id : zmat_zero ≈ @id (Matr Int_Rig) 1%nat → False.
Proof.
  intro H.
  pose proof (H Fin.F1 Fin.F1) as H1.
  simpl in H1.
  discriminate H1.
Qed.

Theorem zmat_id_not_similar_zero :
  MatrixSimilar (@id (Matr Int_Rig) 1%nat) zmat_zero → False.
Proof.
  intro H.
  exact (zmat_zero_not_id (similar_to_id zmat_zero H)).
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Acceptance tests *)
(* ---------------------------------------------------------------------- *)

(* The object action of the functor named by a square matrix is the
   dimension, definitionally -- Mac Lane's "an object of [Matr_K]^(B N)
   is a square matrix" read as an equation.  (Objects, so [=] rather than
   [≈]: this is the convertibility exception.) *)
Example functor_of_square_obj (n : nat) (A : n ~{Matr Int_Rig}~> n) :
  functor_of_square A ttt = n := eq_refl.

(* And its arrow action at the generator is the matrix back again, up to
   the unit law, which is [endo_of_functor_of_endo]. *)
Example square_of_functor_of_square (n : nat)
  (A : n ~{Matr Int_Rig}~> n) : square_of_functor (functor_of_square A) ≈ A.
Proof. exact (endo_of_functor_of_endo A). Qed.

(* Powers compute: the transposition has order two, so its odd powers
   are itself and its even powers the identity, read here at the (0,1)
   entry.  (Entries again, hence [=].) *)
Example zswap_pow_3 :
  mat_pow zmat_swap 3%nat Fin.F1 (Fin.FS Fin.F1) = 1%Z := eq_refl.

Example zswap_pow_2 :
  mat_pow zmat_swap 2%nat Fin.F1 (Fin.FS Fin.F1) = 0%Z := eq_refl.

(* ...and the functor named by the transposition sends k to that power,
   definitionally -- the freeness of (ℕ, +) made computational. *)
Example functor_of_square_fmap_3 :
  @fmap _ _ (functor_of_square zmat_swap) ttt ttt 3%nat
    Fin.F1 (Fin.FS Fin.F1) = 1%Z := eq_refl.
