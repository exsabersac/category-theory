Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Limit.

(* Same two as Instance/Proset.v and Instance/Proset/Galois.v: [relation]
   and [PreOrder] below are the stdlib Prop-valued ones, not [crelation]. *)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/power+set
 nLab: https://ncatlab.org/nlab/show/Galois+connection
 nLab: https://ncatlab.org/nlab/show/direct+image
 nLab: https://ncatlab.org/nlab/show/inverse+image
 Wikipedia: https://en.wikipedia.org/wiki/Image_(mathematics)

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** (A) The inclusion order, and the thin category *)

(* Inclusion of Prop-valued subsets.  This IS a [relation] on the carrier,
   which is what [Proset] and [GaloisConnection] require and what the
   proof-relevant carrier cannot supply. *)
Definition subset_le@{o} {X : SetoidObject@{o o}}
  (S T : carrier (Powerset_Prop_obj@{o} X)) : Prop := ∀ x, S x → T x.

Definition subset_le_preorder@{o} (X : SetoidObject@{o o}) :
  PreOrder (@subset_le@{o} X) :=
  {| PreOrder_Reflexive  := fun S x Hx => Hx
   ; PreOrder_Transitive :=
       fun S T U HST HTU x Hx => HTU x (HST x Hx) |}.

(* Mac Lane's "P(U) ... is a preorder under inclusion", as a category. *)
Definition Subsets@{o u} (X : SetoidObject@{o o}) : Category@{o u u} :=
  Proset@{o u} (subset_le_preorder@{o} X).

(* The objects are the subsets and the homs are the inclusions, on the
   nose.  These are equalities between OBJECTS and TYPES, not between
   morphisms: the setoid discipline's sanctioned same-term exception. *)
Example Subsets_obj_carrier@{o u} (X : SetoidObject@{o o}) :
  obj[Subsets@{o u} X] = carrier (Powerset_Prop_obj@{o} X) := eq_refl.

Example Subsets_hom_is_subset_le@{o u} (X : SetoidObject@{o o})
  (S T : Subsets@{o u} X) : (S ~{Subsets@{o u} X}~> T) = subset_le S T
  := eq_refl.

(* Thin, by construction.  [Thin] is Instance/Proset/Galois.v's; the tree
   also has Structure/Thin.v's predicate of the same name, and
   Instance/Proset/Limit.v deliberately introduces none. *)
Definition Subsets_thin@{o u +} (X : SetoidObject@{o o}) :
  Thin (Subsets@{o u} X) := proset_thin (subset_le_preorder@{o} X).

(* Every equivalence of parallel arrows is [True], so nothing downstream
   can be measured at [≈] inside this category. *)
Example subsets_equiv_is_True@{o u} {X : SetoidObject@{o o}}
  {S T : Subsets@{o u} X} (f g : S ~{Subsets@{o u} X}~> T) :
  (f ≈ g) = True := eq_refl.

(* Two [≈]-equal subsets are DISTINCT objects, isomorphic in the category:
   the setoid point of the header, as a construction. *)
Definition subsets_iso_of_equiv@{o u +} {X : SetoidObject@{o o}}
  {S T : carrier (Powerset_Prop_obj@{o} X)} (H : S ≈ T) :
  @Isomorphism (Subsets@{o u} X) S T.
Proof.
  unshelve econstructor.
  - exact (fun x Hx => proj1 (H x) Hx).
  - exact (fun x Hx => proj2 (H x) Hx).
  - exact I.
  - exact I.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** (B), (C) Monotonicity, the Galois connection, the adjunction *)

Section Images.

Universe o so u.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* The direct image is order-preserving.  Opening the truncation is legal
   because the goal is a [Prop]. *)
Lemma image_monotone (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S T →
  subset_le (Powerset_Prop_image@{o} f S) (Powerset_Prop_image@{o} f T).
Proof.
  intros H y Hy Q k.
  refine (Hy Q _); intros [x [Hx Hfx]].
  exact (k (existT _ x (H x Hx, Hfx))).
Qed.

(* The inverse image is order-preserving: there is nothing to open. *)
Lemma preimage_monotone (S T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le S T →
  subset_le (Powerset_Prop_preimage@{o} f S) (Powerset_Prop_preimage@{o} f T).
Proof. intros H x Hx; exact (H (f x) Hx). Qed.

(* Mac Lane's displayed line, left to right: from f_* S subset T infer
   S subset f^* T.  The witness is [x] itself, at [f x], by reflexivity. *)
Lemma image_transpose_to (S : carrier (Powerset_Prop_obj@{o} X))
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le (Powerset_Prop_image@{o} f S) T →
  subset_le S (Powerset_Prop_preimage@{o} f T).
Proof.
  intros H x Hx.
  refine (H (f x) _).
  apply Powerset_squash_intro@{o}; exists x; split;
    [ exact Hx | reflexivity ].
Qed.

(* ... and right to left.  This is where [T]'s own respectfulness is
   spent: the witness [x] gives [T (f x)], and [f x ≈ y] transports it. *)
Lemma image_transpose_from (S : carrier (Powerset_Prop_obj@{o} X))
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le S (Powerset_Prop_preimage@{o} f T) →
  subset_le (Powerset_Prop_image@{o} f S) T.
Proof.
  intros H y Hy.
  refine (Hy (T y) _); intros [x [Hx Hfx]].
  exact (proj1 (@proper_morphism _ _ _ _ T (f x) y Hfx) (H x Hx)).
Qed.

(* THE GALOIS CONNECTION.  All six fields are supplied by name. *)
Definition image_preimage_galois :
  GaloisConnection (@subset_le@{o} X) (@subset_le@{o} Y) :=
  {| gal_l := Powerset_Prop_image@{o} f
   ; gal_r := Powerset_Prop_preimage@{o} f
   ; gal_mono_l := image_monotone
   ; gal_mono_r := preimage_monotone
   ; gal_to   := image_transpose_to
   ; gal_from := image_transpose_from |}.

(* The two functors, and the adjunction: #380 applied, nothing rebuilt. *)
Definition DirectImage : Subsets@{o u} X ⟶ Subsets@{o u} Y :=
  GaloisFunctor_l (subset_le_preorder@{o} X) (subset_le_preorder@{o} Y)
    image_preimage_galois.

Definition InverseImage : Subsets@{o u} Y ⟶ Subsets@{o u} X :=
  GaloisFunctor_r (subset_le_preorder@{o} X) (subset_le_preorder@{o} Y)
    image_preimage_galois.

Definition image_preimage_adjunction : DirectImage ⊣ InverseImage :=
  GaloisAdjunction (subset_le_preorder@{o} X) (subset_le_preorder@{o} Y)
    image_preimage_galois.

(** ** Readbacks for (C) *)

Example direct_image_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[DirectImage] S = Powerset_Prop_image@{o} f S := eq_refl.

Example inverse_image_obj (T : carrier (Powerset_Prop_obj@{o} Y)) :
  fobj[InverseImage] T = Powerset_Prop_preimage@{o} f T := eq_refl.

(* The two functors act as the pre-existing [Sets]-level ones do.  Both
   hold at Leibniz [=] because the two sides are the SAME term -- the
   Functor/Bifunctor.v precedent the donor files cite for their own
   same-term lemmas. *)
Example direct_image_is_Powerset_Prop
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[DirectImage] S = fmap[Powerset_Prop@{o so}] f S := eq_refl.

Example inverse_image_is_Powerset_Prop_op
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  fobj[InverseImage] T
    = fmap[Powerset_Prop_op@{o so}]
        (f : Y ~{(Sets@{o so})^op}~> X) T := eq_refl.

(* #380's backward passage returns the connection this file supplied, at
   Leibniz [=] on the WHOLE record: its six fields are read off the two
   functors and the hom-set isomorphism, all of which were built from
   those very fields. *)
Example image_galois_round_trip :
  GaloisOfAdjunction (subset_le_preorder@{o} X) (subset_le_preorder@{o} Y)
    DirectImage InverseImage image_preimage_adjunction
  = image_preimage_galois := eq_refl.

(** ** (D) The unit and the counit ARE the two inclusions *)

(* Mac Lane's two inequalities, proved directly. *)
Lemma unit_incl (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S
    (Powerset_Prop_preimage@{o} f (Powerset_Prop_image@{o} f S)).
Proof.
  intros x Hx.
  apply Powerset_squash_intro@{o}; exists x; split;
    [ exact Hx | reflexivity ].
Qed.

Lemma counit_incl (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le
    (Powerset_Prop_image@{o} f (Powerset_Prop_preimage@{o} f T)) T.
Proof.
  intros y Hy.
  refine (Hy (T y) _); intros [x [Hx Hfx]].
  exact (proj1 (@proper_morphism _ _ _ _ T (f x) y Hfx) Hx).
Qed.

(* The adjunction's OWN unit and counit, ascribed at those very types.
   The ascription typechecks by conversion alone and says only that the
   unit inhabits the type of [unit_incl]; a Leibniz [unit S = unit_incl S]
   holds at [eq_refl] once the two transposes and the two inclusions above
   are closed [Defined] (measured by audit, out of tree) and is blocked
   here by their [Qed]s, which is why the names say "has the type of" and
   not "is". *)
Definition adj_unit_has_incl_type (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S
    (Powerset_Prop_preimage@{o} f (Powerset_Prop_image@{o} f S)) :=
  @unit _ _ DirectImage InverseImage image_preimage_adjunction S.

Definition adj_counit_has_incl_type
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  subset_le
    (Powerset_Prop_image@{o} f (Powerset_Prop_preimage@{o} f T)) T :=
  @counit _ _ DirectImage InverseImage image_preimage_adjunction T.

End Images.

Arguments image_monotone {X Y} f S T H.
Arguments preimage_monotone {X Y} f S T H.
Arguments image_transpose_to {X Y} f S T H.
Arguments image_transpose_from {X Y} f S T H.
Arguments image_preimage_galois {X Y} f.
Arguments DirectImage {X Y} f.
Arguments InverseImage {X Y} f.
Arguments image_preimage_adjunction {X Y} f.
Arguments unit_incl {X Y} f S.
Arguments counit_incl {X Y} f T.

(* ------------------------------------------------------------------------ *)
(** ** (E) Meets and joins *)

Section Bounds.

Universe o u.

Context {X : SetoidObject@{o o}}.

(* Intersection of an arbitrary family.  A universally quantified [Prop]
   is a [Prop], so no truncation is needed and respectfulness is the
   family's, pointwise. *)
Definition subset_inter {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ∀ i : Idx, S i x) _).
  intros x y Hxy; split; intros H i.
  - exact (proj1 (@proper_morphism _ _ _ _ (S i) x y Hxy) (H i)).
  - exact (proj2 (@proper_morphism _ _ _ _ (S i) x y Hxy) (H i)).
Defined.

(* Union of an arbitrary family.  [ex] here is stdlib's Prop-valued
   existential, NOT the library's Type-valued [sigT]: the members [S i x]
   are already [Prop]s, so the existential lands in [Prop] and NO
   [Powerset_squash] is required -- in contrast with the direct image,
   whose existential quantifies over the carrier. *)
Definition subset_union {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
       (λ x, ex (fun i : Idx => S i x)) _).
  intros x y Hxy; split; intros Hi; destruct Hi as [i Hi]; exists i.
  - exact (proj1 (@proper_morphism _ _ _ _ (S i) x y Hxy) Hi).
  - exact (proj2 (@proper_morphism _ _ _ _ (S i) x y Hxy) Hi).
Defined.

Lemma subset_inter_IsGLB {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  IsGLB (@subset_le@{o} X) S (subset_inter S).
Proof.
  split.
  - intros i x Hx; exact (Hx i).
  - intros n Hn x Hx i; exact (Hn i x Hx).
Defined.

Lemma subset_union_IsLUB {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  IsLUB (@subset_le@{o} X) S (subset_union S).
Proof.
  split.
  - intros i x Hx; exists i; exact Hx.
  - intros n Hn x Hi; destruct Hi as [i Hi]; exact (Hn i x Hi).
Defined.

(* The binary and nullary specializations. *)
Definition subset_meet (S T : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X) := subset_inter (pair_family S T).

Definition subset_join (S T : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X) := subset_union (pair_family S T).

Definition subset_top : carrier (Powerset_Prop_obj@{o} X) :=
  subset_inter (@empty_family _).

Definition subset_bot : carrier (Powerset_Prop_obj@{o} X) :=
  subset_union (@empty_family _).

Lemma subset_meet_l (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le (subset_meet S T) S.
Proof. exact (fst (subset_inter_IsGLB (pair_family S T)) true). Qed.

Lemma subset_meet_r (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le (subset_meet S T) T.
Proof. exact (fst (subset_inter_IsGLB (pair_family S T)) false). Qed.

Lemma subset_meet_greatest (N S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le N S → subset_le N T → subset_le N (subset_meet S T).
Proof.
  intros H1 H2.
  refine (snd (subset_inter_IsGLB (pair_family S T)) N _).
  intros [|]; assumption.
Qed.

Lemma subset_join_l (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S (subset_join S T).
Proof. exact (fst (subset_union_IsLUB (pair_family S T)) true). Qed.

Lemma subset_join_r (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le T (subset_join S T).
Proof. exact (fst (subset_union_IsLUB (pair_family S T)) false). Qed.

Lemma subset_join_least (N S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S N → subset_le T N → subset_le (subset_join S T) N.
Proof.
  intros H1 H2.
  refine (snd (subset_union_IsLUB (pair_family S T)) N _).
  intros [|]; assumption.
Qed.

Lemma subset_top_greatest (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le S subset_top.
Proof. intros x Hx i; destruct i. Qed.

Lemma subset_bot_least (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le subset_bot S.
Proof. intros x Hx; destruct Hx as [i _]; destruct i. Qed.

(* The four structures, and bicompleteness.  Plain [Definition]s, never
   [Instance]s: the donors' own convention for [Proset_Cartesian] and
   [Proset_Terminal]. *)
Definition Subsets_Cartesian : @Cartesian (Subsets@{o u} X) :=
  Proset_Cartesian (subset_le_preorder@{o} X)
    subset_meet subset_meet_l subset_meet_r subset_meet_greatest.

Definition Subsets_Cocartesian : @Cocartesian (Subsets@{o u} X) :=
  Proset_Cocartesian (subset_le_preorder@{o} X)
    subset_join subset_join_l subset_join_r subset_join_least.

Definition Subsets_Terminal : @Terminal (Subsets@{o u} X) :=
  Proset_Terminal (subset_le_preorder@{o} X) subset_top subset_top_greatest.

Definition Subsets_Initial : @Initial (Subsets@{o u} X) :=
  Proset_Initial (subset_le_preorder@{o} X) subset_bot subset_bot_least.

Definition Subsets_HasAllMeets : HasAllMeets (@subset_le@{o} X) :=
  fun Idx S => existT _ (subset_inter S) (subset_inter_IsGLB S).

Definition Subsets_HasAllJoins : HasAllJoins (@subset_le@{o} X) :=
  fun Idx S => existT _ (subset_union S) (subset_union_IsLUB S).

(* THE [Set] INSTANCE, MADE VISIBLE IN THE SOURCE.  These two -- alone
   among the constants of this section -- are about [Subsets] at hom level
   [Set], and the instance is written out rather than inferred.

   RECORDED CORRECTION TO THE REASON.  An earlier revision said the
   [Set] was a PIN: "Both biconditionals route through
   [Proset_Limit]/[DiscreteCat_Functor], and Instance/Discrete.v's
   unannotated declaration of the latter fixes the shape at
   [DiscreteCat@{u Set Set}] while [IsALimit] identifies the shape's
   hom-and-proof universe with the ambient's."  The donor was annotated in
   place at Instance/Discrete.v in the PR "algebraic carriers are sets"
   (2026-09-17), so no [Set] is forced from there any more.  The literal
   [Set] below is therefore now a CHOICE rather than a pin, and has been
   left as it stands: restating these two at a free hom level was not
   attempted or measured in that PR, which changed prose only.  [IsALimit]
   still identifies the shape's hom-and-proof universe with the ambient's,
   which is the constraint that remains. *)
Definition Subsets_Complete : @Complete (Subsets@{o Set} X) :=
  snd (proset_Complete_iff_all_meets (subset_le_preorder@{o} X))
    Subsets_HasAllMeets.

Definition Subsets_Cocomplete : @Cocomplete (Subsets@{o Set} X) :=
  snd (proset_Cocomplete_iff_all_joins (subset_le_preorder@{o} X))
    Subsets_HasAllJoins.

End Bounds.

(* ------------------------------------------------------------------------ *)
(** ** (F) Preservation, directly *)

Section Preservation.

Universe o so.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* Riehl §4.6.3's right-adjoint half, DIRECTLY: a preimage is a
   substitution and a meet is a universal quantifier, so the second clause
   is the transpose of the family's own second clause. *)
Theorem inverse_image_preserves_meets {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsGLB (@subset_le@{o} Y) T m) :
  IsGLB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m).
Proof.
  split.
  - intro i; exact (preimage_monotone f m (T i) (fst H i)).
  - intros n Hn.
    refine (image_transpose_to f n m _).
    refine (snd H (Powerset_Prop_image@{o} f n) _).
    intro i; exact (image_transpose_from f n (T i) (Hn i)).
Qed.

(* Dually, the left-adjoint half, again directly. *)
Theorem direct_image_preserves_joins {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X))
  (m : carrier (Powerset_Prop_obj@{o} X))
  (H : IsLUB (@subset_le@{o} X) S m) :
  IsLUB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_image@{o} f (S i))
    (Powerset_Prop_image@{o} f m).
Proof.
  split.
  - intro i; exact (image_monotone f (S i) m (fst H i)).
  - intros n Hn.
    refine (image_transpose_from f m n _).
    refine (snd H (Powerset_Prop_preimage@{o} f n) _).
    intro i; exact (image_transpose_to f (S i) n (Hn i)).
Qed.

(* THE HALF WITH NO ADJOINT ROUTE HERE.  Riehl proves this from f^*'s own
   RIGHT adjoint -- the dual image -- which is #384's and is not built in
   this file, so it is proved directly instead.  Membership in a join is
   not decomposable, so the argument runs at the level of the ORDER: [m]
   precedes the canonical union of the family, by the family's own second
   clause, and the union does decompose. *)
Theorem inverse_image_preserves_joins {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsLUB (@subset_le@{o} Y) T m) :
  IsLUB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m).
Proof.
  split.
  - intro i; exact (preimage_monotone f (T i) m (fst H i)).
  - intros n Hn x Hx.
    assert (Hu : subset_le m (subset_union T))
      by exact (snd H (subset_union T) (fst (subset_union_IsLUB T))).
    destruct (Hu (f x) Hx) as [i Hi].
    exact (Hn i x Hi).
Qed.

End Preservation.

(* ------------------------------------------------------------------------ *)
(** ** (F) again: the same two statements read off RAPL and LAPC *)

(* These are stated at the [Set] hom level discussed in the header.  An
   earlier revision called that a PIN and attributed it to
   Instance/Discrete.v's unannotated [DiscreteCat_Functor] fixing the shape
   at [DiscreteCat@{u Set Set}]; that donor was annotated in place at its
    in the PR "algebraic carriers are sets" (2026-09-17), so the [Set]
   here is now a choice carried over rather than a pin, and restating it
   was not attempted.  [IsALimit] still identifies the shape's
   hom-and-proof universe with the ambient's; the DIRECT statements above
   carry no such identification, which is why they come first. *)

Section RAPLRoute.

Universe o so.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

Definition inverse_image_preserves_meets_via_RAPL {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsGLB (@subset_le@{o} Y) T m) :
  IsGLB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m) :=
  isalimit_IsGLB (subset_le_preorder@{o} X)
    (InverseImage f ◯ DiscreteCat_Functor (C:=Subsets Y) T) _
    (@preserves_limit _ _ _ _ _
       (right_adjoint_preserves_limit (image_preimage_adjunction f)
          (DiscreteCat_Functor (C:=Subsets Y) T))
       (Proset_Limit (subset_le_preorder@{o} Y) T m H)).

(* The two routes inhabit ONE type: the pair typechecks. *)
Definition inverse_image_meet_routes_agree {Idx : Type}
  (T : Idx → carrier (Powerset_Prop_obj@{o} Y))
  (m : carrier (Powerset_Prop_obj@{o} Y))
  (H : IsGLB (@subset_le@{o} Y) T m) :
  IsGLB (@subset_le@{o} X)
    (fun i => Powerset_Prop_preimage@{o} f (T i))
    (Powerset_Prop_preimage@{o} f m)
  * IsGLB (@subset_le@{o} X)
      (fun i => Powerset_Prop_preimage@{o} f (T i))
      (Powerset_Prop_preimage@{o} f m) :=
  (inverse_image_preserves_meets f T m H,
   inverse_image_preserves_meets_via_RAPL T m H).

(* The colimit side is stated at the CANONICAL join rather than at an
   arbitrary one, because Instance/Proset/Limit.v supplies [Proset_Limit]
   but no [Colimit]-record counterpart, so the [Colimit] this route needs
   is taken from [Subsets_Cocomplete], whose apex is [subset_union]. *)
Definition direct_image_preserves_joins_via_LAPC {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  IsLUB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_image@{o} f (S i))
    (Powerset_Prop_image@{o} f (subset_union S)) :=
  isacolimit_IsLUB (subset_le_preorder@{o} Y)
    (DirectImage f ◯ DiscreteCat_Functor (C:=Subsets X) S) _
    (preserves_colimit
       (left_adjoint_preserves_colimit (image_preimage_adjunction f)
          (DiscreteCat_Functor (C:=Subsets X) S))
       (Subsets_Cocomplete (DiscreteCat Idx)
          (DiscreteCat_Functor (C:=Subsets X) S))).

Definition direct_image_join_routes_agree {Idx : Type}
  (S : Idx → carrier (Powerset_Prop_obj@{o} X)) :
  IsLUB (@subset_le@{o} Y)
    (fun i => Powerset_Prop_image@{o} f (S i))
    (Powerset_Prop_image@{o} f (subset_union S))
  * IsLUB (@subset_le@{o} Y)
      (fun i => Powerset_Prop_image@{o} f (S i))
      (Powerset_Prop_image@{o} f (subset_union S)) :=
  (direct_image_preserves_joins f S (subset_union S)
     (subset_union_IsLUB S),
   direct_image_preserves_joins_via_LAPC S).

End RAPLRoute.

(* ------------------------------------------------------------------------ *)
(** ** (G) Awodey §9.9 Exercise 4: the same thing as monotone maps *)

Section MonotoneReading.

Universe o so u.
Constraint o < so.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

Definition image_MonotoneFun :
  @MonotoneFun _ (@subset_le@{o} X) _ (@subset_le@{o} Y) :=
  {| mono_map  := Powerset_Prop_image@{o} f
   ; mono_pres := image_monotone f |}.

Definition preimage_MonotoneFun :
  @MonotoneFun _ (@subset_le@{o} Y) _ (@subset_le@{o} X) :=
  {| mono_map  := Powerset_Prop_preimage@{o} f
   ; mono_pres := preimage_monotone f |}.

(* The functors agree on OBJECTS on the nose.  The WHOLE records are not
   compared: [Functor_of_monotone] is a [Program Definition] whose three
   law fields are its own opaque obligations while [GaloisFunctor_l]'s are
   its own, so the difference is confined to those three fields and
   touches neither data field. *)
Example direct_image_is_monotone_functor_obj
  (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[Functor_of_monotone (subset_le_preorder@{o} X)
         (subset_le_preorder@{o} Y) image_MonotoneFun] S
    = fobj[DirectImage f] S := eq_refl.

Example inverse_image_is_monotone_functor_obj
  (T : carrier (Powerset_Prop_obj@{o} Y)) :
  fobj[Functor_of_monotone (subset_le_preorder@{o} Y)
         (subset_le_preorder@{o} X) preimage_MonotoneFun] T
    = fobj[InverseImage f] T := eq_refl.

End MonotoneReading.

(* ------------------------------------------------------------------------ *)
(** ** (H) Non-vacuity *)

(* The witnesses are Instance/Sets/Powerset/Universal.v's own
   [powerset_fin2] (the two-element discrete setoid) and [powerset_const0]
   (the constant map at 0), reused rather than rebuilt, together with
   [powerset_sng1] = {1}. *)

Definition powerset_sng0@{o +} :
  carrier (Powerset_Prop_obj@{o} powerset_fin2@{o}) :=
  Powerset_Prop_singleton_pred@{o} (X:=powerset_fin2@{o}) Fin.F1.

(* The unit at {1} is not invertible: its target f^*(f_* {1}) is the WHOLE
   two-element set, since the constant map lands everything at 0. *)
Theorem unit_not_iso@{o so +} :
  subset_le
    (Powerset_Prop_preimage@{o} powerset_const0@{o so}
       (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o}))
    powerset_sng1@{o}
  → False.
Proof.
  intro H.
  refine (H Fin.F1 _ False _).
  - apply Powerset_squash_intro@{o}; exists (Fin.FS Fin.F1); split.
    + apply Powerset_squash_intro@{o}; reflexivity.
    + reflexivity.
  - intro Heq; discriminate Heq.
Qed.

(* The counit at {1} is not invertible either: f^* {1} is EMPTY, so its
   direct image is empty, while {1} is not. *)
Theorem counit_not_iso@{o so +} :
  subset_le powerset_sng1@{o}
    (Powerset_Prop_image@{o} powerset_const0@{o so}
       (Powerset_Prop_preimage@{o} powerset_const0@{o so} powerset_sng1@{o}))
  → False.
Proof.
  intro H.
  refine (H (Fin.FS Fin.F1) _ False _).
  - apply Powerset_squash_intro@{o}; reflexivity.
  - intros [x [Hx _]]; hnf in Hx.
    refine (Hx False _); intro Heq; discriminate Heq.
Qed.

(* And the direct image does NOT preserve meets: {0} and {1} are disjoint,
   so the image of their meet is empty, while the meet of their images
   contains 0.  The [eq_refl] form of this inequality is refuted in
   Test/ProbePowerset382.v. *)
Theorem direct_image_not_meet_preserving@{o so +} :
  Powerset_Prop_image@{o} powerset_const0@{o so}
      (subset_meet powerset_sng0@{o} powerset_sng1@{o})
    ≈ subset_meet
        (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng0@{o})
        (Powerset_Prop_image@{o} powerset_const0@{o so} powerset_sng1@{o})
  → False.
Proof.
  intro H.
  refine (proj2 (H Fin.F1) _ False _).
  - intros [|].
    + apply Powerset_squash_intro@{o}; exists Fin.F1; split.
      * apply Powerset_squash_intro@{o}; reflexivity.
      * reflexivity.
    + apply Powerset_squash_intro@{o}; exists (Fin.FS Fin.F1); split.
      * apply Powerset_squash_intro@{o}; reflexivity.
      * reflexivity.
  - intros [x [Hx _]].
    refine (Hx true False _); intro H0.
    refine (Hx false False _); intro H1.
    rewrite <- H0 in H1; discriminate H1.
Qed.
