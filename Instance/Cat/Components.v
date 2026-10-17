(** * The components functor and its right adjoint *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Roof.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Construction.Comma.Special.

Generalizable All Variables.

(*
 Book:      Riehl, "Category Theory in Context", Dover 2016, §1.5,
 nLab:      https://ncatlab.org/nlab/show/connected+component
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 nLab:      https://ncatlab.org/nlab/show/adjoint+string
 nLab:      https://ncatlab.org/nlab/show/reflective+subcategory
 nLab:      https://ncatlab.org/nlab/show/Cat
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   本文件给出 Cat 相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** §1. The discrete category on a setoid: two small lemmas *)

(* An [≈] between two points of [DiscreteSetoidCat S] IS an arrow between
   them, so it is half of an isomorphism and symmetry supplies the other
   half.  Both inverse laws are equations in a thin category and are
   discharged by the ambient obligation tactic.  It is used three times
   below -- at the two [fmap_respects]-shaped obligations of §2 and §3,
   and again in §7's [Cat_Disc_not_skeletal] -- which is why it is
   factored out. *)
Program Definition disc_setoid_iso {A : Type} (S : Setoid A) {x y : A}
  (e : @equiv A S x y) : @Isomorphism (DiscreteSetoidCat S) x y :=
  {| to := e ; from := symmetry e |}.

(* The converse collapse: a zig-zag in [DiscreteSetoidCat S] contracts to
   a single [≈].  This is the only induction in the file, and it is the
   whole reason the backward transpose exists -- the [Sets]-morphism it
   produces must respect [ZigZag], and this is what turns a chain into
   the [≈] the target setoid wants.  Each of the three cases is one law
   of [S]: reflexivity, transitivity, and transitivity after symmetry. *)
Lemma zigzag_setoid_contract {A : Type} (S : Setoid A)
  (x y : DiscreteSetoidCat S) : ZigZag x y → @equiv A S x y.
Proof.
  intro s; induction s.
  - reflexivity.
  - now transitivity y.
  - now transitivity y; [ symmetry |].
Qed.

(** ** §2. The discrete functor Sets ⟶ Cat *)

(* The arrow action.  Both the object and the arrow part are READ OFF a
   [Sets]-morphism: [fobj] is its underlying function and [fmap] is its
   [proper_morphism] certificate, since an arrow of the discrete category
   on a setoid is a proof of [≈].  All three functor laws are equations
   in a thin category and cost nothing. *)
Program Definition Cat_Disc_map {A B : Sets} (f : A ~> B) :
  DiscreteSetoidCat (is_setoid A) ⟶ DiscreteSetoidCat (is_setoid B) :=
  {| fobj := f
   ; fmap := fun x y (e : x ≈ y) => proper_morphism f x y e |}.

(* The functor.  Its ONE obligation is [fmap_respects]: two pointwise
   [≈]-equal [Sets]-morphisms induce naturally isomorphic functors, the
   component at [a] being [disc_setoid_iso] of the hypothesis at [a] and the
   naturality clause being [True].  [fmap_id] and [fmap_comp] are
   discharged by the ambient tactic for the same reason. *)
Program Definition Cat_Disc : Sets ⟶ Cat := {|
  fobj := fun A => DiscreteSetoidCat (is_setoid A)
; fmap := fun _ _ f => Cat_Disc_map f
|}.
Next Obligation.
  intros f g H.
  exists (fun a => disc_setoid_iso (is_setoid y) (H a)); intros; exact I.
Defined.

(* Four readbacks, all [eq_refl].  The second and third are the ones a
   consumer needs: the objects of the discrete category ARE the carrier
   and its homs ARE the setoid's own relation. *)
Example cat_disc_obj (A : Sets) :
  fobj[Cat_Disc] A = DiscreteSetoidCat (is_setoid A) := eq_refl.

Example cat_disc_obj_carrier (A : Sets) :
  obj[fobj[Cat_Disc] A] = carrier A := eq_refl.

Example cat_disc_hom (A : Sets) (x y : carrier A) :
  (x ~{fobj[Cat_Disc] A}~> y) = (x ≈ y) := eq_refl.

Example cat_disc_fmap (A B : Sets) (f : A ~> B) (a : carrier A) :
  fobj[fmap[Cat_Disc] f] a = f a := eq_refl.

(** ** §3. The transposition *)

(* Forward: a map on components extends to a functor.  Its object action
   IS the given map -- [carrier (pi0 C)] is [obj[C]] by
   Theory/Connected/Components.v's [pi0_carrier] -- and its arrow action
   is the map's own respectfulness certificate applied to the one-step
   chain [hom_zigzag f].  So no data is invented in this direction; the
   two ingredients are already present in the argument. *)
Program Definition pi0_to {C : Cat} {A : Sets}
  (h : fobj[Pi0] C ~{Sets}~> A) : C ~{Cat}~> fobj[Cat_Disc] A :=
  {| fobj := h
   ; fmap := fun x y (f : x ~> y) =>
       @proper_morphism _ _ _ _ h x y (hom_zigzag f) |}.

(* Backward: a functor into a discrete category restricts to a map on
   components.  Its underlying function is the functor's object action;
   the content is the ONE obligation, which is where [zigzag_fmap] and
   [zigzag_setoid_contract] are spent -- transport the chain along the functor,
   then contract it in the thin target. *)
Program Definition pi0_from {C : Cat} {A : Sets}
  (F : C ~{Cat}~> fobj[Cat_Disc] A) : fobj[Pi0] C ~{Sets}~> A :=
  {| morphism := fobj[F] |}.
Next Obligation.
  intros x y s.
  exact (zigzag_setoid_contract (is_setoid A) _ _ (zigzag_fmap F s)).
Defined.

(* The hom-setoid isomorphism.  Two obligations, both [Proper] fields;
   the two round trips are discharged by the ambient tactic, and §4
   records that the second of them is vacuous on arrows. *)
Program Definition pi0_adj_iso (C : Cat) (A : Sets) :
  @Isomorphism Sets
    {| carrier := @hom Sets (fobj[Pi0] C) A
     ; is_setoid := @homset Sets (fobj[Pi0] C) A |}
    {| carrier := @hom Cat C (fobj[Cat_Disc] A)
     ; is_setoid := @homset Cat C (fobj[Cat_Disc] A) |} :=
  {| to   := {| morphism := fun h => @pi0_to C A h |}
   ; from := {| morphism := fun F => @pi0_from C A F |} |}.
Next Obligation.
  intros h k H.
  exists (fun a => disc_setoid_iso (is_setoid A) (H a)); intros; exact I.
Defined.
Next Obligation. intros F G H a; exact (to (`1 H a)). Defined.

(** ** §4. The adjunction *)

(* Mac Lane's leftmost adjunction, packaged.  ZERO obligations: the two
   naturality clauses [Build_Adjunction'] asks for land in [Cat] at a
   thin target, where [≈] between functors is a family of isomorphisms
   together with a [True], and the object families agree definitionally. *)
Program Definition Components_Disc_Adjunction : Pi0 ⊣ Cat_Disc :=
  Build_Adjunction' pi0_adj_iso _ _.

Example pi0_adj_to_at (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) (x : C) :
  fobj[to (pi0_adj_iso C A) h] x = h x := eq_refl.

Example pi0_adj_from_at (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) (x : C) :
  from (pi0_adj_iso C A) F x = F x := eq_refl.

(* The unit and the counit are both the identity function -- on the nose.
   The unit is [C ⟶ Cat_Disc (Pi0 C)], the projection of an object to its
   component, and the carrier of [pi0 C] IS [obj[C]], so there is nothing
   for it to do on objects. *)
Example pi0_unit_is_id (C : Cat) (x : C) :
  fobj[@unit _ _ _ _ Components_Disc_Adjunction C] x = x := eq_refl.

Example pi0_counit_is_id (A : Sets) (a : carrier A) :
  @counit _ _ _ _ Components_Disc_Adjunction A a = a := eq_refl.

(* NEGATIVE 1 (CONVERSION).  The [Sets]-side round trip is not strict.
   Two controls localize the failure to a single field: the value at each
   point returns on the nose, and so does the whole [morphism] FIELD, so
   -- [SetoidMorphism] being a primitive-projection record with eta --
   what differs is exactly [proper_morphism], which [pi0_from] rebuilds. *)
Fail Example pi0_rt_from_to_strict (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) :
  from (pi0_adj_iso C A) (to (pi0_adj_iso C A) h) = h := eq_refl.

Example pi0_rt_from_to_at (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) (x : carrier (fobj[Pi0] C)) :
  from (pi0_adj_iso C A) (to (pi0_adj_iso C A) h) x = h x := eq_refl.

Example pi0_rt_from_to_fn (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) :
  @morphism _ _ _ _ (from (pi0_adj_iso C A) (to (pi0_adj_iso C A) h))
    = @morphism _ _ _ _ h := eq_refl.

(* NEGATIVE 2 and NEGATIVE 3 (CONVERSION).  The [Cat]-side round trip is
   not strict either, and the cause is DIFFERENT: the object action does
   return on the nose (control), the ARROW action does not, and it cannot,
   because an arrow of [DiscreteSetoidCat S] is a PROOF of [≈] and the
   round trip manufactures a fresh one through [zigzag_setoid_contract]. *)
Fail Example pi0_rt_to_from_strict (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) :
  to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F) = F := eq_refl.

Example pi0_rt_to_from_obj (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) :
  fobj[to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F)] = fobj[F]
  := eq_refl.

Fail Example pi0_rt_to_from_map (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) (x y : C) (f : x ~> y) :
  fmap[to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F)] f = fmap[F] f
  := eq_refl.

(* ... and the [≈] that replaces it is VACUOUS, which the next two
   commands say together rather than separately: the first holds, and the
   second shows it holds of ANY two parallel arrows, so it verifies
   nothing about the round trip.  The content of [iso_from_to] here is
   the object family, which is [pi0_rt_to_from_obj]. *)
Example pi0_rt_to_from_map_equiv (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) (x y : C) (f : x ~> y) :
  fmap[to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F)] f ≈ fmap[F] f
  := I.

Example cat_disc_hom_trivial (A : Sets) (x y : carrier A)
  (p q : x ~{fobj[Cat_Disc] A}~> y) : p ≈ q := I.

(** ** §5. Cat_Disc is fully faithful; Sets is reflective in Cat *)

(* [Full] asks only for a section of [fmap] with no functoriality, and
   here the section is the reverse reading of §2: the underlying function
   of the recovered [Sets]-morphism is the functor's object action and
   its certificate is the functor's arrow action.  Its ONE obligation is
   that certificate, supplied by a one-step script rather than as a field
   for the reason Theory/Connected/Components.v records at
   [sets_quot_proj] -- [Proper (equiv ==> equiv) fobj[F]] is CONVERTIBLE
   with the type of [fmap[F]], but the elaborator does not unfold
   [Proper] and [respectful] during unification, so the field assignment
   is rejected.  (Measured here too, at exactly that spot.)  [fmap_sur]
   is discharged by the ambient tactic. *)
Program Definition Cat_Disc_Full : Full Cat_Disc := {|
  prefmap := fun A B F => {| morphism := fobj[F] |}
|}.
Next Obligation. intros x y e; exact (fmap[F] e). Defined.

Definition Cat_Disc_Faithful : Faithful Cat_Disc.
Proof.
  unshelve econstructor.
  intros A B f g H a; exact (to (`1 H a)).
Defined.

(* Mac Lane's "the components of a discrete category are its objects",
   in the form that carries the most: the COUNIT is an isomorphism.  With
   [Cat_Disc_Full] and [Cat_Disc_Faithful] this exhibits [Sets] as a reflective
   subcategory of [Cat] with reflector π₀ -- the inclusion is the right
   adjoint and is fully faithful.

   Both legs are the identity function; the two obligations are the
   respectfulness of the backward leg (an [≈] IS an arrow, hence a
   one-step chain) and the [ZigZag x x] the second round trip asks for,
   which is the empty chain. *)
Program Definition pi0_counit_iso (A : Sets) :
  @Isomorphism Sets (fobj[Pi0] (fobj[Cat_Disc] A)) A :=
  {| to   := @counit _ _ _ _ Components_Disc_Adjunction A
   ; from := {| morphism := fun a : carrier A => a |} |}.
Next Obligation.
  intros x y e.
  exact (@hom_zigzag (DiscreteSetoidCat (is_setoid A)) x y e).
Defined.
Next Obligation. exact (zz_nil _). Defined.

Example pi0_counit_iso_to (A : Sets) (a : carrier A) :
  to (pi0_counit_iso A) a = a := eq_refl.

Example pi0_counit_iso_from (A : Sets) (a : carrier A) :
  from (pi0_counit_iso A) a = a := eq_refl.

(** ** §6. Non-vacuity: π₀ genuinely forgets *)

(* The constant functors out of the terminal category.  [Roof] is the
   walking span [RNeg ← RZero → RPos]: it is CONNECTED
   ([Roof_Connected], Structure/Groupoid/Connected.v), so π₀ merges
   its three objects, while [RoofHom RNeg RPos] is EMPTY
   ([RNeg_RPos_absurd], Instance/Roof.v), so [Roof] itself does not.
   That gap is what both refutations below exploit. *)
Program Definition roof_pt@{o h p ru rh} (r : Roof@{ru rh}) :
  _1@{o h p} ⟶ Roof@{ru rh} :=
  {| fobj := fun _ => r ; fmap := fun _ _ _ => id[r] |}.

Example roof_objs_distinct : RNeg <> RPos.
Proof. discriminate. Qed.

Example roof_pi0_merges :
  @equiv _ (fobj[Pi0] Roof) RNeg RPos := Roof_Connected RNeg RPos.

(* π₀ is not faithful: the two constant functors [_1 ⟶ Roof] at [RNeg]
   and at [RPos] have the SAME image under π₀ (both objects lie in one
   component) and are not [≈] in [Cat], since that would give an
   isomorphism [RNeg ≅ RPos] whose forward leg is an arrow that does not
   exist. *)
Theorem Pi0_not_Faithful : Faithful Pi0 → False.
Proof.
  intro H.
  destruct (@fmap_inj _ _ Pi0 H _1 Roof (roof_pt RNeg) (roof_pt RPos)
              (fun _ => Roof_Connected RNeg RPos)) as [iso _].
  exact (RNeg_RPos_absurd (to (iso ttt))).
Qed.

(* ... and the unit is not full, so the adjunction is not an equivalence.
   [Full]'s [prefmap] is a bare section, so applying it to the zig-zag
   arrow that exists upstairs manufactures the missing [Roof]-arrow
   directly.  Read the conclusion at exactly that strength: nothing here
   rules out an equivalence between [Roof] and some discrete category by
   OTHER maps, and no essential-surjectivity statement about [Cat_Disc]
   is proved. *)
Theorem unit_not_Full :
  Full (@unit _ _ _ _ Components_Disc_Adjunction Roof) → False.
Proof.
  intro H.
  exact (RNeg_RPos_absurd
           (@prefmap _ _ _ H RNeg RPos (Roof_Connected RNeg RPos))).
Qed.

(** ** §7. Why the right adjoint is not the plain discrete category *)

(* [bool] under the everywhere-true setoid.  This is the witness for both
   refutations: it makes [id] and [negb] equivalent as [Sets]-morphisms
   while keeping [true] and [false] Leibniz-distinct. *)
Program Definition blur_bool : Sets := {|
  carrier   := bool
; is_setoid := {| equiv := fun _ _ => True |}
|}.

Program Definition blur_bool_negb : blur_bool ~{Sets}~> blur_bool :=
  {| morphism := negb |}.

Example blur_bool_id_equiv_negb : id[blur_bool] ≈ blur_bool_negb := fun _ => I.

(* The arrow action a carrier-based discrete functor would have to have:
   objects the CARRIER, arrows Leibniz equalities, so the action on
   arrows is [f_equal]. *)
Program Definition disc_carrier_map@{o so dh dp} {A B : Sets@{o so}}
  (f : A ~> B) :
  DiscreteCat@{o dh dp} (carrier A) ⟶ DiscreteCat@{o dh dp} (carrier B) :=
  {| fobj := f ; fmap := fun x y (e : x = y) => f_equal f e |}.

(* REFUTATION.  Its [fmap_respects] field is FALSE.  This is the theorem
   that separates the two [Discrete]s of Mac Lane's string: over [Sets]
   the right adjoint cannot be Instance/Discrete.v's [DiscreteCat] on the
   carrier, which is what the sibling development's [StrictCat_Disc] is
   built from. *)
Theorem DiscreteCat_carrier_not_functorial :
  (∀ (A B : Sets) (f g : A ~> B), f ≈ g →
     @equiv _ (@homset Cat (DiscreteCat (carrier A))
                           (DiscreteCat (carrier B)))
       (disc_carrier_map f) (disc_carrier_map g)) → False.
Proof.
  intro H.
  destruct (H blur_bool blur_bool id[blur_bool] blur_bool_negb (fun _ => I))
    as [iso _].
  exact (Bool.diff_true_false (to (iso true))).
Qed.

(* The general form, which says WHAT the obstruction is rather than
   exhibiting one instance of it: a functor [Sets ⟶ Cat] whose objects
   carry the points of the setoid injectively and naturally cannot have
   SKELETAL fibres.  [Kskel] is Theory/Skeleton.v's [Skeletal]
   predicate ([∀ x y : C, x ≅ y → x = y]) spelled out at each fibre;
   that module is not required here, so the hypothesis is written out
   rather than imported.

   Read the argument: [id ≈ negb] gives a natural isomorphism between the
   two induced functors; evaluating it at the point [true] and rewriting
   both ends by naturality turns it into [pt true ≅ pt false];
   skeletality makes that a Leibniz equality and injectivity finishes. *)
Theorem no_skeletal_carrier_functor_Sets_Cat
  (K : Sets ⟶ Cat)
  (pt : ∀ A : Sets, carrier A → obj[fobj[K] A])
  (Kobj : ∀ (A B : Sets) (f : A ~> B) (x : carrier A),
            fobj[fmap[K] f] (pt A x) = pt B (f x))
  (Kskel : ∀ (A : Sets) (x y : obj[fobj[K] A]), x ≅ y → x = y)
  (Kinj : ∀ (A : Sets) (x y : carrier A), pt A x = pt A y → x = y) :
  False.
Proof.
  destruct (@fmap_respects _ _ K blur_bool blur_bool
              id[blur_bool] blur_bool_negb (fun _ => I)) as [iso _].
  pose proof (iso (pt blur_bool true)) as I0.
  rewrite (Kobj blur_bool blur_bool id[blur_bool] true) in I0.
  rewrite (Kobj blur_bool blur_bool blur_bool_negb true) in I0.
  simpl in I0.
  exact (Bool.diff_true_false (Kinj blur_bool true false (Kskel _ _ _ I0))).
Qed.

(* ... and the refutation is not vacuous for [Cat_Disc]: it satisfies
   [Kobj] (at [eq_refl]) and [Kinj] (by the identity function), and fails
   EXACTLY [Kskel].  So the escape is located rather than assumed, and
   the general theorem is genuinely about the shape of the fibres. *)
Definition cat_disc_pt (A : Sets) : carrier A → obj[fobj[Cat_Disc] A] :=
  fun a => a.

Example cat_disc_Kobj (A B : Sets) (f : A ~> B) (x : carrier A) :
  fobj[fmap[Cat_Disc] f] (cat_disc_pt A x) = cat_disc_pt B (f x) := eq_refl.

Definition cat_disc_Kinj (A : Sets) (x y : carrier A) :
  cat_disc_pt A x = cat_disc_pt A y → x = y := fun e => e.

Theorem Cat_Disc_not_skeletal :
  (∀ (A : Sets) (x y : obj[fobj[Cat_Disc] A]), x ≅ y → x = y) → False.
Proof.
  intro Hskel.
  refine (Bool.diff_true_false (Hskel blur_bool true false _)).
  exact (disc_setoid_iso (is_setoid blur_bool) I).
Qed.

(* NEGATIVE 4 (CONVERSION).  The two discrete categories are not even
   convertible, which pins at the level of terms what the refutation
   above establishes at the level of theorems.  The controls are
   [cat_disc_obj] and [cat_disc_obj_carrier] in §2: the object TYPES do
   agree. *)
Fail Example disc_is_DiscreteCat (A : Sets) :
  fobj[Cat_Disc] A = DiscreteCat (carrier A) := eq_refl.

(** ** §8. The universe boundary *)

(* Instrument check: [Fail] is live in this file.  Every negative above
   and below was additionally stripped once and its failure kind read off
   the whole error message -- four CONVERSION failures in §4 and §7,
   reporting "cannot unify" with no universe clause, and two FORMABILITY
   failures here, reporting "universe inconsistency: Cannot enforce ...".
   The two kinds are kept lexically apart. *)
Fail Definition probe_instrument_live : Datatypes.unit := 0.

(* Section-local [Universes]/[Constraint] declarations do not leak; the
   Instance/Fun/Group.v precedent applies, so these probes live in the
   library file beside the constants they guard rather than in [Test/].

   FIRST, the restriction and its attribution.  The [Constraint] here is
   LOAD-BEARING and that was measured by deletion: without it [ch]
   unifies with [co] and both negatives succeed.

   The three controls run down the chain and each removes one candidate
   culprit.  [C : obj[Cat]] shows the ambient category of categories is
   innocent -- it accepts a category whose homs sit STRICTLY BELOW its
   objects.  [pi0 C] shows the object map is innocent.  [pi0_fmap] at
   that same C shows the arrow map is innocent.  What is left is
   [pi0_fmap_respects] (Theory/Connected/Components.v), declared over
   [Category@{u0 u0 u0}], and it is rejected -- as is [fobj[Pi0] C] with
   it, on the same message.  So [Pi0], and hence every constant of this
   file that mentions it, accepts only categories whose object, hom and
   proof universes COINCIDE. *)
Section Pi0Restriction.
  Universes co ch.
  Constraint ch < co.
  Context (C D : Category@{co ch ch}).

  Check (C : obj[Cat]).
  Check (pi0 C).
  Check (fun F : C ⟶ D => pi0_fmap F).

  Fail Check (fun (F G : C ⟶ D) => @pi0_fmap_respects C D F G).
  Fail Check (fobj[Pi0] C).
End Pi0Restriction.

(* SECOND, the accepted class is inhabited: at a category with all three
   universes at one level [pi0_fmap_respects], [Pi0] and the
   transposition are all formable, so the restriction above cuts rather
   than empties.  There is no [Constraint] here and none is wanted.

   The first control here exists because a rename simulation FOUND A
   VACUOUS GUARD: [pi0_fmap_respects] was named only inside its own
   [Fail], so a rename of the donor would have turned that negative
   silently green.  Naming it in a command that must SUCCEED closes
   that. *)
Section Pi0Accepted.
  Universes cu.
  Context (C : Category@{cu cu cu}).
  Check (fun (F G : C ⟶ C) => @pi0_fmap_respects C C F G).
  Check (fobj[Pi0] C).
  Check (fun A : Sets => pi0_adj_iso C A).
End Pi0Accepted.

(* THIRD, and this is the guard item IV promised: the identification is
   MINIMIZATION AND NOT CONTENT.  The donor's lemma is restated here with
   its binders written out -- same statement, same one-line proof text,
   nothing else changed -- inside a section declaring BOTH categories'
   hom universes STRICTLY BELOW their object universe, and it is
   accepted.  The [Constraint]s are meaning-giving rather than
   load-bearing: the [Lemma] would elaborate without them, but then the
   levels could collapse and the command would demonstrate nothing.

   This is a PROBE.  The repair belongs to
   Theory/Connected/Components.v and is NOT performed here; nothing
   in this file uses the restatement, and no claim is made that [Pi0]
   itself would then be free, which would require rebuilding it.  Note
   also what the repair does not remove: the restated lemma still carries
   [hc = hd] in its own constraint block, identifying the two categories'
   hom universes with each other. *)
Section Pi0RespectsRepairable.
  Universes o hc hd so.
  Constraint hc < o.
  Constraint hd < o.

  Lemma probe_pi0_fmap_respects_annotated
    {C : Category@{o hc hc}} {D : Category@{o hd hd}} (F G : C ⟶ D)
    (H : F ≈ G) : @pi0_fmap@{o so hc hd} C D F ≈ pi0_fmap G.
  Proof. intro x; exact (hom_zigzag (to (`1 H x))). Qed.
End Pi0RespectsRepairable.
