(** * The objects functor on the category of categories *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 nLab:      https://ncatlab.org/nlab/show/indiscrete+category
 nLab:      https://ncatlab.org/nlab/show/adjoint+string
 nLab:      https://ncatlab.org/nlab/show/Cat
 nLab:      https://ncatlab.org/nlab/show/strict+category
 nLab:      https://ncatlab.org/nlab/show/connected+component
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   本文件给出对象相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** §1. The discrete extension, with its universes written out *)

(* A function [f : A → obj[C]] extends to a functor out of the discrete
   category on [A]: an object goes to its image, and the only morphism of
   a discrete hom-set -- an equality proof -- goes to the identity,
   transported along that proof.

   This is Instance/Discrete.v's [DiscreteCat_Functor] with the
   universe binders written out and the setoid [rewrite] avoided.  BOTH
   changes were load-bearing and were measured separately.  Written
   without the binders, minimization pins the source at
   [DiscreteCat@{o Set Set}] -- which WAS the donor's actual signature,
   and the pin §8 used to exhibit.  And discharging the [fmap_comp]
   branch with [now rewrite id_left] instead of [symmetry; apply
   id_left] drags [Morphisms] universes in that no annotation can bind
   (the elaborator reports an unbound universe, and adding further
   binders only renames it).

   TWO RECORDED CORRECTIONS.  First, the donor is no longer written
   without binders: it was annotated in place in the PR "algebraic
   carriers are sets" (2026-09-17), so [disc_ext] is now a SECOND
   [Set]-free extension rather than the only one, and §8 checks the two
   against each other instead of separating them.  Second, an earlier
   revision of this paragraph ended "A [Program Definition] cannot be
   annotated here at all, since its obligations mint fresh universes;
   hence the [refine]."  That is FALSE as stated and the annotated donor
   is the counterexample: a [Program Definition] takes binders like any
   other, and a trailing [+] in the binder list allows exactly the fresh
   universes its obligations mint.  What [refine] buys is narrower and is
   still true -- it mints NO auxiliary universe, so [disc_ext@{o h p q}]
   needs no [+] where [DiscreteCat_Functor@{o h p uo uh up +}] does. *)
Definition disc_ext@{o h p q} {A : Type@{o}} {C : Category@{q h p}}
  (f : A → obj[C]) : DiscreteCat@{o h p} A ⟶ C.
Proof.
  unshelve refine (@Build_Functor (DiscreteCat@{o h p} A) C f
                    (fun x y (e : x = y) =>
                       match e in _ = z return f x ~{C}~> f z with
                       | eq_refl => id end) _ _ _).
  - intros x y e1 e2 He. destruct He. reflexivity.
  - intros x. reflexivity.
  - intros x y z g e. destruct g, e. simpl. symmetry; apply id_left.
Defined.

(** ** §2. The objects functor *)

(* [obj[-]] on objects and [fobj[-]] on arrows.  All three functor laws
   are discharged by the ambient obligation tactic, and there is a reason
   rather than an accident behind that: [fmap_respects] is the FIRST
   PROJECTION of [Functor_StrictEq_Setoid]'s pair, whose first component
   [eq_on_obj] IS the required pointwise Leibniz equality of object maps
   (§6's [objects_respects_StrictCat] writes that projection out as a
   [:=] with no tactic), and the identity and composition laws ask only
   for [∀ x, x = x] on the underlying object maps. *)
Program Definition StrictCat_Objects : StrictCat ⟶ Coq := {|
  fobj := fun C => obj[C];
  fmap := fun _ _ F => fobj[F]
|}.

(** ** §3. The discrete functor *)

(* The three obligations are [fmap_respects], [fmap_id] and [fmap_comp],
   each a strict equality of functors between discrete categories: the
   object component is supplied by the hypothesis (respectively by
   [eq_refl]) and the coherence field vanishes once the discrete
   morphism -- an equality proof -- is destructed. *)
Program Definition StrictCat_Disc : Coq ⟶ StrictCat := {|
  fobj := fun A => DiscreteCat A;
  fmap := fun A B (f : A ~{Coq}~> B) => disc_ext (C := DiscreteCat B) f
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. destruct e; simpl.
  now destruct (H a).
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. now destruct e.
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. now destruct e.
Defined.

(** ** §4. The adjunction *)

(* The transposition.  A functor out of a discrete category IS its object
   map, and that is the whole content: [to] forgets the arrow action and
   [from] is [disc_ext].  Two obligations remain -- that [from] respects
   [≈], and the round trip [from ∘ to ≈ id]; the other round trip and
   the [Proper] certificate for [to] are discharged by the ambient
   tactic, which is already the strict/[≈] split §5 measures. *)
Program Definition disc_adj_iso (A : obj[Coq]) (C : obj[StrictCat]) :
  @Isomorphism Sets
    {| carrier := @hom StrictCat (StrictCat_Disc A) C
     ; is_setoid := @homset StrictCat (StrictCat_Disc A) C |}
    {| carrier := @hom Coq A (StrictCat_Objects C)
     ; is_setoid := @homset Coq A (StrictCat_Objects C) |} := {|
  to   := {| morphism := fun (F : DiscreteCat A ⟶ C) => fobj[F] |};
  from := {| morphism := fun (f : A → obj[C]) => disc_ext f |}
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. destruct e; simpl.
  now destruct (H a).
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. destruct e.
  unfold Logic.transport, Logic.transport_r, Logic.transport; simpl.
  symmetry; exact (@fmap_id _ _ x a).
Defined.

(* Mac Lane's middle adjunction.  Both naturality clauses close by
   [reflexivity]: [Build_Adjunction'] states them for the FORWARD
   transpose, which lands in [Coq], where [≈] is pointwise [=] and where
   forgetting the arrow action of a composite is forgetting it twice. *)
Definition Disc_Objects_Adjunction : StrictCat_Disc ⊣ StrictCat_Objects.
Proof.
  unshelve eapply Build_Adjunction'.
  - exact disc_adj_iso.
  - intros A B C f g. reflexivity.
  - intros A B C f g. reflexivity.
Defined.

(** ** §5. Strengths, strict first *)

Example objects_obj (C : obj[StrictCat]) :
  fobj[StrictCat_Objects] C = obj[C] := eq_refl.

Example objects_map (C D : obj[StrictCat]) (F : C ~{StrictCat}~> D)
  (x : C) : fmap[StrictCat_Objects] F x = F x := eq_refl.

Example disc_on_obj (A : obj[Coq]) :
  fobj[StrictCat_Disc] A = DiscreteCat A := eq_refl.

Example disc_map (A B : obj[Coq]) (f : A ~{Coq}~> B) (x : A) :
  fobj[fmap[StrictCat_Disc] f] x = f x := eq_refl.

Example adj_to_forgets (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) :
  to (disc_adj_iso A C) F = fobj[F] := eq_refl.

Example adj_from_extends (A : obj[Coq]) (C : obj[StrictCat])
  (f : A ~{Coq}~> StrictCat_Objects C) (x : A) :
  fobj[from (disc_adj_iso A C) f] x = f x := eq_refl.

Example adj_to_from (A : obj[Coq]) (C : obj[StrictCat])
  (f : A ~{Coq}~> StrictCat_Objects C) :
  to (disc_adj_iso A C) (from (disc_adj_iso A C) f) = f := eq_refl.

(* The unit is the IDENTITY FUNCTION, not merely a natural isomorphism:
   the transpose of [id] at [StrictCat_Disc A] is [fobj[Id]], which is
   [fun x => x] on the nose.  The counit is the identity on objects, and
   cannot be the identity functor, for the same reason
   Adjunction/Diagonal/Finite.v
   records for the diagonal: [counit] at [C] is a functor
   [StrictCat_Disc (StrictCat_Objects C) ⟶ C] between two DIFFERENT
   categories. *)
Example unit_is_id (A : obj[Coq]) (a : A) :
  @unit _ _ _ _ Disc_Objects_Adjunction A a = a := eq_refl.

Example counit_obj (C : obj[StrictCat])
  (x : StrictCat_Disc (StrictCat_Objects C)) :
  fobj[@counit _ _ _ _ Disc_Objects_Adjunction C] x = x := eq_refl.

(* THE ONE [≈]-ONLY STEP, REFUTED AT [eq_refl] AND THEN LOCALIZED.  The
   two probes below sit either side of a passing control, so the cause is
   read off rather than guessed: the OBJECT map returns on the nose, the
   ARROW map does not, and the residue is exactly [fmap_id]. *)
Fail Example adj_from_to_strict (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) :
  from (disc_adj_iso A C) (to (disc_adj_iso A C) F) = F := eq_refl.

Example adj_from_to_equiv (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) :
  from (disc_adj_iso A C) (to (disc_adj_iso A C) F) ≈ F.
Proof. exact (iso_from_to (disc_adj_iso A C) F). Qed.

Example roundtrip_obj (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) (x : A) :
  fobj[from (disc_adj_iso A C) (to (disc_adj_iso A C) F)] x = fobj[F] x
  := eq_refl.

Fail Example roundtrip_map (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) (x : A) :
  fmap[from (disc_adj_iso A C) (to (disc_adj_iso A C) F)] (eq_refl : x = x)
    = fmap[F] (eq_refl : x = x) := eq_refl.

Example roundtrip_map_equiv (A : obj[Coq]) (C : obj[StrictCat])
  (F : StrictCat_Disc A ~{StrictCat}~> C) (x : A) :
  fmap[from (disc_adj_iso A C) (to (disc_adj_iso A C) F)] (eq_refl : x = x)
    ≈ fmap[F] (eq_refl : x = x).
Proof. symmetry; exact (@fmap_id _ _ F x). Qed.

(* [StrictCat_Disc] is fully faithful, which is what "the unit is the identity"
   says categorically.  Faithfulness costs NOTHING -- the ambient tactic
   discharges it, since injectivity of [fmap[StrictCat_Disc]] is the first
   projection of a strict functor equality.  Fullness costs exactly the
   round trip above, i.e. exactly one [fmap_id]. *)
#[export] Program Instance Disc_Faithful : Faithful StrictCat_Disc.

#[export] Program Instance Disc_Full : Full StrictCat_Disc := {|
  prefmap := fun A B (G : StrictCat_Disc A ~{StrictCat}~> StrictCat_Disc B)
              => fobj[G]
|}.
Next Obligation.
  exact (iso_from_to (disc_adj_iso x (StrictCat_Disc y)) g).
Defined.

(** ** §6. Why the source is [StrictCat] and not [Cat] *)

(* [ObjRespectsCat] is exactly the [fmap_respects] obligation that ANY
   objects functor owes, at either candidate target: both [Coq]'s
   hom-setoid and [ObjSetoid]'s [equiv] are Leibniz equality of objects,
   so respecting [≈] means carrying [≈]-equal functors to POINTWISE
   LEIBNIZ-EQUAL object maps. *)
Definition ObjRespectsCat : Type :=
  ∀ (C D : Category) (F G : C ⟶ D),
    @equiv _ (@homset Cat C D) F G → ∀ x : C, F x = G x.

(* Over [StrictCat] it is the FIRST PROJECTION of the hom-setoid: a [:=]
   with no tactic. *)
Definition objects_respects_StrictCat :
  ∀ (C D : Category) (F G : C ⟶ D),
    @equiv _ (@homset StrictCat C D) F G → ∀ x : C, F x = G x :=
  fun C D F G H => `1 H.

Lemma indiscrete_hom_eq (a b : Datatypes.unit) : a = b.
Proof. now destruct a, b. Qed.

(* The witness.  In [Indiscrete bool] every hom-set is [unit], so the
   negation endofunctor is naturally isomorphic to the identity -- the
   component at each object is [tt], invertible by [tt] -- while its
   object map differs from the identity's at [true]. *)
Program Definition SwapI : Indiscrete bool ⟶ Indiscrete bool := {|
  fobj := negb;
  fmap := fun _ _ _ => tt
|}.

Lemma swap_iso_in_Cat :
  @equiv _ (@homset Cat (Indiscrete bool) (Indiscrete bool))
         (Id[Indiscrete bool]) SwapI.
Proof.
  unshelve eexists.
  - intro x. unshelve eexists; simpl; try exact tt; apply indiscrete_hom_eq.
  - intros x y f; simpl; apply indiscrete_hom_eq.
Qed.

(* Hence there is no objects functor over [Cat] INTO A TARGET WHOSE
   MORPHISM [≈] IS POINTWISE LEIBNIZ EQUALITY OF OBJECTS -- [Coq], or
   [Sets] at [ObjSetoid] -- and not merely that this one construction
   fails there.  The qualifier is necessary and is not a hedge: an
   objects functor [Cat ⟶ Sets] over the ISOMORPHISM setoid exists, with
   [fmap_respects] discharged by [fobj_iso].  That is the alternative
   issue #357 item 1 itself offers, and it is excluded here by the
   exercise's request for the strict version, NOT by this theorem. *)
Theorem objects_not_functorial_over_Cat : ObjRespectsCat → False.
Proof.
  intro K.
  exact (eq_ind true (fun b : bool => if b then True else False) I false
           (K _ _ (Id[Indiscrete bool]) SwapI swap_iso_in_Cat true)).
Qed.

(** ** §7. Why the target is [Coq] and not [Sets] *)

(* The mirror-image refutation.  It is stated for an ARBITRARY object map
   [K : obj[Sets] → obj[StrictCat]] rather than for [StrictCat_Disc], because it
   has to be binding on the right-hand wing too: the two instantiations
   at the end of this section are the discrete and the INDISCRETE object
   maps, and both are refuted by the same theorem.

   The hypotheses are the least that make [K] deserve the name: it is
   POINTED (each object of [K A] is named by a point of [A]), that naming
   is INJECTIVE, and it is NATURAL (the arrow action carries the name of
   [x] to the name of [f x]).  Both [DiscreteCat ∘ carrier] and
   [Indiscrete ∘ carrier] satisfy all three with [Kpt] the identity. *)
Definition PointedObjectMap
  (K : obj[Sets] → obj[StrictCat])
  (Kmap : ∀ A B : obj[Sets], (A ~{Sets}~> B) → (K A ~{StrictCat}~> K B))
  (Kpt : ∀ A : obj[Sets], carrier A → obj[K A]) : Type :=
  (∀ (A : obj[Sets]) (x y : carrier A), Kpt A x = Kpt A y → x = y)
    * (∀ (A B : obj[Sets]) (f : A ~{Sets}~> B) (x : carrier A),
         fobj[Kmap A B f] (Kpt A x) = Kpt B (f x)).

(* The separating object: [bool] under the everywhere-true setoid.  Two
   constant maps out of it are [≈] without being pointwise equal, which
   is precisely what a [Sets]-morphism may do and a [StrictCat]-morphism
   may not. *)
Program Definition BlurBool : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := fun _ _ => True |}
|}.

Program Definition kTrue : BlurBool ~{Sets}~> BlurBool :=
  {| morphism := fun _ => true |}.

Program Definition kFalse : BlurBool ~{Sets}~> BlurBool :=
  {| morphism := fun _ => false |}.

Lemma k_equiv : kTrue ≈ kFalse.
Proof. intro x; exact I. Qed.

Theorem no_carrier_functor_Sets_StrictCat
  (K : obj[Sets] → obj[StrictCat])
  (Kmap : ∀ A B : obj[Sets], (A ~{Sets}~> B) → (K A ~{StrictCat}~> K B))
  (Kpt : ∀ A : obj[Sets], carrier A → obj[K A])
  (HK : PointedObjectMap K Kmap Kpt)
  (Kresp : ∀ (A B : obj[Sets]) (f g : A ~{Sets}~> B), f ≈ g →
     @equiv _ (@homset StrictCat (K A) (K B)) (Kmap A B f) (Kmap A B g))
  : False.
Proof.
  destruct HK as [Kinj Kobj].
  pose proof (`1 (Kresp _ _ kTrue kFalse k_equiv) (Kpt BlurBool true)) as H.
  rewrite (Kobj BlurBool BlurBool kTrue true) in H.
  rewrite (Kobj BlurBool BlurBool kFalse true) in H.
  apply Kinj in H.
  discriminate.
Qed.

(* Instantiation 1: the DISCRETE object map on carriers, i.e. §3's
   [StrictCat_Disc] re-aimed at [Sets].  It is refuted. *)
Definition disc_carrier_Kmap (A B : obj[Sets]) (f : A ~{Sets}~> B) :
  DiscreteCat (carrier A) ~{StrictCat}~> DiscreteCat (carrier B) :=
  disc_ext (C := DiscreteCat (carrier B)) f.

Definition disc_carrier_pointed :
  PointedObjectMap (fun A => DiscreteCat (carrier A)) disc_carrier_Kmap
                   (fun _ x => x) :=
  (fun _ _ _ H => H, fun _ _ _ _ => eq_refl).

Theorem disc_carrier_not_Sets_functor
  (Kresp : ∀ (A B : obj[Sets]) (f g : A ~{Sets}~> B), f ≈ g →
     @equiv _ (@homset StrictCat _ _)
            (disc_carrier_Kmap A B f) (disc_carrier_Kmap A B g)) : False.
Proof.
  exact (no_carrier_functor_Sets_StrictCat _ _ _ disc_carrier_pointed Kresp).
Qed.

(* Instantiation 2: the INDISCRETE object map on carriers -- the right
   adjoint of the right-hand wing, re-aimed at [Sets].  It is refuted by
   the SAME theorem, which is why §7 is stated generally.  This is the
   sense in which the codomain decision is binding on that module. *)
Program Definition ind_carrier_Kmap (A B : obj[Sets]) (f : A ~{Sets}~> B) :
  Indiscrete (carrier A) ~{StrictCat}~> Indiscrete (carrier B) := {|
  fobj := f;
  fmap := fun _ _ _ => tt
|}.

Definition ind_carrier_pointed :
  PointedObjectMap (fun A => Indiscrete (carrier A)) ind_carrier_Kmap
                   (fun _ x => x) :=
  (fun _ _ _ H => H, fun _ _ _ _ => eq_refl).

Theorem ind_carrier_not_Sets_functor
  (Kresp : ∀ (A B : obj[Sets]) (f g : A ~{Sets}~> B), f ≈ g →
     @equiv _ (@homset StrictCat _ _)
            (ind_carrier_Kmap A B f) (ind_carrier_Kmap A B g)) : False.
Proof.
  exact (no_carrier_functor_Sets_StrictCat _ _ _ ind_carrier_pointed Kresp).
Qed.

(** ** §8. The universe boundary *)

(* Instrument check: [Fail] is live in this file.  Every negative below
   and in §5 was additionally stripped once and its failure kind read off
   the whole error message -- two CONVERSION failures in §5 (reporting
   "cannot unify", with no universe clause) and one FORMABILITY refusal
   here (reporting "universe inconsistency: Cannot enforce ...").
   The two kinds are kept lexically apart.

   RECORDED CORRECTION.  An earlier revision counted THREE formability
   refusals here: the [StrictCat] donor identification of the section
   after next, plus two [Set] pins in [Section SetPin].  The two [Set]
   pins are gone -- see that section -- so the count is now one. *)
Fail Definition probe_instrument_live : Datatypes.unit := 0.

(* Section-local [Universes]/[Constraint] declarations do not leak; the
   Instance/Fun/Group.v precedent applies, so these probes live in the
   library file beside the constants they guard rather than in [Test/].

   FIRST: item I.3's [Set] pin -- now REPAIRED, and this section is the
   record of the repair.

   RECORDED CORRECTION.  An earlier revision stated this section as two
   FORMABILITY NEGATIVES: over a category whose homs are declared
   strictly above [Set], ascribing [DiscreteCat_Functor f] to
   [DiscreteCat@{uo uh uh} A ⟶ C] and ascribing [Indiscrete] to
   [Type@{uo} → Category@{uo uh uh}] were both refused, each reading
   "universe inconsistency: Cannot enforce Set = uh", because both donors
   were declared with bare binders and minimization pinned their hom and
   proof levels to [Set].  The comment added that the [Constraint] below
   was INERT for those two negatives, since what they fired on was the
   donors' literal [Set] meeting the rigid declared level [uh].

   In the PR "algebraic carriers are sets" (2026-09-17) both donors were
   annotated in place -- [DiscreteCat_Functor@{o h p uo uh up +}] at
   Instance/Discrete.v and [Indiscrete@{o h p}] at
   Instance/Discrete/Reconstruct.v -- so both ascriptions are now
   ACCEPTED and both lines below are positive controls.  The [Constraint]
   remains inert, and is kept for the reason it was kept before: it
   states the intended reading, and the whole section is only interesting
   above [Set].

   What this section still guards is therefore not a refusal but an
   AGREEMENT: the two annotated donors and the hand-written [disc_ext]
   reach the same declared levels, so the tree now has three
   interchangeable discrete extensions rather than one usable one and two
   pinned ones.  [disc_ext] is retained because it is written with
   [refine] rather than [Program] and so mints no auxiliary universe;
   §1's paragraph on that difference stands.

   Contrast the section after next, where the analogous [Constraint] IS
   load-bearing and the negative is real: deleting the [Constraint] makes
   that negative succeed and the file stops compiling. *)
Section SetPin.
  Universes uo uh.
  Constraint Set < uh.
  Context (A : Type@{uo}) (C : Category@{uo uh uh}) (f : A → obj[C]).

  (* controls: the shape and the functor type ARE formable here, and both
     donors ARE nameable. *)
  Check (DiscreteCat@{uo uh uh} A).
  Check (DiscreteCat@{uo uh uh} A ⟶ C).
  Check (DiscreteCat_Functor f).
  Check (Indiscrete A).

  (* and, since the annotation, both donors also REACH these levels *)
  Check (DiscreteCat_Functor f : DiscreteCat@{uo uh uh} A ⟶ C).
  Check (Indiscrete@{uo uh uh} : Type@{uo} → Category@{uo uh uh}).

  (* as does the hand-written extension *)
  Check (disc_ext@{uo uh uh uo} f : DiscreteCat@{uo uh uh} A ⟶ C).
End SetPin.

(* SECOND: a DONOR identification, named and not repaired.  An object of
   [StrictCat] has its hom and proof universes identified -- the fourth
   and fifth universe arguments of [StrictCat] are the inner category's
   object and hom-and-proof levels -- so the rejection below reports
   "Cannot enforce cp = ch".  Here the [Constraint] IS load-bearing:
   without it [cp] unifies with [ch] and the negative succeeds.  What is
   NOT identified is object against hom, which is what the following
   section's control shows, its homs sitting strictly BELOW its
   objects. *)
Section StrictCatObjects.
  Universes co ch cp.
  Constraint ch < cp.
  Context (C : Category@{co ch cp}).
  Fail Check (C : obj[StrictCat]).
End StrictCatObjects.

Section StrictCatHomsBelow.
  Universes co ch.
  Constraint ch < co.
  Context (C : Category@{co ch ch}).
  Check (C : obj[StrictCat]).
End StrictCatHomsBelow.

(* THIRD, and this is the guard §5 promised: the identification visible
   in [Disc_Objects_Adjunction]'s BINDER is minimization and not content.
   The adjunction TYPE is formable with the inner categories' hom
   universe declared STRICTLY BELOW their object universe -- here the
   two functors run between [Coq@{e f f f}] and [StrictCat@{c f a f b}],
   whose objects are categories with objects at [f] and homs at [b].

   This is also where the comparison with Instance/Top/Forgetful.v
   belongs.  That file's [Discrete ⊣ Forget ⊣ Indiscrete] for [Top] is
   forced into transposition isomorphisms because [Top]'s homs sit
   strictly above its points, so no single [Sets] serves both directions
   and the packaged [Adjunction] record is unformable at every level.
   NO ANALOGUE OF THAT WALL ARISES HERE: the two functors of this file
   run between one [StrictCat] and one [Coq] in both directions, the record
   is built above, and the check below shows it is not even confined to
   a degenerate universe assignment.

   The [Constraint] here is neither inert nor load-bearing in the sense
   of the two sections above: the [Check] passes with or without it, and
   what the declaration buys is the CONTENT of the control -- without it
   the levels could collapse and the command would demonstrate nothing.
   Stated so that a later reader does not delete it as redundant. *)
Section AdjunctionUniversesSeparated.
  Universes a b c e f.
  Constraint b < f.
  Check (StrictCat_Disc@{a b c f e f} ⊣ StrictCat_Objects@{a c f e f b}).
End AdjunctionUniversesSeparated.

(** ** §9. The objects functor genuinely forgets *)

(* Sharpness for [StrictCat_Objects], proved rather than asserted: it is NOT
   faithful.  The witness is the delooping of the two-element xor monoid
   -- one object, [bool] as its hom-set, [false] as the identity -- which
   carries exactly two endomorphisms as a monoid, the identity and the
   constant.  Both are functors, both have the SAME object map (there is
   only one object), and they differ at the arrow [true]. *)
#[local] Ltac bool_cases :=
  repeat match goal with [ b : bool |- _ ] => destruct b end;
  reflexivity.

Program Definition BoolMon : Category := {|
  obj     := poly_unit;
  hom     := fun _ _ => bool;
  homset  := fun _ _ => {| equiv := @eq bool |};
  id      := fun _ => false;
  compose := fun _ _ _ f g => xorb f g
|}.
Next Obligation. bool_cases. Defined.
Next Obligation. bool_cases. Defined.
Next Obligation. bool_cases. Defined.

Program Definition ZeroF : BoolMon ⟶ BoolMon := {|
  fobj := fun x => x;
  fmap := fun _ _ _ => false
|}.

(* [poly_unit] has decidable equality, so Hedberg applies and the
   transport in [Functor_StrictEq_Setoid]'s coherence field can be
   eliminated; the argument is axiom-free. *)
Lemma poly_unit_uip (p : @eq poly_unit ttt ttt) : p = eq_refl.
Proof.
  apply (Eqdep_dec.UIP_dec (fun x y : poly_unit => left
    (match x, y with ttt, ttt => eq_refl end))).
Qed.

Lemma Id_neq_ZeroF :
  @equiv _ (@homset StrictCat BoolMon BoolMon) (Id[BoolMon]) ZeroF → False.
Proof.
  intros [eo co].
  pose proof (co ttt ttt true) as H.
  rewrite (poly_unit_uip (eo ttt)) in H.
  simpl in H. discriminate.
Qed.

Example objects_merges :
  fmap[StrictCat_Objects] (Id[BoolMon]) ≈ fmap[StrictCat_Objects] ZeroF.
Proof. intro x; reflexivity. Qed.

Theorem Objects_not_Faithful : Faithful StrictCat_Objects → False.
Proof.
  intro F. exact (Id_neq_ZeroF (fmap_inj _ _ objects_merges)).
Qed.
