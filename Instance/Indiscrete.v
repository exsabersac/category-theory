(** * The indiscrete functor and the right half of Smythe's adjoint string *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Coq.
Require Import Category.Instance.StrictCat.
Require Import Category.Structure.Discrete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Instance.Cat.Objects.

Generalizable All Variables.

(*
 nLab:      https://ncatlab.org/nlab/show/indiscrete+category
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 nLab:      https://ncatlab.org/nlab/show/adjoint+string
 nLab:      https://ncatlab.org/nlab/show/adjoint+triple
 nLab:      https://ncatlab.org/nlab/show/strict+category
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   本文件给出非离散范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** §1. The indiscrete co-extension *)

(* A function [f : obj[C] → A] co-extends to a functor into the
   indiscrete category on [A]: an object goes to its image, and a
   morphism goes to the only morphism there is.  This is the exact
   mirror of Instance/Cat/Objects.v:§1's [disc_ext], and like it, all
   three functor laws are equations in [unit] and close by that file's
   own [indiscrete_hom_eq].

   Unlike [disc_ext] it carries NO universe binders.  RECORDED CORRECTION
   to the reason: an earlier revision said "the reason is not that it is
   better behaved but that there is nothing left to bind: [Indiscrete] has
   already fixed the target's hom and proof universes at [Set], and
   [Functor] then forces the SOURCE's to agree.  Item V and §8 measure
   that; it is the one place this wing is worse off than the left one."
   [Indiscrete] fixes nothing since its annotation in the PR "algebraic
   carriers are sets" (2026-09-17), and measured now
   [indisc_lift@{u u0 u1}] is over [C : Category@{u0 u1 u1}] with the
   target at [Functor@{u0 u1 u1 u u1 u1}] -- free, and no worse off than
   the left wing.  The absence of binders here is therefore inherited
   freedom rather than a pin, and adding them was not attempted.

   A SECOND CORRECTION: the same revision added "A [Program Definition]
   cannot be annotated here in any case, since its obligations mint fresh
   universes."  That is FALSE, and Instance/Discrete.v's annotated
   [Program Definition DiscreteCat_Functor@{o h p uo uh up +}] is the
   counterexample: a trailing [+] allows exactly the universes the
   obligations mint.  The [refine] is kept for the narrower reason that it
   mints none, again following the donor. *)
Definition indisc_lift {C : Category} {A : Type} (f : obj[C] -> A)
  : C ⟶ Indiscrete A.
Proof.
  unshelve refine (@Build_Functor C (Indiscrete A) f
                     (fun _ _ _ => tt) _ _ _).
  - intros x y f1 g1 H. apply indiscrete_hom_eq.
  - intros x. apply indiscrete_hom_eq.
  - intros x y z g1 h1. apply indiscrete_hom_eq.
Defined.

(** ** §2. The indiscrete functor *)

(* [Indiscrete] on objects, and [indisc_lift] on arrows -- the arrow
   action is not a second construction, because [obj[Indiscrete A]] IS
   [A] ([indisc_obj_carrier], §4), so a [Coq]-morphism [A ~> B] already
   has the type [indisc_lift] wants.  §3's mirror on the left wing is
   Objects.v's [fmap := fun A B f => disc_ext f].

   ONE obligation remains, [fmap_respects]; [fmap_id] and [fmap_comp]
   are discharged by the ambient tactic, since a strict functor equality
   between two functors into an indiscrete category has an [eq_refl]
   object family and a coherence field valued in [unit]. *)
Program Definition StrictCat_Indisc : Coq ⟶ StrictCat := {|
  fobj := Indiscrete;
  fmap := fun A B (f : A ~{Coq}~> B) => indisc_lift (C := Indiscrete A) f
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. apply indiscrete_hom_eq.
Defined.

(** ** §3. The adjunction *)

(* The transposition, and the whole content is that a functor INTO an
   indiscrete category IS its object map: [to] co-extends and [from]
   forgets the arrow action.  On the left wing the two are exchanged --
   there [to] forgets and [from] extends -- which is why the round trip
   that survives on the nose is the other one (§4).

   Two obligations remain, that [to] respects [≈] and one round trip;
   the other round trip and [from]'s [Proper] certificate are discharged
   by the ambient tactic, which is already the strict/[≈] split §4
   measures. *)
(* THE [StrictCat] INSTANCE IS WRITTEN OUT, AND THE LAST TWO BINDERS ARE
   THE POINT.  [StrictCat@{u u0 u1 co ch} : Category@{u u0 u0}] has the
   INNER category's object level [co] and hom-and-proof level [ch] as its
   fourth and fifth arguments, and nothing in this definition relates
   them.  Left implicit, universe minimization identifies them, and the
   adjunction then applies only to categories whose objects and homs sit
   at one level.  That was invisible while [Indiscrete] was pinned at
   [Category@{u Set Set}] -- [ch] was then the literal [Set] and [co] was
   free by construction -- and it became visible the moment [Indiscrete]
   was annotated (Instance/Discrete/Reconstruct.v, PR "algebraic
   carriers are sets", 2026-09-17).  Naming the instance keeps both free,
   so §8's two sections can exhibit homs strictly above [Set] AND objects
   strictly above homs.  The trailing [+] allows the universes
   [Program]'s obligations mint. *)
Program Definition indisc_adj_iso@{u u0 u1 co ch +}
  (C : obj[StrictCat@{u u0 u1 co ch}]) (A : obj[Coq]) :
  @Isomorphism Sets
    {| carrier := @hom Coq (StrictCat_Objects C) A
     ; is_setoid := @homset Coq (StrictCat_Objects C) A |}
    {| carrier := @hom StrictCat C (StrictCat_Indisc A)
     ; is_setoid := @homset StrictCat C (StrictCat_Indisc A) |} := {|
  to   := {| morphism := fun (f : obj[C] -> A) => indisc_lift f |};
  from := {| morphism := fun (F : C ⟶ Indiscrete A) => fobj[F] |}
|}.
Next Obligation.
  intros f g H. exists H. intros a b e. apply indiscrete_hom_eq.
Defined.
Next Obligation.
  exists (fun _ => eq_refl). intros a b e. apply indiscrete_hom_eq.
Defined.

(* Mac Lane's right-hand adjunction.  Both naturality clauses close with
   an [eq_refl] object family and one [indiscrete_hom_eq], for the reason
   §2's comment gives.  [Build_Adjunction'] (Theory/Adjunction.v)
   asks only for the two [to]-side clauses; see item IV. *)
Definition Objects_Indisc_Adjunction :
  StrictCat_Objects ⊣ StrictCat_Indisc.
Proof.
  unshelve eapply Build_Adjunction'.
  - exact indisc_adj_iso.
  - intros C D A f g. exists (fun _ => eq_refl).
    intros a b e. apply indiscrete_hom_eq.
  - intros C A B f g. exists (fun _ => eq_refl).
    intros a b e. apply indiscrete_hom_eq.
Defined.

(** ** §4. Strengths, strict first *)

Example indisc_obj (A : obj[Coq]) :
  fobj[StrictCat_Indisc] A = Indiscrete A := eq_refl.

Example indisc_obj_carrier (A : obj[Coq]) :
  obj[Indiscrete A] = A := eq_refl.

Example indisc_map (A B : obj[Coq]) (f : A ~{Coq}~> B) (x : A) :
  fobj[fmap[StrictCat_Indisc] f] x = f x := eq_refl.

Example adj_to_lifts (C : obj[StrictCat]) (A : obj[Coq])
  (f : StrictCat_Objects C ~{Coq}~> A) :
  to (indisc_adj_iso C A) f = indisc_lift f := eq_refl.

Example adj_from_forgets (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) :
  from (indisc_adj_iso C A) F = fobj[F] := eq_refl.

Example adj_from_to_ind (C : obj[StrictCat]) (A : obj[Coq])
  (f : StrictCat_Objects C ~{Coq}~> A) :
  from (indisc_adj_iso C A) (to (indisc_adj_iso C A) f) = f := eq_refl.

Example indisc_counit_is_id (A : obj[Coq]) (a : A) :
  @counit _ _ _ _ Objects_Indisc_Adjunction A a = a := eq_refl.

Example unit_obj (C : obj[StrictCat]) (x : C) :
  fobj[@unit _ _ _ _ Objects_Indisc_Adjunction C] x = x := eq_refl.

Example unit_is_lift (C : obj[StrictCat]) :
  @unit _ _ _ _ Objects_Indisc_Adjunction C
    = indisc_lift (fun x : obj[C] => x) := eq_refl.

Fail Example adj_to_from_ind (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) :
  to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F) = F := eq_refl.

Example rt_obj (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) (x : C) :
  fobj[to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F)] x
    = fobj[F] x := eq_refl.

Fail Example rt_map_strict (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) (x y : C) (h : x ~> y) :
  fmap[to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F)] h
    = fmap[F] h := eq_refl.

Example rt_map_leibniz (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) (x y : C) (h : x ~> y) :
  fmap[to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F)] h
    = fmap[F] h.
Proof. apply indiscrete_hom_eq. Qed.

Example adj_to_from_equiv (C : obj[StrictCat]) (A : obj[Coq])
  (F : C ~{StrictCat}~> StrictCat_Indisc A) :
  to (indisc_adj_iso C A) (from (indisc_adj_iso C A) F) ≈ F.
Proof. exact (iso_to_from (indisc_adj_iso C A) F). Qed.

Fail Example unit_has_no_eta (u : Datatypes.unit) : u = tt := eq_refl.

Example unit_eta_by_destruct (u : Datatypes.unit) : u = tt.
Proof. now destruct u. Qed.

(** ** §5. The indiscrete functor is fully faithful *)

(* Which is what "the counit is the identity" (§4) says categorically.
   Faithfulness costs NOTHING -- injectivity of [fmap[StrictCat_Indisc]]
   is the first projection of a strict functor equality, and the ambient
   tactic finds it.  Fullness costs exactly the round trip of §4, taken
   at [≈]: the preimage of [G] is [fobj[G]], and [iso_to_from] says the
   co-extension of that is [G] again. *)
#[export] Program Instance Indisc_Faithful : Faithful StrictCat_Indisc.

#[export] Program Instance Indisc_Full : Full StrictCat_Indisc := {|
  prefmap := fun A B (G : StrictCat_Indisc A ~{StrictCat}~> StrictCat_Indisc B)
              => fobj[G]
|}.
Next Obligation.
  exact (iso_to_from (indisc_adj_iso (StrictCat_Indisc x) y) g).
Defined.

(** ** §6. The adjoint string, as far as it goes *)

(* Three of Mac Lane's four functors, and the two adjunctions between
   them, as ONE term -- so that the string is an artifact rather than two
   files that happen to compile.  It has two components and not three,
   and item II says why: the fourth adjoint lives over a different pair
   of categories, and Instance/Cat/Components.v now proves it there.
   Nothing here claims Mac Lane's full string is in the tree. *)
Definition adjoint_string :
  (StrictCat_Disc ⊣ StrictCat_Objects)
    * (StrictCat_Objects ⊣ StrictCat_Indisc) :=
  (Disc_Objects_Adjunction, Objects_Indisc_Adjunction).

(** ** §7. The two adjoints of the objects functor genuinely differ *)

(* The engine, one line: a morphism of a DISCRETE category is an
   equality proof, and an indiscrete category supplies a morphism
   between any two objects, so the image of [tt] IS the equation. *)
Lemma ind_to_disc_constant {A B : Type}
  (F : Indiscrete A ⟶ DiscreteCat B) (x y : A) : fobj[F] x = fobj[F] y.
Proof. exact (fmap[F] (tt : x ~{Indiscrete A}~> y)). Qed.

Theorem disc_indisc_not_iso :
  @Isomorphism StrictCat (DiscreteCat bool) (Indiscrete bool) -> False.
Proof.
  intro I.
  destruct (iso_to_from I) as [eo _]. simpl in eo.
  pose proof (f_equal (fobj[to I]) (ind_to_disc_constant (from I) true false))
    as H.
  rewrite (eo true), (eo false) in H.
  discriminate.
Qed.

Theorem disc_indisc_not_eq :
  StrictCat_Disc bool = StrictCat_Indisc bool -> False.
Proof.
  intro H.
  refine (Indiscrete_bool_Discrete_absurd _).
  exact (eq_rect _ Discrete (DiscreteCat_Discrete bool) _ H).
Qed.

(** ** §8. The universe boundary *)

(* Instrument check: [Fail] is live in this file. *)
Fail Definition probe_instrument_live : Datatypes.unit := 0.

(* The former [Set] pin of [Indiscrete], and its propagation -- first into
   this file's own [indisc_lift], then into the adjunction.

   RECORDED CORRECTION.  An earlier revision stated this section as THREE
   NEGATIVES and read:

     "The [Set] pin of [Indiscrete], guarded rather than merely measured,
      and then tracked as it propagates -- first into this file's own
      [indisc_lift], then into the adjunction.

      READ THE [Constraint] CORRECTLY: IT IS INERT FOR ALL THREE
      NEGATIVES, AND THAT WAS MEASURED BY DELETION RATHER THAN ASSUMED.
      Removing the line leaves all three [Fail]s failing with
      byte-identical messages, because what they fire on is the donor's
      LITERAL [Set] meeting the RIGID declared level [uh], not a relation
      declared between them."

   The three negatives were: [Indiscrete] refused at
   [Type@{uo} -> Category@{uo uh uh}]; [indisc_lift] refused over [C],
   with the gloss "NO annotation of [indisc_lift] can free it, because the
   pin reaches the SOURCE as well"; and [indisc_adj_iso] refused in
   consequence.

   ALL THREE ARE NOW ACCEPTED, and that gloss was the one thing measured
   wrongly.  No annotation of [indisc_lift] could free it, true -- but an
   annotation of [Indiscrete] could, and did: [Indiscrete@{o h p}]
   (Instance/Discrete/Reconstruct.v, PR "algebraic carriers are sets",
   2026-09-17) is [Set]-free, so the bound [Functor] puts on the source's
   hom universe is now a bound by a free level rather than by the literal
   [Set], and the whole propagation chain travels.  All three commands are
   kept as positive controls at exactly the levels that used to refuse
   them, so dropping the annotation refuses them again and breaks this
   file.

   The first line is also a GUARD ON THE ARITY: written [Indiscrete@{uo}]
   before, it would now be a universe-instance-length error and a [Fail]
   on it would have passed vacuously.  It is written with all three
   levels.

   [Constraint Set < uh] is kept: what it buys is the CONTENT of the
   section, which is only interesting above [Set].  (Instance/Cat/
   Objects.v's §8 carries the parallel correction for its own [SetPin]
   section, and records beside it a [Constraint] that IS load-bearing on
   a negative that remains, so the distinction is not academic.) *)
Section IndiscreteSetPin.
  Universes uo uh.
  Constraint Set < uh.
  Context (C : Category@{uo uh uh}) (A : Type@{uo}).

  (* Controls: the ambient, the left wing, and the two shapes. *)
  Check (C : obj[StrictCat]).
  Check (fmap[StrictCat_Objects] (Id[C])).
  Check (@disc_ext@{uo uh uh uo}).
  Check (DiscreteCat@{uo uh uh} A).
  Check (@indisc_lift (DiscreteCat@{uo Set Set} A) A).

  (* 1: the donor reaches these levels. *)
  Check (Indiscrete@{uo uh uh} : Type@{uo} -> Category@{uo uh uh}).

  (* 2: so does the lift built over it ... *)
  Check (@indisc_lift C A).

  (* 3: ... and so, therefore, does the adjunction. *)
  Check (@indisc_adj_iso C A).
End IndiscreteSetPin.

(* The OBJECT universe is free of the hom universe, and stays so.

   RECORDED CORRECTION to what this section was FOR.  An earlier revision
   read: "What is NOT pinned: the OBJECT universe.  The restriction is
   exactly 'hom and proof universes are the literal [Set]', and objects
   may sit anywhere above it -- so the adjunction is a statement about a
   real class of categories rather than about [Set]-sized ones."  There is
   no longer any [Set] restriction to soften: §8 above now exhibits the
   whole wing at homs strictly ABOVE [Set].  What this section measures
   instead is the independence that survived the repair, and it is kept
   because that independence was nearly LOST in it: with [Indiscrete]
   annotated, [indisc_adj_iso]'s implicit [StrictCat] instance minimized
   its inner object and hom levels TOGETHER, which no [Set] had been
   allowed to do while [ch] was the literal [Set].  Writing that instance
   out at §3 keeps them apart, and this section is the guard on that: the
   [Check]s below are refused if the binders at [indisc_adj_iso] are ever
   dropped.

   The [Constraint] here is neither inert nor load-bearing: the two
   [Check]s pass with or without it (measured by deletion), and what the
   declaration buys is the CONTENT of the controls -- without it [wo]
   could collapse to [Set] and the commands would demonstrate nothing.
   Stated so that a later reader does not delete it as redundant.

   The second section pushes the same point one step further and needs no
   [Set] at all: homs strictly above [Set] AND objects strictly above the
   homs, neither identified with the other. *)
Section IndiscreteObjectsFree.
  Universes wo.
  Constraint Set < wo.
  Context (C : Category@{wo Set Set}) (A : Type@{wo}).
  Check (@indisc_lift C A).
  Check (@indisc_adj_iso C A).
End IndiscreteObjectsFree.

Section IndiscreteObjectsAboveHoms.
  Universes vo vh.
  Constraint Set < vh.
  Constraint vh < vo.
  Context (C : Category@{vo vh vh}) (A : Type@{vo}).
  Check (@indisc_lift C A).
  Check (@indisc_adj_iso C A).
End IndiscreteObjectsAboveHoms.

(** ** §9. Where the string stops on the right *)

(* WHY one expects [StrictCat_Indisc ⊣ StrictCat_Objects] to fail, and
   NOT a proof that it does -- read the two apart, since only the first
   is established here.  §7's [ind_to_disc_constant] says every functor
   out of an indiscrete category into a discrete one is constant; so the
   identity map of [bool] is the object map of NO such functor, while it
   is of course one of four functions [bool → bool].  A counting
   argument from that to the non-existence of an adjunction would need
   the transposition's two legs to BE [fobj] and its inverse, and an
   [Adjunction] supplies only a pair of arbitrary setoid maps, so
   nothing here forces that.  No refutation is attempted and none is
   claimed; item VII repeats the caveat where a reader will meet it. *)
Theorem no_identity_functor_ind_to_disc
  (F : Indiscrete bool ⟶ DiscreteCat bool)
  (H : forall b : bool, fobj[F] b = b) : False.
Proof.
  pose proof (ind_to_disc_constant F true false) as K.
  rewrite (H true), (H false) in K. discriminate.
Qed.

(** ** §10. Non-vacuity *)

(* The composite [Objects ◯ Indisc] returns [Id[Coq]]'s DATA on the nose
   -- object action and arrow action both by [eq_refl] -- which is what
   "the counit is the identity" (§4) says one level up.  The whole record
   is REFUTED, and the cause is the usual one: [Compose] rebuilds
   [fmap_respects], [fmap_id] and [fmap_comp] as its own opaque proofs.
   So this is a CONVERSION negative about the law fields, with the two
   data fields as its passing controls. *)
Example comp_obj (A : obj[Coq]) :
  fobj[StrictCat_Objects ◯ StrictCat_Indisc] A = A := eq_refl.

Example comp_map (A B : obj[Coq]) (f : A ~{Coq}~> B) (x : A) :
  fmap[StrictCat_Objects ◯ StrictCat_Indisc] f x = f x := eq_refl.

Fail Example comp_is_id :
  StrictCat_Objects ◯ StrictCat_Indisc = Id[Coq] := eq_refl.

(* [Indiscrete bool] is not degenerate in either direction: it has two
   provably DISTINCT objects, and they are nonetheless isomorphic, which
   is what "indiscrete" means and what [DiscreteCat bool] provably is
   not (§7).  So the witnesses below are not applied to a one-object
   category, and the adjunction is not being exercised at a shape where
   its content evaporates. *)
Example ind_bool_objs_distinct : (true : Indiscrete bool) = false -> False.
Proof. discriminate. Qed.

(* PRIOR ART, disclosed rather than duplicated silently: this is
   Theory/Skeleton/Separation.v's [Indiscrete_iso] -- which is already
   general in the type and the two points -- specialized at [bool].  That
   module is NOT required, for a measured reason rather than taste:
   through [Theory/Skeleton.v] it would add TEN modules to this file's
   49-module closure ([Construction/Quotient.v],
   [Construction/Subcategory.v], [Instance/Fun.v], [Instance/One.v],
   [Instance/Two.v], the three [Theory/Equivalence*] files,
   [Theory/Skeleton.v] and [Theory/Skeleton/Separation.v] itself), and
   [Instance/Fun.v] in particular is in neither this closure nor
   [Instance/Cat.v]'s.  Nothing here is claimed new. *)
(* Issue #357 work item 5 asks for two sanity checks.  The first --
   components of a discrete category are its objects -- is
   [pi0_counit_iso] in Instance/Cat/Components.v.  This is the second:
   the indiscrete category on a two-element set is CONNECTED.  It is
   pure instantiation of Structure/Groupoid/Connected.v's
   [arrow_connected] at the unique arrow, every hom of [Indiscrete]
   being [unit] -- so no zig-zag induction is performed here. *)

(* THE SHARED-MIDDLE READING COSTS NOTHING, AND THAT IS MEASURED.

   RECORDED CORRECTION.  An earlier revision read: "THE SHARED-MIDDLE
   READING COSTS A [Set] PIN, AND THAT IS MEASURED.  At its DEFAULT
   universe instance [adjoint_string] does NOT print with one
   [StrictCat_Objects]: the two occurrences elaborate at different
   instances, the second carrying a literal [Set].  So 'the two links
   share their middle term' is true only at a shared instance, and the
   shared instance pins an inner level to [Set] -- inherited from
   [Indiscrete], as §4 records."  It then checked
   [adjoint_string@{b a Set a a b a Set}], an EIGHT-universe instance with
   two literal [Set]s.

   Half of that still holds and half does not.  At its default instance
   [adjoint_string] still elaborates its two [StrictCat_Objects]
   occurrences at DIFFERENT instances -- it is now
   [adjoint_string@{u u0 u1 u2 u3 u4}], six universes, the left link at
   [{u0 u1}] and the right at [{u3 u4}] with [u1 < u0] and [u4 < u3] --
   so the shared-middle reading is still a statement about a shared
   INSTANCE and not about the default one.  What is gone is the price:
   [Indiscrete] was annotated (Instance/Discrete/Reconstruct.v, PR
   "algebraic carriers are sets", 2026-09-17), so no [Set] appears in the
   shared instance at all.  The check below identifies the two middles on
   the nose -- both print [StrictCat_Objects@{a a b a b b}] -- with the
   hom level [b] declared strictly ABOVE [Set] and the object level [a]
   strictly above [b].  Measured, not asserted. *)

Section SharedMiddle.
Universes a b c d.
Constraint Set < b.
Constraint b < a.
Check adjoint_string@{c a b d a b}.
End SharedMiddle.

Definition ind_bool_connected : Connected (Indiscrete bool) :=
  @arrow_connected (Indiscrete bool) (fun _ _ => tt).

Program Definition ind_bool_iso :
  @Isomorphism (Indiscrete bool) true false := {| to := tt; from := tt |}.

(* The transposition computes.  By [adj_to_lifts] the forward leg IS
   [indisc_lift], so these evaluate the adjunction's own [to] at a
   non-identity function. *)
Example neg_lift_true :
  fobj[indisc_lift (C := DiscreteCat bool) negb] true = false := eq_refl.

Example neg_lift_false :
  fobj[indisc_lift (C := DiscreteCat bool) negb] false = true := eq_refl.

Example counit_bool (b : bool) :
  @counit _ _ _ _ Objects_Indisc_Adjunction bool b = b := eq_refl.

Example unit_disc_bool (b : bool) :
  fobj[@unit _ _ _ _ Objects_Indisc_Adjunction (DiscreteCat bool)] b = b
  := eq_refl.
