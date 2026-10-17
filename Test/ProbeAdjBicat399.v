Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Bicategory.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Square.
Require Import Category.Instance.Adjoints.
Require Import Category.Instance.Adj.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Instance.Adj.Bicategory.

Generalizable All Variables.

(** * Probe for Instance/Adj/Bicategory.v *)

(*
   本文件为测试：ProbeAdjBicat399。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ---------------------------------------------------------------------- *)
(* INSTRUMENT.  A passing [Fail] prints nothing under this repo's coqc, so *)
(* this command establishes that [Fail] is doing anything at all.          *)
(* ---------------------------------------------------------------------- *)

Fail Check p399_no_such_constant_anywhere.

(* ---------------------------------------------------------------------- *)
(* GUARD BLOCK.  Every constant that any negative below names, target and  *)
(* donor alike, is named here OUTSIDE every [Fail], so that renaming any   *)
(* one of them breaks this file at a [Check] line rather than turning a    *)
(* negative vacuously green.                                              *)
(* ---------------------------------------------------------------------- *)

Check @Category.
Check @Functor.
Check @Transform.
Check @Adjunction.
Check @Compose.
Check @Id.
Check @Isomorphism.
Check @Bicategory.
Check @eq.
Check @obj.
Check @hom.
Check @homset.
Check @id.
Check @compose.
Check @compose_respects.
Check @id_left.
Check @id_right.
Check @comp_assoc.
Check @comp_assoc_sym.
Check @fobj.
Check @fmap.
Check @transform.
Check @nat_hcompose.

Check @Adjunction_Compose.
Check @Adjunction_Id.
Check @Adjunction_Compose_adj_comp_to.
Check @Adjunction_Compose_adj_comp_from.
Check @paste_v_sigma.
Check @paste_v_tau.
Check @Adjoints.
Check @adjunction.
Check @free_functor.
Check @forgetful_functor.
Check @Cat_Hcompose.
Check @Build_Bicategory.
Check @Build_Bicategory'.

Check @AdjObj.
Check @ConjPair.
Check @Adj.
Check @adjobj_left.
Check @adjobj_right.
Check @adjobj_adj.

Check @conjugate_hcompose.
Check @conj_padL.
Check @conj_padR.
Check @routeb_hyp.
Check @routeb_sigma.
Check @routeb_tau.
Check @conjugate_hcompose_via_square.
Check @nat_hcompose_interchange.
Check @AdjIdObj.
Check @adjobj_hcompose.
Check @conj_pair_hcompose.
Check @Adj_Hcompose.
Check @Adj_Hcompose_shape.
Check @hcomp_obj_adj.
Check @hcomp_obj_left.
Check @hcomp_obj_right.
Check @hcomp_left_is_nat_hcompose.
Check @hcomp_right_is_nat_hcompose.
Check @conj_interchange.
Check @Adj_hunit_left.
Check @Adj_hunit_right.
Check @Adj_hassoc.
Check @hunit_left_obj_left.
Check @hunit_left_obj_right.
Check @hunit_right_obj_left.
Check @hunit_right_obj_right.
Check @adj_hcomp2.
Check @Adj_hunit_left_natural.
Check @Adj_hunit_right_natural.
Check @Adj_hassoc_natural.
Check @Adj_triangle.
Check @Adj_pentagon.
Check @Adj_Bicategory.
Check @Adj_bicat_is_Adj.
Check @adjobj_of_morphism.
Check @morphism_of_adjobj.
Check @adjoints_round_record.

(* ====================================================================== *)
(* (1) N1-N6.  The 1-cell layer of [Adj] is WEAK: neither associativity   *)
(*     nor either unit law of [Adjunction_Compose] is even statable, and  *)
(*     one level down the functor equations are statable and refused at   *)
(*     conversion.                                                        *)
(* ====================================================================== *)

Section P399Assoc.

Context {D C E Z : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (Aa : F ⊣ U).
Context {G : C ⟶ E} {V : E ⟶ C} (Bb : G ⊣ V).
Context {H : E ⟶ Z} {W : Z ⟶ E} (Cc : H ⊣ W).

(* -- N1 (TYPING).  CONTROLS: both bracketings elaborate; what is        -- *)
(* -- refused is the EQUATION, whose two sides do not share a type.      -- *)

Check (@Adjunction_Compose E D Z (G ◯ F) (U ◯ V) H W
         (@Adjunction_Compose C D E F U G V Aa Bb) Cc).
Check (@Adjunction_Compose C D Z F U (H ◯ G) (V ◯ W) Aa
         (@Adjunction_Compose E C Z G V H W Bb Cc)).

Fail Example n1 :
  @eq (@Adjunction Z D (H ◯ (G ◯ F)) (U ◯ V ◯ W))
      (@Adjunction_Compose E D Z (G ◯ F) (U ◯ V) H W
         (@Adjunction_Compose C D E F U G V Aa Bb) Cc)
      (@Adjunction_Compose C D Z F U (H ◯ G) (V ◯ W) Aa
         (@Adjunction_Compose E C Z G V H W Bb Cc)) := eq_refl.

(* -- N2/N3 (TYPING).  CONTROLS: both padded composites elaborate.       -- *)

Check (@Adjunction_Compose C D C F U Id[C] Id[C] Aa (@Adjunction_Id C)).
Check (@Adjunction_Compose D D C Id[D] Id[D] F U (@Adjunction_Id D) Aa).

Fail Example n2 :
  @eq (@Adjunction C D F U) Aa
      (@Adjunction_Compose C D C F U Id[C] Id[C] Aa (@Adjunction_Id C))
  := eq_refl.

Fail Example n3 :
  @eq (@Adjunction C D F U) Aa
      (@Adjunction_Compose D D C Id[D] Id[D] F U (@Adjunction_Id D) Aa)
  := eq_refl.

(* -- N4-N6 (CONVERSION).  CONTROLS: [fobj] and [fmap] agree on the      -- *)
(* -- nose on both sides, so what the three negatives locate is the      -- *)
(* -- three LAW fields of [Compose] and neither data field.              -- *)

Example c399_n4a (o : D) :
  @eq (obj[Z]) (fobj[H ◯ G ◯ F] o) (fobj[H ◯ (G ◯ F)] o) := eq_refl.

Example c399_n4b (o1 o2 : D) (f : o1 ~> o2) :
  @eq (fobj[H ◯ G ◯ F] o1 ~{Z}~> fobj[H ◯ G ◯ F] o2)
      (fmap[H ◯ G ◯ F] f) (fmap[H ◯ (G ◯ F)] f) := eq_refl.

Fail Example n4 : @eq (D ⟶ Z) (H ◯ G ◯ F) (H ◯ (G ◯ F)) := eq_refl.

Example c399_n56a (o : D) :
  @eq (obj[C]) (fobj[Id[C] ◯ F] o) (fobj[F] o) := eq_refl.

Example c399_n56b (o : D) :
  @eq (obj[C]) (fobj[F ◯ Id[D]] o) (fobj[F] o) := eq_refl.

Fail Example n5 : @eq (D ⟶ C) (Id[C] ◯ F) F := eq_refl.

Fail Example n6 : @eq (D ⟶ C) (F ◯ Id[D]) F := eq_refl.

End P399Assoc.

(* ====================================================================== *)
(* (2) N7-N10.  The same three laws one level up, at [AdjObj]: both unit  *)
(*     laws, associativity, and the left-adjoint component of the first.  *)
(* ====================================================================== *)

Section P399AdjObj.

Context {x y z w : Category}.
Context (a : AdjObj x y) (b : AdjObj y z) (c : AdjObj z w).

(* -- CONTROLS: the target's own four [eq_refl] readbacks, which say     -- *)
(* -- what the padded 1-cell's two adjoints ARE.                         -- *)

Example c399_n7 :
  @eq (y ⟶ x) (adjobj_left (adjobj_hcompose (AdjIdObj y) a))
              (adjobj_left a ◯ Id[y])
  := @hunit_left_obj_left x y a.

Example c399_n8 :
  @eq (x ⟶ y) (adjobj_right (adjobj_hcompose (AdjIdObj y) a))
              (Id[y] ◯ adjobj_right a)
  := @hunit_left_obj_right x y a.

Example c399_n9 :
  @eq (y ⟶ x) (adjobj_left (adjobj_hcompose a (AdjIdObj x)))
              (Id[x] ◯ adjobj_left a)
  := @hunit_right_obj_left x y a.

Example c399_n10 :
  @eq (x ⟶ y) (adjobj_right (adjobj_hcompose a (AdjIdObj x)))
              (adjobj_right a ◯ Id[x])
  := @hunit_right_obj_right x y a.

Fail Example n7 :
  @eq (AdjObj x y) (adjobj_hcompose (AdjIdObj y) a) a := eq_refl.

Fail Example n8 :
  @eq (AdjObj x y) (adjobj_hcompose a (AdjIdObj x)) a := eq_refl.

Fail Example n9 :
  @eq (AdjObj x w) (adjobj_hcompose (adjobj_hcompose c b) a)
                   (adjobj_hcompose c (adjobj_hcompose b a)) := eq_refl.

Fail Example n10 :
  @eq (y ⟶ x) (adjobj_left (adjobj_hcompose (AdjIdObj y) a))
              (adjobj_left a) := eq_refl.

End P399AdjObj.

(* ====================================================================== *)
(* (3) N11, N12.  Route (b): the sigma leg of Adjunction/Square.v's       *)
(*     vertical paste IS the Godement product componentwise; the tau leg  *)
(*     is not, and as a WHOLE transformation neither leg has the type     *)
(*     [nat_hcompose] has.                                                *)
(* ====================================================================== *)

Section P399RouteB.

Context {C D E : Category}.
Context {F F' : D ⟶ C} {U U' : C ⟶ D}.
Context {G G' : C ⟶ E} {V V' : E ⟶ C}.

(* -- CONTROL for N11: the target's [routeb_tau], the same statement     -- *)
(* -- at [~=], one application of [naturality].                          -- *)

Example c399_n11 (t : U ⟹ U') (tb : V ⟹ V') (e : E) :
  paste_v_tau Id[D] Id[C] Id[E] (conj_padR t) (conj_padR tb) e
    ≈ nat_hcompose t tb e
  := @routeb_tau C D E U U' V V' t tb e.

(* -- CONTROL for N12: the target's [routeb_sigma], the sigma leg at a   -- *)
(* -- COMPONENT and at [eq_refl].                                        -- *)

Example c399_n12 (s : F' ⟹ F) (sb : G' ⟹ G) (o : D) :
  paste_v_sigma Id[D] Id[C] Id[E] (conj_padL s) (conj_padL sb) o
    = nat_hcompose sb s o
  := @routeb_sigma C D E F F' G G' s sb o.

Fail Example n11 (t : U ⟹ U') (tb : V ⟹ V') (e : E) :
  @eq (fobj[U] (fobj[V] e) ~{D}~> fobj[U'] (fobj[V'] e))
      (paste_v_tau Id[D] Id[C] Id[E] (conj_padR t) (conj_padR tb) e)
      (nat_hcompose t tb e) := eq_refl.

Fail Example n12 (s : F' ⟹ F) (sb : G' ⟹ G) :
  @eq (@Transform D E (G' ◯ F') (G ◯ F))
      (paste_v_sigma Id[D] Id[C] Id[E] (conj_padL s) (conj_padL sb))
      (nat_hcompose sb s) := eq_refl.

End P399RouteB.

(* ====================================================================== *)
(* (4) N13, N14.  The bridge to Instance/Adjoints.v: that category        *)
(*     composes by [adj_comp], whose composite is NOT [Adjunction_Compose] *)
(*     at conversion though the two share a type; and the sigT round trip *)
(*     does not close where the record one does.                          *)
(* ====================================================================== *)

Section P399Adjoints.

Context {A1 B1 C1 : Category}.
Context (mA : B1 ~{Adjoints}~> C1) (mB : A1 ~{Adjoints}~> B1).
Context (xo : AdjObj A1 B1).

(* -- CONTROLS for N13: both sides elaborate, at one and the same type.  -- *)

Check (adjunction (mA ∘ mB)).
Check (@Adjunction_Compose B1 C1 A1
         (free_functor mA) (forgetful_functor mA)
         (free_functor mB) (forgetful_functor mB)
         (adjunction mA) (adjunction mB)).

(* -- CONTROL for N13, the positive half already in tree: the two        -- *)
(* -- constructions have definitionally equal transposes.                -- *)

Example c399_n13a (o : C1) (p : A1)
  (f : fobj[free_functor mB] (fobj[free_functor mA] o) ~{A1}~> p) :
  to (@adj _ _ _ _ (@Adjunction_Compose B1 C1 A1
        (free_functor mA) (forgetful_functor mA)
        (free_functor mB) (forgetful_functor mB)
        (adjunction mA) (adjunction mB)) o p) f
    ≈ to (@adj _ _ _ _ (adj_comp (free_functor mB) (forgetful_functor mB)
            (free_functor mA) (forgetful_functor mA)
            (adjunction mB) (adjunction mA)) o p) f
  := @Adjunction_Compose_adj_comp_to B1 C1 A1
       (free_functor mA) (forgetful_functor mA)
       (free_functor mB) (forgetful_functor mB)
       (adjunction mA) (adjunction mB) o p f.

(* -- CONTROL for N14: the RECORD round trip closes at [eq_refl].        -- *)

Example c399_n14 : morphism_of_adjobj (adjobj_of_morphism mA) = mA
  := @adjoints_round_record B1 C1 mA.

Fail Example n13 :
  @eq (@Adjunction A1 C1 (free_functor mB ◯ free_functor mA)
                   (forgetful_functor mA ◯ forgetful_functor mB))
      (adjunction (mA ∘ mB))
      (@Adjunction_Compose B1 C1 A1
         (free_functor mA) (forgetful_functor mA)
         (free_functor mB) (forgetful_functor mB)
         (adjunction mA) (adjunction mB)) := eq_refl.

Fail Example n14 :
  @eq (AdjObj A1 B1) (adjobj_of_morphism (morphism_of_adjobj xo)) xo
  := eq_refl.

End P399Adjoints.

(* ====================================================================== *)
(* (5) N15.  [Build_Bicategory'] churns: its [symmetry]-derived           *)
(*     [comp_assoc_sym] breaks record eta, [bicat x y] is then no longer  *)
(*     [Adj x y], and [Adj_Hcompose] no longer typechecks against         *)
(*     [hcompose].  The twenty arguments below are the twenty-one         *)
(*     [Adj_Bicategory] passes to the raw constructor, less the           *)
(*     [comp_assoc_sym] that this one derives.                            *)
(* ====================================================================== *)

(* -- CONTROL: the raw-constructor build, which does typecheck.          -- *)

Check @Adj_Bicategory.

Fail Definition n15 : Bicategory :=
  Build_Bicategory'
    Category
    (fun C D => @obj (Adj C D))
    (fun C D => @hom (Adj C D))
    (@AdjIdObj)
    (fun C D => @homset (Adj C D))
    (fun C D => @id (Adj C D))
    (fun C D => @compose (Adj C D))
    (fun C D => @compose_respects (Adj C D))
    (fun C D => @id_left (Adj C D))
    (fun C D => @id_right (Adj C D))
    (fun C D => @comp_assoc (Adj C D))
    (@Adj_Hcompose)
    (fun C D f => Adj_hunit_left f)
    (fun C D f => Adj_hunit_right f)
    (@Adj_hassoc)
    (@Adj_hunit_left_natural)
    (@Adj_hunit_right_natural)
    (@Adj_hassoc_natural)
    (@Adj_triangle)
    (@Adj_pentagon).

(* ====================================================================== *)
(* (6) N16-N24 (FORMABILITY): hom = proof.  The identification every      *)
(*     constant of the target carries in its BINDER is INHERITED, and     *)
(*     [Compose] is a donor of it on its own -- N20 refuses [Gq (o) Fq]   *)
(*     with no adjunction and no transformation anywhere in the command,  *)
(*     while a [Transform] between two functors is accepted.              *)
(* ====================================================================== *)

Section P399UnivHomProof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu Du Eu : Category@{co ch cp}).

(* CONTROLS, all accepted at these very levels. *)

Check (fun o1 o2 : Cu => o1 ~{Cu}~> o2).
Check (fun o : Cu => @id Cu o).
Check (Cu ⟶ Du).
Check (Du ⟶ Cu).
Check (fun Fq Gq : Cu ⟶ Du => Fq ⟹ Gq).

(* -- N16.  [Adjunction] is a donor.                                     -- *)

Fail Check (fun (Fq : Du ⟶ Cu) (Uq : Cu ⟶ Du) => Fq ⊣ Uq).

(* -- N17-N19.  [AdjObj], [Adj] and [ConjPair] inherit it.  NOTE that    -- *)
(* -- [AdjObj] contains an [Adjunction] and [ConjPair] two [AdjObj]s, so -- *)
(* -- neither can be tested apart from its donor: N17-N19 record that     -- *)
(* -- the identification reaches them, not that they add one.            -- *)

Fail Check (AdjObj Cu Du).

Fail Check (Adj Cu Du).

Fail Check (fun o1 o2 : AdjObj Cu Du => @ConjPair Cu Du o1 o2).

(* -- N20, N21.  [Compose] refuses on its own; [nat_hcompose] refuses    -- *)
(* -- because its result type mentions [Compose], the [Transform]        -- *)
(* -- control above having been accepted.                                -- *)

Fail Check (fun (Fq : Cu ⟶ Du) (Gq : Du ⟶ Eu) => Gq ◯ Fq).

Fail Check (fun (F1 G1 : Cu ⟶ Du) (J1 K1 : Du ⟶ Eu)
                (aa : J1 ⟹ K1) (bb : F1 ⟹ G1) => nat_hcompose aa bb).

(* -- N22-N24.  Cat's own horizontal composition and the target's two    -- *)
(* -- 1-cell and bifunctor constants, all inheriting.                    -- *)

Fail Check (@Cat_Hcompose Cu Du Eu).

Fail Check (@adjobj_hcompose Cu Du Eu).

Fail Check (@Adj_Hcompose Cu Du Eu).

End P399UnivHomProof.

(* ====================================================================== *)
(* (7) N25, N26 (FORMABILITY): the two categories' HOM LEVELS.  Functors  *)
(*     in BOTH directions identify them before any adjunction is formed,  *)
(*     and [AdjObj] carries functors in both directions.                  *)
(* ====================================================================== *)

Section P399UnivHomLevels.

Universes ao ah bo bh.
Constraint ah < bh.

Context (Aq : Category@{ao ah ah}).
Context (Bq : Category@{bo bh bh}).

Check (Aq ⟶ Bq).
Check (fun o1 o2 : Aq => o1 ~{Aq}~> o2).
Check (fun o1 o2 : Bq => o1 ~{Bq}~> o2).
Check (fun o : Aq => @id Aq o).

Fail Check (Bq ⟶ Aq).

Fail Check (AdjObj Aq Bq).

End P399UnivHomLevels.
