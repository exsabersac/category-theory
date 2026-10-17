Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.

Generalizable All Variables.

(** * Limits over a shape with an initial object, computed by evaluation *)

(*
   nLab:        https://ncatlab.org/nlab/show/final+functor
   nLab:        https://ncatlab.org/nlab/show/limit

   本文件给出始对象结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The limit of a diagram over a shape with an initial object *)

Section LimitFromInitial.

Context {J C : Category}.
Context (I : @Initial J).
Context (F : J ⟶ C).

(* The leg at x is the image of the unique arrow ¡ : 0 ~> x. *)

Definition initial_leg (x : J) : F (@initial_obj J I) ~{C}~> F x :=
  fmap[F] (@zero J I x).

(* Cone coherence is uniqueness of arrows out of 0, pushed through F. *)

Lemma initial_leg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ initial_leg x ≈ initial_leg y.
Proof.
  unfold initial_leg.
  rewrite <- fmap_comp.
  apply fmap_respects.
  apply (@zero_unique J I).
Qed.

Definition initial_acone : ACone (F (@initial_obj J I)) F :=
  {| vertex_map     := initial_leg
   ; cone_coherence := @initial_leg_coherence |}.

Definition initial_cone : Cone F :=
  {| vertex_obj := F (@initial_obj J I)
   ; coneFrom   := initial_acone |}.

(* The leg AT the initial object is the identity — only up to `≈`; see the
   header's STRENGTHS paragraph for the measured rejection at `eq_refl`. *)

Lemma initial_leg_id : initial_leg (@initial_obj J I) ≈ id.
Proof.
  unfold initial_leg.
  rewrite (@zero_unique J I _ (@zero J I (@initial_obj J I)) id).
  apply fmap_id.
Qed.

(* The mediator from a competing cone is that cone's own leg at 0. *)

Definition initial_med (N : Cone F) :
  vertex_obj[N] ~{C}~> F (@initial_obj J I) :=
  cone_leg N (@initial_obj J I).

Lemma initial_med_commutes (N : Cone F) (x : J) :
  initial_leg x ∘ initial_med N ≈ cone_leg N x.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) _ _ (@zero J I x)).
Qed.

(* Uniqueness: evaluate the factorization condition at 0, where the leg is
   `≈ id`.  This is the whole content of the universal property. *)

Lemma initial_med_unique (N : Cone F)
  (v : vertex_obj[N] ~{C}~> F (@initial_obj J I)) :
  (∀ x : J, initial_leg x ∘ v ≈ cone_leg N x) → initial_med N ≈ v.
Proof.
  intro Hv.
  rewrite <- (Hv (@initial_obj J I)).
  rewrite initial_leg_id.
  now rewrite id_left.
Qed.

(* The three packagings: cone-level, apex-pinned, and bundled. *)

Definition initial_IsLimitCone : IsLimitCone initial_cone :=
  fun N =>
    {| unique_obj      := initial_med N
     ; unique_property := initial_med_commutes N
     ; uniqueness      := initial_med_unique N |}.

Definition initial_IsALimit : IsALimit F (F (@initial_obj J I)) :=
  limitcone_isalimit initial_IsLimitCone.

Definition initial_Limit : Limit F :=
  limitcone_limit initial_cone initial_IsLimitCone.

(* Strictness, measured. *)

Example initial_leg_strict (x : J) :
  limit_leg initial_IsALimit x = fmap[F] (@zero J I x) := eq_refl.

Example initial_apex_strict :
  @vertex_obj _ _ _ initial_cone = F (@initial_obj J I) := eq_refl.

Example initial_med_strict (N : Cone F) :
  limit_med initial_IsALimit N = cone_leg N (@initial_obj J I) := eq_refl.

Example initial_Limit_strict :
  @limit_cone _ _ _ initial_Limit = initial_cone := eq_refl.

(** *** The evaluation cone as a terminal object of [Cones F] *)

(* The terminal-cone reading of the same fact: the evaluation cone is a
   terminal object of Instance/Cones.v's category of cones over F.  This is
   what Instance/Cones/Limit.v's [Limit_Cones] consumes, so the two
   presentations can be compared — see [initial_Cones_strict]. *)

Program Definition initial_Cones_Terminal : @Terminal (Cones F) := {|
  terminal_obj := initial_cone;
  one          := fun N => (initial_med N; initial_med_commutes N)
|}.
Next Obligation.
  rewrite <- (initial_med_unique x f X0).
  now rewrite <- (initial_med_unique x g X).
Qed.

Example initial_Cones_strict :
  @limit_cone _ _ _ (@Limit_Cones J C F initial_Cones_Terminal)
    = initial_cone := eq_refl.

(** *** The honest biconditional *)

(* A cone over F is limiting exactly when its leg at the initial object is
   invertible.  Forward: the two mediators are mutually inverse, each round
   trip being pinned by a uniqueness clause.  Backward: that inverse is a
   cone isomorphism from the evaluation cone, along which limiting-ness
   transports. *)

Theorem limiting_iff_initial_leg_iso (N : Cone F) :
  IsLimitCone N ↔ IsIsomorphism (cone_leg N (@initial_obj J I)).
Proof.
  split.
  - intro HN.
    unshelve refine
      {| two_sided_inverse := unique_obj (HN initial_cone) |}.
    + rewrite (unique_property (HN initial_cone) (@initial_obj J I)).
      exact initial_leg_id.
    + transitivity (unique_obj (HN N)).
      * symmetry.
        apply (uniqueness (HN N)).
        intro x.
        rewrite comp_assoc.
        rewrite (unique_property (HN initial_cone) x).
        exact (initial_med_commutes N x).
      * apply (uniqueness (HN N)).
        intro x; now rewrite id_right.
  - intro Hiso.
    unshelve refine (limitcone_transport _ initial_IsLimitCone).
    unshelve eexists.
    + unshelve refine {| to   := two_sided_inverse
                       ; from := cone_leg N (@initial_obj J I) |}.
      * apply is_left_inverse.
      * apply is_right_inverse.
    + intro x; simpl.
      rewrite <- (initial_med_commutes N x).
      rewrite <- comp_assoc.
      rewrite is_right_inverse.
      now rewrite id_right.
Qed.

End LimitFromInitial.

(** ** Reading invertibility back from the opposite category *)

(* [IsIsomorphism] at C^op and at C carry the same inverse and swap their
   two law fields, so passing between them is a field permutation with no
   proof content.  Theory/Morphisms/CokernelPair.v already carries this
   pair, as [IsIsomorphism_of_op] and [op_IsIsomorphism_of]; that module is
   NOT required here — it pulls Theory/Morphisms.v, Structure/Pullback.v,
   Structure/Pushout.v, Theory/Morphisms/Stability.v and
   Theory/Morphisms/Duality.v onto every consumer — so the idiom is copied
   under names that do not collide with it. *)

Section OpIso.

Context {C : Category}.

Definition iso_of_op {a b : C} (h : b ~> a)
  (H : @IsIsomorphism (C^op) a b h) : @IsIsomorphism C b a h :=
  @Build_IsIsomorphism C b a h
    (@two_sided_inverse (C^op) a b h H)
    (@is_left_inverse (C^op) a b h H)
    (@is_right_inverse (C^op) a b h H).

Definition iso_to_op {a b : C} (h : b ~> a)
  (H : @IsIsomorphism C b a h) : @IsIsomorphism (C^op) a b h :=
  @Build_IsIsomorphism (C^op) a b h
    (@two_sided_inverse C b a h H)
    (@is_left_inverse C b a h H)
    (@is_right_inverse C b a h H).

End OpIso.

(** ** The dual: a terminal shape computes colimits by evaluation *)

(* Everything here is the section above read at J^op and C^op.
   `Initial (J^op)` is notation for `Terminal ((J^op)^op)`, and
   Construction/Opposite.v builds duality so that (J^op)^op is J on the
   nose, so a `Terminal J` IS the hypothesis the primal section wants.  The
   four packagings and the two accessors are supplied by `:=` with no
   tactic.  Of the three lemmas, only [terminal_inj_id] is a single
   [exact] of a PRIMAL lemma (`@initial_leg_id (J^op) (C^op) T (F^op)`);
   an earlier draft of this header said all three were, which is wrong on
   two counts.  [terminal_med_commutes] is a single [exact] of
   [colimit_med_commutes] — a Structure/Limit/Preservation.v ACCESSOR, not
   a primal lemma of this file — and [terminal_med_unique] introduces its
   hypothesis first, so it is TWO tactics and again of an accessor.  The
   biconditional is the primal one composed with the field permutation of
   [iso_of_op]/[iso_to_op].  No second argument is given anywhere.

   The accessors are stated covariantly, in C: no `^op` appears in any type
   below, which is the point of routing through
   Structure/Limit/Preservation.v's [Cocone], [cocone_inj], [IsAColimit],
   [colimit_inj] and [colimit_med]. *)

Section ColimitFromTerminal.

Context {J C : Category}.
Context (T : @Terminal J).
Context (F : J ⟶ C).

(* The injection at x is the image of the unique arrow ! : x ~> 1. *)

Definition terminal_inj (x : J) : F x ~{C}~> F (@terminal_obj J T) :=
  fmap[F] (@one J T x).

Definition terminal_cocone : Cocone F :=
  @initial_cone (J^op) (C^op) T (F^op).

Definition terminal_IsColimitCocone : IsColimitCocone terminal_cocone :=
  @initial_IsLimitCone (J^op) (C^op) T (F^op).

Definition terminal_IsAColimit : IsAColimit F (F (@terminal_obj J T)) :=
  @initial_IsALimit (J^op) (C^op) T (F^op).

Definition terminal_Colimit : Colimit F :=
  @initial_Limit (J^op) (C^op) T (F^op).

(* The mediator out of the colimit into a competing cocone is that
   cocone's own injection at the terminal object. *)

Definition terminal_med (N : Cocone F) :
  F (@terminal_obj J T) ~{C}~> vertex_obj[N] :=
  cocone_inj N (@terminal_obj J T).

Lemma terminal_med_commutes (N : Cocone F) (x : J) :
  terminal_med N ∘ terminal_inj x ≈ cocone_inj N x.
Proof. exact (colimit_med_commutes terminal_IsAColimit N x). Qed.

Lemma terminal_med_unique (N : Cocone F)
  (v : F (@terminal_obj J T) ~{C}~> vertex_obj[N]) :
  (∀ x : J, v ∘ terminal_inj x ≈ cocone_inj N x) → terminal_med N ≈ v.
Proof. intro Hv. exact (colimit_med_unique terminal_IsAColimit N v Hv). Qed.

Lemma terminal_inj_id : terminal_inj (@terminal_obj J T) ≈ id.
Proof. exact (@initial_leg_id (J^op) (C^op) T (F^op)). Qed.

(* Strictness of the covariant accessors, measured. *)

Example terminal_cocone_strict (x : J) :
  cocone_inj terminal_cocone x = terminal_inj x := eq_refl.

Example terminal_inj_strict (x : J) :
  colimit_inj terminal_IsAColimit x = terminal_inj x := eq_refl.

Example terminal_med_strict (N : Cocone F) :
  colimit_med terminal_IsAColimit N = terminal_med N := eq_refl.

Example terminal_apex_strict :
  colimit_apex terminal_Colimit = F (@terminal_obj J T) := eq_refl.

(* The dual biconditional.  The primal theorem supplies both directions
   with no second argument; the only residue is that invertibility at C^op
   and at C are the same data in a different field order, which [iso_of_op]
   and [iso_to_op] permute. *)

Definition colimiting_iff_terminal_inj_iso (N : Cocone F) :
  IsColimitCocone N ↔ IsIsomorphism (cocone_inj N (@terminal_obj J T)) :=
  (fun H => iso_of_op _
     (fst (@limiting_iff_initial_leg_iso (J^op) (C^op) T (F^op) N) H),
   fun H => snd (@limiting_iff_initial_leg_iso (J^op) (C^op) T (F^op) N)
     (iso_to_op _ H)).

End ColimitFromTerminal.

(** ** Deliverable: the point shape (Seven Sketches §3.5.3 Ex 3.98) *)

(* `_1` has an initial object — its unique object — and that instance did
   not exist: Instance/One.v's [Cat_Terminal] says `_1` is terminal in
   Cat, a different statement (see the header). *)

Program Definition One_Initial : @Initial _1 := {|
  terminal_obj := ttt;
  one          := fun _ => ttt
|}.
Next Obligation. now destruct f, g. Qed.

(* The limit of a diagram of shape 1 is its value at the point.  This is
   the section-1 theorem instantiated, not a second construction. *)

Definition point_cone {C : Category} (F : _1 ⟶ C) : Cone F :=
  @initial_cone _1 C One_Initial F.

Definition point_IsALimit {C : Category} (F : _1 ⟶ C) :
  IsALimit F (F ttt) := @initial_IsALimit _1 C One_Initial F.

Definition point_Limit {C : Category} (F : _1 ⟶ C) : Limit F :=
  @initial_Limit _1 C One_Initial F.

(* The cross-check the exercise asks for: the same cone is a TERMINAL
   OBJECT of the category of cones, and the [Limit] that
   Instance/Cones/Limit.v reads off it is the very cone built above. *)

Definition point_Cones_Terminal {C : Category} (F : _1 ⟶ C) :
  @Terminal (Cones F) := @initial_Cones_Terminal _1 C One_Initial F.

Example point_Cones_strict {C : Category} (F : _1 ⟶ C) :
  @limit_cone _ _ _ (@Limit_Cones _1 C F (point_Cones_Terminal F))
    = point_cone F := eq_refl.

(** *** A computing witness in Sets *)

(* [bool_set] is a REDUNDANT REDECLARATION, and an earlier draft of this
   note gave a reason for it that is false.  That draft said the tree had
   TWO [bool_setoid_object] definitions, in Theory/Concrete.v and
   Theory/Algebra/Rig.v, "neither of which this file has any other reason
   to require".  There are FIVE, and one of them — Instance/Sets.v,
   `bool_setoid_object@{t u}` — is byte-identical in content to [bool_set]
   and lives in a module this file ALREADY requires.  It is
   convertible on the nose (`bool_setoid_object = bool_set := eq_refl`
   compiles against this file's own import list, no new Require), and both
   [Sets] witnesses below replay verbatim against it.  So the copy was
   never forced.  It is kept rather than removed because deleting it is a
   code change, not a correction of the record.  The cone apex, by
   contrast, IS reused
   — it is Instance/Sets.v's terminal singleton, so a cone over a point
   diagram with that apex is literally a global element, and the mediator
   below is the element it names. *)

Program Definition bool_set : obj[Sets] :=
  {| carrier := bool ; is_setoid := {| equiv := eq |} |}.

Program Definition elt_acone (b : bool) :
  ACone (@terminal_obj Sets Sets_Terminal) (=(bool_set)) := {|
  vertex_map := fun _ => {| morphism := fun _ => b |}
|}.

Definition elt_cone (b : bool) : Cone (=(bool_set)) :=
  {| vertex_obj := @terminal_obj Sets Sets_Terminal
   ; coneFrom   := elt_acone b |}.

Example point_Sets_apex :
  @vertex_obj _ _ _ (@limit_cone _ _ _ (point_Limit (=(bool_set))))
    = bool_set := eq_refl.

(* The mediator computes: it is the element the competing cone names. *)

Example point_Sets_med (b : bool) :
  limit_med (point_IsALimit (=(bool_set))) (elt_cone b) ttt = b := eq_refl.

(* Non-degeneracy, and it is worth being exact about what this adds.  The
   identification `limit_med … N = cone_leg N 0` holds at ARBITRARY
   arguments ([initial_med_strict]), so instantiating it proves nothing on
   its own.  What is specific to this diagram is that two cones over it
   have provably different mediators, so the limit apex has at least two
   distinct elements.  Be exact about the MECHANISM too: because the
   mediator is DEFINITIONALLY the cone's leg, the statement reduces to
   `true <> false` and [discriminate] closes it — no commutation or
   uniqueness lemma is consumed, so it is not the universal property that
   separates, as an earlier draft of this note said.  What the example
   establishes is the apex's two distinct elements, which is what makes
   the corollary non-degenerate: over a subsingleton apex any two
   mediators would agree automatically. *)

Example point_Sets_separates :
  limit_med (point_IsALimit (=(bool_set))) (elt_cone true) ttt
    <> limit_med (point_IsALimit (=(bool_set))) (elt_cone false) ttt.
Proof. discriminate. Qed.

(** ** Deliverable: successor ordinals (Riehl §3.1) *)

(* The top stage of `Ordinal (S n)`, and its bottom stage, neither of which
   was named in Instance/Ordinal.v. *)

Definition ord_top (n : nat) : Ord_obj (S n) := ord_at n le_t_n.

Definition ord_bot (n : nat) : Ord_obj (S n) :=
  ord_at 0 (le_t_SS (le_t_zero n)).

Lemma ord_top_neq_bot (n : nat) : ord_top (S n) <> ord_bot (S n).
Proof. intro H; discriminate (f_equal ord_val H). Qed.

(* The top stage is terminal: the arrow from x is the bound of x with one
   successor peeled off both sides, and uniqueness is thinness of `le_t`. *)

Program Definition Ordinal_Succ_Terminal (n : nat) :
  @Terminal (Ordinal (S n)) := {|
  terminal_obj := ord_top n;
  one          := fun x => le_t_SS_inv (ord_bound x)
|}.
Next Obligation. apply le_t_irr. Qed.

(* Hence: the colimit of a diagram indexed by a successor ordinal is its
   value at the top stage. *)

Definition ordinal_succ_IsAColimit {n : nat} {C : Category}
  (G : Ordinal (S n) ⟶ C) : IsAColimit G (G (ord_top n)) :=
  @terminal_IsAColimit (Ordinal (S n)) C (Ordinal_Succ_Terminal n) G.

Definition ordinal_succ_Colimit {n : nat} {C : Category}
  (G : Ordinal (S n) ⟶ C) : Colimit G :=
  @terminal_Colimit (Ordinal (S n)) C (Ordinal_Succ_Terminal n) G.

(* A witness whose diagram genuinely varies from stage to stage:
   Instance/Ordinal.v's embedding of `Ordinal (S n)` into ω sends a stage
   to its own index, so the colimit apex is the numeral n and the bottom
   stage is 0.  The same honesty note applies as in the [Sets] witness:
   `colimit_apex … = G (ord_top n)` holds at ARBITRARY G
   ([terminal_apex_strict]), so the apex computation alone shows nothing.
   What is specific here is [ordinal_omega_nonconstant] — the diagram takes
   different values at the bottom and top stages, so "the colimit is the
   value at the top stage" is not a statement about a constant diagram. *)

Example ordinal_omega_apex (n : nat) :
  colimit_apex (ordinal_succ_Colimit (Ord_Omega (S n))) = n := eq_refl.

Example ordinal_omega_bot (n : nat) :
  Ord_Omega (S n) (ord_bot n) = 0%nat := eq_refl.

Lemma ordinal_omega_nonconstant (n : nat) :
  Ord_Omega (S (S n)) (ord_bot (S n))
    <> Ord_Omega (S (S n)) (ord_top (S n)).
Proof. discriminate. Qed.

(** *** Why ω itself is outside the colimit half of the theorem *)

(* ω has an initial object, so LIMITS over ω are evaluation at stage 0 by
   the first section — and provably no terminal object, so the second
   section says nothing about colimits over ω.  That asymmetry is Riehl's
   reason for indexing sequential colimits by ω rather than by a successor
   ordinal: over a successor ordinal the colimit is the top stage and
   nothing is glued.  Note that `Ordinal (S n)` is a FINITE successor
   ordinal; ω+1 is not a category in this tree and is not claimed to be. *)

Program Definition Omega_Initial : @Initial Omega := {|
  terminal_obj := 0%nat;
  one          := fun x => le_t_zero x
|}.
Next Obligation. apply le_t_irr. Qed.

Theorem Omega_no_Terminal : @Terminal Omega → False.
Proof.
  intro T.
  exact (le_t_no_desc (@one Omega T (S (@terminal_obj Omega T)))).
Qed.
