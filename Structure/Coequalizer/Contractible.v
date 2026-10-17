Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.

Generalizable All Variables.

(** * Contractible pairs, and the coequalizers that are split *)

(*
   nLab:   https://ncatlab.org/nlab/show/split+coequalizer, the section

   本文件给出相关范畴论结构的定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The definition *)

(* A contraction t of the pair: a section of f through which g ∘ t
   coforks the pair. *)
Record ContractiblePair {C : Category} {x y : C} (f g : x ~> y) := {
  contr_t : y ~> x;                                (* the contraction *)

  contr_section : f ∘ contr_t ≈ id;                (* ∂₀ t = 1 *)
  contr_cofork  : g ∘ contr_t ∘ f ≈ g ∘ contr_t ∘ g
                                                   (* ∂₁ t ∂₀ = ∂₁ t ∂₁ *)
}.

Arguments contr_t       {_ _ _ _ _} _.
Arguments contr_section {_ _ _ _ _} _.
Arguments contr_cofork  {_ _ _ _ _} _.

(** ** (a) The pair of a split fork is contractible *)

(* t is the split fork's t: law 3 is ∂₀ t = 1, and g t f = s e f = s e g
   = g t g by laws 4, 1 and 4. *)
Definition split_coequalizer_contractible {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) : ContractiblePair f g.
Proof.
  unshelve refine {| contr_t := scoeq_t S; contr_section := scoeq_law3 S |}.
  transitivity (scoeq_s S ∘ scoeq_e S ∘ f).
  { (* law 4 *)
    refine (compose_respects _ _ (scoeq_law4 S) _ _ _).
    reflexivity. }
  transitivity (scoeq_s S ∘ scoeq_e S ∘ g).
  { (* law 1, under s *)
    transitivity (scoeq_s S ∘ (scoeq_e S ∘ f)).
    { symmetry.
      apply comp_assoc. }
    transitivity (scoeq_s S ∘ (scoeq_e S ∘ g)).
    { refine (compose_respects _ _ _ _ _ (scoeq_law1 S)).
      reflexivity. }
    apply comp_assoc. }
  (* law 4 *)
  refine (compose_respects _ _ _ _ _ _).
  - symmetry.
    exact (scoeq_law4 S).
  - reflexivity.
Defined.

Example split_coequalizer_contractible_t {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) :
  contr_t (split_coequalizer_contractible S) = scoeq_t S := eq_refl.

(** ** (b) A coequalizer of a contractible pair is split *)

(* On the same object and arrow: s is the descent of g ∘ t through e,
   which the second equation makes possible; then s e = g t is law 4, and
   e s e = e g t = e f t = e gives law 2, e being epic. *)
Definition contractible_coequalizer_split {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) : SplitCoequalizer f g.
Proof.
  unshelve refine
    {| scoeq_obj := q
     ; scoeq_e   := e
     ; scoeq_s   := unique_obj (coeq_desc E (g ∘ contr_t P) (contr_cofork P))
     ; scoeq_t   := contr_t P |}.
  - (* law 1 *)
    exact (cofork E).
  - (* law 2: (e ∘ s) ∘ e ≈ id ∘ e, then e is epic *)
    apply (@epic _ _ _ e (coequalizer_epic f g E)).
    transitivity
      (e ∘ (unique_obj (coeq_desc E (g ∘ contr_t P) (contr_cofork P)) ∘ e)).
    { symmetry.
      apply comp_assoc. }
    transitivity (e ∘ (g ∘ contr_t P)).
    { refine (compose_respects _ _ _ _ _
                (unique_property
                   (coeq_desc E (g ∘ contr_t P) (contr_cofork P)))).
      reflexivity. }
    transitivity (e ∘ g ∘ contr_t P).
    { apply comp_assoc. }
    transitivity (e ∘ f ∘ contr_t P).
    { refine (compose_respects _ _ _ _ _ _).
      - symmetry.
        exact (cofork E).
      - reflexivity. }
    transitivity (e ∘ (f ∘ contr_t P)).
    { symmetry.
      apply comp_assoc. }
    transitivity (e ∘ id).
    { refine (compose_respects _ _ _ _ _ (contr_section P)).
      reflexivity. }
    transitivity e.
    { apply id_right. }
    symmetry.
    apply id_left.
  - (* law 3 *)
    exact (contr_section P).
  - (* law 4 *)
    symmetry.
    exact (unique_property (coeq_desc E (g ∘ contr_t P) (contr_cofork P))).
Defined.

Example contractible_coequalizer_split_obj {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_obj (contractible_coequalizer_split P E) = q := eq_refl.

Example contractible_coequalizer_split_e {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_e (contractible_coequalizer_split P E) = e := eq_refl.

Example contractible_coequalizer_split_s {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_s (contractible_coequalizer_split P E)
    = unique_obj (coeq_desc E (g ∘ contr_t P) (contr_cofork P)) := eq_refl.

Example contractible_coequalizer_split_t {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_t (contractible_coequalizer_split P E) = contr_t P := eq_refl.

(* Given the coequalizer and the contraction, s is unique up to ≈: any s'
   satisfying law 4 is the descent of g ∘ t. *)
Lemma contractible_coequalizer_split_s_unique {C : Category} {x y : C}
  {f g : x ~> y} (P : ContractiblePair f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) (s : q ~> y) (Hs : g ∘ contr_t P ≈ s ∘ e) :
  scoeq_s (contractible_coequalizer_split P E) ≈ s.
Proof.
  exact (uniqueness (coeq_desc E (g ∘ contr_t P) (contr_cofork P)) s
           (symmetry Hs)).
Qed.

(** ** "Any (and hence every) coequalizer is split" *)

Definition every_coequalizer_split {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) : SplitCoequalizer f g :=
  contractible_coequalizer_split (split_coequalizer_contractible S) E.

Example every_coequalizer_split_obj {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_obj (every_coequalizer_split S E) = q := eq_refl.

Example every_coequalizer_split_e {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_e (every_coequalizer_split S E) = e := eq_refl.

(* Every coequalizer of the pair is split by the same t. *)
Example every_coequalizer_split_t {C : Category} {x y : C}
  {f g : x ~> y} (S : SplitCoequalizer f g) {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) :
  scoeq_t (every_coequalizer_split S E) = scoeq_t S := eq_refl.

(** ** The characterization *)

(* A pair has a split coequalizer exactly when it is contractible and has
   a coequalizer: (a) and Mac Lane's Lemma one way, (b) the other. *)
Definition split_coequalizer_iff_contractible {C : Category} {x y : C}
  (f g : x ~> y) :
  SplitCoequalizer f g ↔
  (ContractiblePair f g ∧ ∃ (q : C) (e : y ~> q), IsCoequalizer f g q e).
Proof.
  split.
  - intros S.
    split.
    + exact (split_coequalizer_contractible S).
    + exists (scoeq_obj S), (scoeq_e S).
      exact (split_coequalizer_is_coequalizer f g S).
  - intros [P [q [e E]]].
    exact (contractible_coequalizer_split P E).
Defined.

(** ** The pair (1, i) of an idempotent *)

(* Contracted by 1: the second equation is i ∘ 1 ∘ 1 ≈ i ∘ 1 ∘ i, both
   sides being i up to ≈, the right one by idempotence. *)
Definition idempotent_contractible {C : Category} {x : C} (i : x ~> x)
  (I : Idempotent i) : ContractiblePair id i.
Proof.
  unshelve refine {| contr_t := id; contr_section := id_left id |}.
  transitivity i.
  - transitivity (i ∘ id).
    + apply id_right.
    + apply id_right.
  - transitivity (i ∘ i).
    + symmetry.
      exact idem.
    + refine (compose_respects _ _ _ _ _ _).
      * symmetry.
        apply id_right.
      * reflexivity.
Defined.

(* A coequalizer r of (1, i) splits i through r: s ∘ r ≈ i is law 4 of
   (b), i ∘ 1 ≈ s ∘ r, and r ∘ s ≈ 1 is its law 2. *)
Definition coequalizer_splits_idempotent {C : Category} {x : C}
  (i : x ~> x) (I : Idempotent i) {q : C} {r : x ~> q}
  (E : IsCoequalizer id i q r) : @SplitIdempotent C x q.
Proof.
  unshelve refine
    {| split_idem   := i
     ; split_idem_r := r
     ; split_idem_s := scoeq_s (contractible_coequalizer_split
                                  (idempotent_contractible i I) E) |}.
  - (* s ∘ r ≈ i *)
    symmetry.
    transitivity (i ∘ id).
    + symmetry.
      apply id_right.
    + exact (scoeq_law4 (contractible_coequalizer_split
                           (idempotent_contractible i I) E)).
  - (* r ∘ s ≈ 1 *)
    exact (scoeq_law2 (contractible_coequalizer_split
                         (idempotent_contractible i I) E)).
Defined.

Example coequalizer_splits_idempotent_idem {C : Category} {x : C}
  (i : x ~> x) (I : Idempotent i) {q : C} {r : x ~> q}
  (E : IsCoequalizer id i q r) :
  @split_idem C x q (coequalizer_splits_idempotent i I E) = i := eq_refl.

Example coequalizer_splits_idempotent_r {C : Category} {x : C}
  (i : x ~> x) (I : Idempotent i) {q : C} {r : x ~> q}
  (E : IsCoequalizer id i q r) :
  @split_idem_r C x q (coequalizer_splits_idempotent i I E) = r := eq_refl.

(** ** Functors preserve contractible pairs *)

Theorem functor_preserves_contractible@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) :
  ContractiblePair f g → ContractiblePair (fmap[F] f) (fmap[F] g).
Proof.
  intros P.
  unshelve refine {| contr_t := fmap[F] (contr_t P) |}.
  - (* F f ∘ F t ≈ F (f ∘ t) ≈ F id ≈ id *)
    transitivity (fmap[F] (f ∘ contr_t P)).
    + symmetry.
      apply fmap_comp.
    + transitivity (fmap[F] (@id C y)).
      * apply fmap_respects.
        exact (contr_section P).
      * apply fmap_id.
  - (* F g ∘ F t ∘ F f ≈ F (g ∘ t ∘ f) ≈ F (g ∘ t ∘ g) ≈ F g ∘ F t ∘ F g *)
    transitivity (fmap[F] (g ∘ contr_t P ∘ f)).
    { transitivity (fmap[F] (g ∘ contr_t P) ∘ fmap[F] f).
      - refine (compose_respects _ _ _ _ _ _).
        + symmetry.
          apply fmap_comp.
        + reflexivity.
      - symmetry.
        apply fmap_comp. }
    transitivity (fmap[F] (g ∘ contr_t P ∘ g)).
    { apply fmap_respects.
      exact (contr_cofork P). }
    transitivity (fmap[F] (g ∘ contr_t P) ∘ fmap[F] g).
    { apply fmap_comp. }
    refine (compose_respects _ _ _ _ _ _).
    + apply fmap_comp.
    + reflexivity.
Defined.

Example functor_preserves_contractible_t@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D)
  {x y : C} {f g : x ~> y} (P : ContractiblePair f g) :
  contr_t (functor_preserves_contractible F f g P) = fmap[F] (contr_t P)
  := eq_refl.
