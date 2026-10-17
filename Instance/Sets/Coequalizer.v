Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Coequalizer.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * Coequalizers in [Sets] *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Coequaliser

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明等价、（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The generated relation *)

Section CoeqRel.

Context {A B : SetoidObject}.
Context (f g : A ~{Sets}~> B).

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive coeq_rel : carrier B -> carrier B -> Type :=
  | cq_base  : forall b1 b2 : carrier B, b1 ≈ b2 -> coeq_rel b1 b2
  | cq_glue  : forall a : carrier A, coeq_rel (f a) (g a)
  | cq_sym   : forall b1 b2 : carrier B, coeq_rel b1 b2 -> coeq_rel b2 b1
  | cq_trans : forall b1 b2 b3 : carrier B,
      coeq_rel b1 b2 -> coeq_rel b2 b3 -> coeq_rel b1 b3.

Lemma coeq_rel_refl (b : carrier B) : coeq_rel b b.
Proof. apply cq_base; reflexivity. Qed.

Lemma coeq_rel_Equivalence : Equivalence coeq_rel.
Proof.
  constructor.
  - exact coeq_rel_refl.
  - intros b1 b2 H; exact (cq_sym b1 b2 H).
  - intros b1 b2 b3 H1 H2; exact (cq_trans b1 b2 b3 H1 H2).
Qed.

Definition coeq_rel_coarser : SetoidCoarser coeq_rel := cq_base.

End CoeqRel.

Arguments coeq_rel {A B} f g _ _.
Arguments coeq_rel_refl {A B} f g b.
Arguments coeq_rel_Equivalence {A B} f g.
Arguments coeq_rel_coarser {A B} f g.

(** ** Leastness: respecting the closure IS coforking *)

Section Leastness.

Context {A B : SetoidObject}.
Context (f g : A ~{Sets}~> B).
Context {X : SetoidObject}.

(*
   本节说明 Coequalizer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma coeq_rel_of_cofork (h : B ~{Sets}~> X) (Hh : h ∘ f ≈ h ∘ g) :
  SetsRespects (coeq_rel f g) X h.
Proof.
  intros b1 b2 Hb.
  induction Hb as
    [ b1 b2 Hb | a | b1 b2 Hb IH | b1 b2 b3 Hb1 IH1 Hb2 IH2 ].
  - now apply proper_morphism.
  - exact (Hh a).
  - now symmetry.
  - now transitivity (h b2).
Qed.

(* ... and back, by the [cq_glue] constructor alone. *)
Lemma cofork_of_coeq_rel (h : B ~{Sets}~> X)
  (Hh : SetsRespects (coeq_rel f g) X h) : h ∘ f ≈ h ∘ g.
Proof. intro a; exact (Hh (f a) (g a) (cq_glue f g a)). Qed.

Theorem coeq_rel_respects (h : B ~{Sets}~> X) :
  SetsRespects (coeq_rel f g) X h ↔ h ∘ f ≈ h ∘ g.
Proof.
  split.
  - exact (cofork_of_coeq_rel h).
  - exact (coeq_rel_of_cofork h).
Qed.

End Leastness.

(** ** The coequalizer object *)

Section SetsCoeq.

Context {A B : SetoidObject}.
Context (f g : A ~{Sets}~> B).

Definition SetsCoeq : SetoidObject :=
  SetsQuotient B (coeq_rel f g) (coeq_rel_Equivalence f g).

Definition sets_coeq_proj : B ~{Sets}~> SetsCoeq :=
  sets_quot_proj B (coeq_rel f g) (coeq_rel_Equivalence f g)
    (coeq_rel_coarser f g).

(* The carrier is B's, and the coequalizing map is the identity function
   -- both by conversion, the [eq_refl] exception. *)
Example sets_coeq_carrier : carrier SetsCoeq = carrier B.
Proof. reflexivity. Qed.

Example sets_coeq_proj_at (b : carrier B) : sets_coeq_proj b = b.
Proof. reflexivity. Qed.

(* Awodey §3.4's construction and Seven Sketches §6.2.4's example, as the
   elementary universal property of Structure/Coequalizer.v. *)
Definition sets_coeq_IsCoequalizer :
  IsCoequalizer f g SetsCoeq sets_coeq_proj.
Proof.
  unshelve refine {| cofork := _ |}.
  - (* the projection coforks: this is [cq_glue] read pointwise *)
    intro a; exact (cq_glue f g a).
  - intros X h Hh.
    unshelve refine
      {| unique_obj :=
           sets_quot_med (coeq_rel f g) (coeq_rel_Equivalence f g)
             (existT (SetsRespects (coeq_rel f g) X) h
                (coeq_rel_of_cofork f g h Hh)) |}.
    + intro b; simpl; reflexivity.
    + intros v Hv b; simpl; symmetry; exact (Hv b).
Defined.

End SetsCoeq.

Arguments SetsCoeq {A B} f g.
Arguments sets_coeq_proj {A B} f g.

(* THE INSTANCE.  [∃] is [sigT], so the coequalizer is a CHOSEN one,
   supplied as data; no choice principle is consumed. *)
#[export] Instance Sets_HasCoequalizers : HasCoequalizers Sets := {|
  coeq := fun x y f g =>
    existT (fun q : Sets => { e : y ~{Sets}~> q & IsCoequalizer f g q e })
      (SetsCoeq f g)
      (existT (fun e : y ~{Sets}~> SetsCoeq f g =>
                 IsCoequalizer f g (SetsCoeq f g) e)
         (sets_coeq_proj f g) (sets_coeq_IsCoequalizer f g))
|}.

(* The chosen object and map are the ones built above, by conversion. *)
Example sets_hascoeq_obj {A B : SetoidObject} (f g : A ~{Sets}~> B) :
  `1 (@coeq Sets Sets_HasCoequalizers A B f g) = SetsCoeq f g.
Proof. reflexivity. Qed.

Example sets_hascoeq_map {A B : SetoidObject} (f g : A ~{Sets}~> B) :
  `1 (`2 (@coeq Sets Sets_HasCoequalizers A B f g)) = sets_coeq_proj f g.
Proof. reflexivity. Qed.

(** ** Mac Lane §III.3 exercise 5: X/E is the coequalizer of E ⇉ X *)

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section RelObject.

Context {X : SetoidObject}.
Context (R : crelation (carrier X)).

Definition sets_rel_carrier : Type :=
  { x : carrier X & { y : carrier X & R x y } }.

Definition sets_rel_equiv : crelation sets_rel_carrier :=
  fun s t => (`1 s ≈ `1 t) ∧ (`1 (`2 s) ≈ `1 (`2 t)).

Lemma sets_rel_equivalence : Equivalence sets_rel_equiv.
Proof.
  unfold sets_rel_equiv; constructor.
  - intro s; split; reflexivity.
  - intros s t [H1 H2]; split; now symmetry.
  - intros s t u [H1 H2] [H3 H4]; split;
      [ now transitivity (`1 t) | now transitivity (`1 (`2 t)) ].
Qed.

Definition SetsRelObj : SetoidObject :=
  {| carrier := sets_rel_carrier ;
     is_setoid := {| equiv := sets_rel_equiv ;
                     setoid_equiv := sets_rel_equivalence |} |}.

Definition sets_rel_fst : SetsRelObj ~{Sets}~> X.
Proof.
  unshelve refine {| morphism := fun s : sets_rel_carrier => `1 s |}.
  intros s t Hst; exact (fst Hst).
Defined.

Definition sets_rel_snd : SetsRelObj ~{Sets}~> X.
Proof.
  unshelve refine {| morphism := fun s : sets_rel_carrier => `1 (`2 s) |}.
  intros s t Hst; exact (snd Hst).
Defined.

(* The pair ⟨x, y, w⟩ is where the two projections separate, and it is
   what makes the cofork condition say exactly "h respects R". *)
Definition sets_rel_pt {x y : carrier X} (w : R x y) : carrier SetsRelObj :=
  existT (fun x' : carrier X => { y' : carrier X & R x' y' }) x
    (existT (fun y' : carrier X => R x y') y w).

Example sets_rel_fst_at {x y : carrier X} (w : R x y) :
  sets_rel_fst (sets_rel_pt w) = x.
Proof. reflexivity. Qed.

Example sets_rel_snd_at {x y : carrier X} (w : R x y) :
  sets_rel_snd (sets_rel_pt w) = y.
Proof. reflexivity. Qed.

(* Coforking the projection pair IS respecting R.  Unlike
   [coeq_rel_respects] this needs no induction at all: one direction
   evaluates at [sets_rel_pt], the other reads a triple apart. *)
Lemma sets_rel_cofork_iff {Z : SetoidObject} (h : X ~{Sets}~> Z) :
  (h ∘ sets_rel_fst ≈ h ∘ sets_rel_snd) ↔ SetsRespects R Z h.
Proof.
  split.
  - intros Hh x y w; exact (Hh (sets_rel_pt w)).
  - intros Hh s; exact (Hh (`1 s) (`1 (`2 s)) (`2 (`2 s))).
Qed.

(* Mac Lane §III.3 exercise 5 / Awodey §3.4 example 3.19.  Note that the
   coequalizer object here is the quotient ON THE NOSE, not merely
   isomorphic to it. *)
Definition sets_rel_IsCoequalizer (HR : Equivalence R) (HC : SetoidCoarser R) :
  IsCoequalizer sets_rel_fst sets_rel_snd (SetsQuotient X R HR)
    (sets_quot_proj X R HR HC).
Proof.
  unshelve refine {| cofork := _ |}.
  - intro s; exact (`2 (`2 s)).
  - intros Z h Hh.
    unshelve refine
      {| unique_obj :=
           sets_quot_med R HR
             (existT (SetsRespects R Z) h
                (fst (sets_rel_cofork_iff h) Hh)) |}.
    + intro x; simpl; reflexivity.
    + intros v Hv x; simpl; symmetry; exact (Hv x).
Defined.

End RelObject.

Arguments SetsRelObj {X} R.
Arguments sets_rel_fst {X} R.
Arguments sets_rel_snd {X} R.
Arguments sets_rel_pt {X R x y} w.

(** ** The two readings agree *)

Section Comparison.

Context {X : SetoidObject}.
Context (R : crelation (carrier X)).
Context (HR : Equivalence R).
(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sets_rel_coeq_rel_iff (HR' : Equivalence R) (HC' : SetoidCoarser R)
  (x y : carrier X) :
  coeq_rel (sets_rel_fst R) (sets_rel_snd R) x y ↔ R x y.
Proof.
  split.
  - intro H.
    induction H as
      [ b1 b2 Hb | s | b1 b2 Hb IH | b1 b2 b3 Hb1 IH1 Hb2 IH2 ].
    + exact (HC' b1 b2 Hb).
    + exact (`2 (`2 s)).
    + now symmetry.
    + now transitivity b2.
  - intro H; exact (cq_glue (sets_rel_fst R) (sets_rel_snd R) (sets_rel_pt H)).
Qed.

(*
   本节说明 Coequalizer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_rel_coeq_iso (HC' : SetoidCoarser R) :
  @Isomorphism Sets (SetsCoeq (sets_rel_fst R) (sets_rel_snd R))
    (SetsQuotient X R HR).
Proof.
  unshelve refine {| to := _ ; from := _ |}.
  - unshelve refine {| morphism := fun x : carrier X => x |}.
    intros a b Hab; exact (fst (sets_rel_coeq_rel_iff HR HC' a b) Hab).
  - unshelve refine {| morphism := fun x : carrier X => x |}.
    intros a b Hab; exact (snd (sets_rel_coeq_rel_iff HR HC' a b) Hab).
  - intro x; exact (@Equivalence_Reflexive _ R HR x).
  - intro x; exact (coeq_rel_refl (sets_rel_fst R) (sets_rel_snd R) x).
Defined.

(* Both legs are the identity function, by conversion. *)
Example sets_rel_coeq_iso_to (HC : SetoidCoarser R) (x : carrier X) :
  to (sets_rel_coeq_iso HC) x = x.
Proof. reflexivity. Qed.

Example sets_rel_coeq_iso_from (HC : SetoidCoarser R) (x : carrier X) :
  from (sets_rel_coeq_iso HC) x = x.
Proof. reflexivity. Qed.

End Comparison.

(** ** Non-vacuity *)

(* A coequalizer that MERGES.  The two constant maps out of the singleton
   into the two-element discrete setoid identify [false] with [true], so
   the coequalizer collapses [bool]. *)

Definition UnitSet : SetoidObject :=
  {| carrier := poly_unit ; is_setoid := unit_setoid |}.

(* [BoolSet] is Instance/Sets/Quotient.v's, reused rather than
   redeclared: the two files' witnesses then live over the same object. *)

Definition bool_false_map : UnitSet ~{Sets}~> BoolSet.
Proof. unshelve refine {| morphism := fun _ : poly_unit => false |}. Defined.

Definition bool_true_map : UnitSet ~{Sets}~> BoolSet.
Proof. unshelve refine {| morphism := fun _ : poly_unit => true |}. Defined.

Definition bool_flip_coeq : SetoidObject :=
  SetsCoeq bool_false_map bool_true_map.

Lemma bool_flip_merges : @equiv _ bool_flip_coeq false true.
Proof. exact (cq_glue bool_false_map bool_true_map ttt). Qed.

(*
   本节说明 Coequalizer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma coeq_rel_diagonal {A B : SetoidObject} (f : A ~{Sets}~> B)
  (b1 b2 : carrier B) : coeq_rel f f b1 b2 → b1 ≈ b2.
Proof.
  intro H.
  induction H as
    [ b1 b2 Hb | a | b1 b2 Hb IH | b1 b2 b3 Hb1 IH1 Hb2 IH2 ].
  - exact Hb.
  - reflexivity.
  - now symmetry.
  - now transitivity b2.
Qed.

Lemma bool_id_coeq_separates :
  @equiv _ (SetsCoeq bool_false_map bool_false_map) false true → False.
Proof.
  intro H.
  pose proof (coeq_rel_diagonal bool_false_map false true H) as E.
  discriminate E.
Qed.

(*
   本节说明 Coequalizer 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma bool_legs_distinct : bool_false_map ≈ bool_true_map → False.
Proof. intro H; pose proof (H ttt) as E; discriminate E. Qed.
