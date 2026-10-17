Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Thin.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Props.

Generalizable All Variables.

(** * The Lindenbaum category of an elementary theory *)

(*
 nLab:      https://ncatlab.org/nlab/show/Lindenbaum-Tarski+algebra
 nLab:      https://ncatlab.org/nlab/show/Heyting+algebra
 nLab:      https://ncatlab.org/nlab/show/deduction+theorem
 Wikipedia: https://en.wikipedia.org/wiki/Lindenbaum%E2%80%93Tarski_algebra
 Wikipedia: https://en.wikipedia.org/wiki/Deduction_theorem
 Book:      Lambek and Scott, "Introduction to Higher Order Categorical

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** (A) Syntax *)

(* Atoms, truth, conjunction, implication.  Nothing else; see the scope
   note in the header. *)
Inductive Sent (V : Type) : Type :=
  | s_var : V -> Sent
  | s_top : Sent
  | s_and : Sent -> Sent -> Sent
  | s_imp : Sent -> Sent -> Sent.

Arguments s_var {V} _.
Arguments s_top {V}.
Arguments s_and {V} _ _.
Arguments s_imp {V} _ _.

(* A theory is a bare set of sentences: its axioms.  It is not required
   to be deductively closed, consistent, or inhabited. *)
Definition Theo (V : Type) : Type := Sent V -> Prop.

(** ** (B) Entailment relative to a theory *)

(* Mac Lane's "q is a consequence of p on the basis of the axioms of T".
   Prop-valued, so [Proset] accepts it and the category below is thin
   without any truncation. *)
Inductive Entails {V : Type} (T : Theo V) : Sent V -> Sent V -> Prop :=
  (* assumption / reflexivity *)
  | ent_refl p : Entails p p
  (* cut / transitivity *)
  | ent_cut p q r : Entails p q -> Entails q r -> Entails p r
  (* the axiom rule: an axiom of T follows from anything *)
  | ent_ax p a : T a -> Entails p a
  (* ⊤-introduction *)
  | ent_top p : Entails p s_top
  (* ∧-introduction *)
  | ent_pair p q r : Entails p q -> Entails p r -> Entails p (s_and q r)
  (* the two ∧-eliminations *)
  | ent_fst p q : Entails (s_and p q) p
  | ent_snd p q : Entails (s_and p q) q
  (* →-introduction: the deduction theorem, here a CONSTRUCTOR *)
  | ent_curry p q r : Entails (s_and p q) r -> Entails p (s_imp q r)
  (* evaluation / modus ponens in sequent form *)
  | ent_eval q r : Entails (s_and (s_imp q r) q) r.

(*
   本节说明 Lindenbaum 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition entails_PreOrder {V} (T : Theo V) :
  RelationClasses.PreOrder (Entails T) :=
  {| RelationClasses.PreOrder_Reflexive := ent_refl T
   ; RelationClasses.PreOrder_Transitive :=
       fun p q r H K => ent_cut T p q r H K |}.

(** ** (C) The category of sentences ordered by entailment *)

Definition Lind {V} (T : Theo V) : Category :=
  Proset (entails_PreOrder T).

Example lind_obj {V} (T : Theo V) : obj[Lind T] = Sent V := eq_refl.

Example lind_hom {V} (T : Theo V) (p q : Sent V) :
  (p ~{Lind T}~> q) = Entails T p q := eq_refl.

Example lind_id {V} (T : Theo V) (p : Sent V) :
  @id (Lind T) p = ent_refl T p := eq_refl.

Example lind_compose {V} (T : Theo V) (p q r : Sent V)
  (f : Entails T p q) (g : Entails T q r) :
  (g ∘[Lind T] f) = ent_cut T p q r f g := eq_refl.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition lind_thin {V} (T : Theo V) : Thin (Lind T) :=
  fun _ _ _ _ => I.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition lind_any_Faithful {V} (T : Theo V) {D : Category}
  (F : Lind T ⟶ D) : Faithful F :=
  @Build_Faithful (Lind T) D F (fun x y f g _ => I).

(** ** (D) Terminal, cartesian and closed *)

(* Terminal object: truth.  [one] is ⊤-introduction; [one_unique] is
   free by thinness. *)
#[export] Program Instance Lind_Terminal {V} (T : Theo V) :
  @Terminal (Lind T) := {
  terminal_obj := s_top;
  one := fun p => ent_top T p
}.

(* Product: conjunction, exactly as the exercise says.  [fork] is
   ∧-introduction, the projections are the two ∧-eliminations;
   [fork_respects] and [ump_products] are free by thinness. *)
#[export] Program Instance Lind_Cartesian {V} (T : Theo V) :
  @Cartesian (Lind T) := {
  product_obj := s_and;
  fork := fun p q r f g => ent_pair T p q r f g;
  exl  := fun p q => ent_fst T p q;
  exr  := fun p q => ent_snd T p q
}.

(*
   本节说明 Lindenbaum 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition lind_uncurry {V} {T : Theo V} {p q r : Sent V}
  (f : Entails T p (s_imp q r)) : Entails T (s_and p q) r :=
  ent_cut T (s_and p q) (s_and (s_imp q r) q) r
    (ent_pair T (s_and p q) (s_imp q r) q
       (ent_cut T (s_and p q) p (s_imp q r) (ent_fst T p q) f)
       (ent_snd T p q))
    (ent_eval T q r).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Program Instance Lind_Closed {V} (T : Theo V) :
  @Closed (Lind T) _ := {
  exponent_obj := s_imp;
  exp_iso := fun p q r =>
    {| to   := {| morphism := fun f => ent_curry T p q r f |}
     ; from := {| morphism := fun f => lind_uncurry f |} |}
}.

(* The exercise's three identifications, pinned so that a later edit
   cannot drift away from them. *)
Example lind_terminal_is_top {V} (T : Theo V) :
  @terminal_obj (Lind T) (Lind_Terminal T) = s_top := eq_refl.

Example lind_product_is_and {V} (T : Theo V) (p q : Sent V) :
  @product_obj (Lind T) (Lind_Cartesian T) p q = s_and p q := eq_refl.

Example lind_exponent_is_imp {V} (T : Theo V) (p q : Sent V) :
  @exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q
    = s_imp p q := eq_refl.

(* Currying IS the deduction rule, on the nose. *)
Example lind_curry_is_rule {V} (T : Theo V) (p q r : Sent V)
  (f : Entails T (s_and p q) r) :
  @curry (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q r f
    = ent_curry T p q r f := eq_refl.

(* ...and the counit is [lind_uncurry] at the identity derivation. *)
Example lind_eval_unfold {V} (T : Theo V) (q r : Sent V) :
  @eval (Lind T) (Lind_Cartesian T) (Lind_Closed T) q r
    = lind_uncurry (ent_refl T (s_imp q r)) := eq_refl.

(** ** (E) Soundness under a valuation *)

(* The interpretation of a sentence under a valuation of the atoms.
   Conjunction goes to /\ and implication to ->, which is what makes
   section (F)'s three preservation statements hold at eq_refl. *)
Fixpoint sdenote {V} (val : V -> Prop) (p : Sent V) : Prop :=
  match p with
  | s_var v   => val v
  | s_top     => True
  | s_and a b => sdenote val a /\ sdenote val b
  | s_imp a b => sdenote val a -> sdenote val b
  end.

(*
   本节说明 Lindenbaum 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem ent_soundness {V} (T : Theo V) (val : V -> Prop)
  (HT : forall a, T a -> sdenote val a) {p q : Sent V} :
  Entails T p q -> sdenote val p -> sdenote val q.
Proof.
  intros D; induction D; simpl in *; try tauto.
  - intros _; exact (HT a H).
Qed.

(** ** (F) The comparison functor into Instance/Props.v *)

(* The soundness map packaged as a functor.  All three functor laws are
   free: Props is thin, so every equation between its arrows is True. *)
Program Definition LindSound {V} (T : Theo V) (val : V -> Prop)
  (HT : forall a, T a -> sdenote val a) : Lind T ⟶ Props := {|
  fobj := sdenote val;
  fmap := fun p q f => ent_soundness T val HT f
|}.

(* Preservation of the three pieces of cartesian closed structure, at
   Leibniz equality of objects rather than up to isomorphism. *)
Example sound_terminal {V} (T : Theo V) val HT :
  fobj[LindSound T val HT] (@terminal_obj (Lind T) (Lind_Terminal T))
    = @terminal_obj Props Props_Terminal := eq_refl.

Example sound_product {V} (T : Theo V) val HT (p q : Sent V) :
  fobj[LindSound T val HT]
      (@product_obj (Lind T) (Lind_Cartesian T) p q)
    = @product_obj Props Props_Cartesian
        (fobj[LindSound T val HT] p) (fobj[LindSound T val HT] q)
  := eq_refl.

Example sound_exponent {V} (T : Theo V) val HT (p q : Sent V) :
  fobj[LindSound T val HT]
      (@exponent_obj (Lind T) (Lind_Cartesian T) (Lind_Closed T) p q)
    = @exponent_obj Props Props_Cartesian Props_Closed
        (fobj[LindSound T val HT] p) (fobj[LindSound T val HT] q)
  := eq_refl.

(* Faithful, but VACUOUSLY so: this IS [lind_any_Faithful], so nothing
   about soundness is consulted and the vacuity is not a claim about the
   proof but the definition itself. *)
#[export] Instance LindSound_Faithful {V} (T : Theo V) val HT :
  Faithful (LindSound T val HT) :=
  lind_any_Faithful T (LindSound T val HT).

(** ** (G) Two axiom sets, two categories *)

(*
   本节说明 Lindenbaum 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma entails_weaken {V} {T T' : Theo V} (HTT : forall a, T a -> T' a)
  {p q : Sent V} : Entails T p q -> Entails T' p q.
Proof.
  intros D; induction D;
    [ apply ent_refl
    | eapply ent_cut; eassumption
    | apply ent_ax; apply HTT; assumption
    | apply ent_top
    | apply ent_pair; assumption
    | apply ent_fst
    | apply ent_snd
    | apply ent_curry; assumption
    | apply ent_eval ].
Defined.

(* ...as an identity-on-objects functor between the two categories. *)
Program Definition LindWeaken {V} {T T' : Theo V}
  (HTT : forall a, T a -> T' a) : Lind T ⟶ Lind T' := {|
  fobj := fun p => p;
  fmap := fun p q f => entails_weaken HTT f
|}.

(* Two atoms, and three theories over them: no axioms, the single
   implication between the atoms, and every sentence an axiom. *)
Definition sv (b : bool) : Sent bool := s_var b.

Definition T_empty : Theo bool := fun _ => False.
Definition T_mp : Theo bool := fun s => s = s_imp (sv true) (sv false).
Definition T_all : Theo bool := fun _ => True.

(* The separating valuation: the first atom true, the second not. *)
Definition val_sep (b : bool) : Prop := b = true.

Lemma val_sep_empty : forall a, T_empty a -> sdenote val_sep a.
Proof. intros a []. Qed.

(* Non-derivability at the empty theory, by soundness at [val_sep].
   This is the half that cannot be got by exhibiting a derivation. *)
Theorem not_entails_empty :
  Entails T_empty (sv true) (sv false) -> False.
Proof.
  intros D.
  pose proof (@ent_soundness bool T_empty val_sep val_sep_empty _ _ D
                eq_refl) as Hf.
  discriminate Hf.
Qed.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem entails_mp : Entails T_mp (sv true) (sv false).
Proof.
  apply (ent_cut _ _ (s_and (sv true) (sv true))).
  - apply ent_pair; apply ent_refl.
  - apply (@lind_uncurry bool T_mp).
    apply ent_ax; reflexivity.
Defined.

Definition empty_sub_mp : forall a, T_empty a -> T_mp a :=
  fun a H => match H return T_mp a with end.

(* The comparison functor between the two categories is identity on
   objects, and it is NOT full: [entails_mp] has no preimage. *)
Theorem weaken_not_Full : Full (LindWeaken empty_sub_mp) -> False.
Proof.
  intros [pre _].
  exact (not_entails_empty (pre (sv true) (sv false) entails_mp)).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition empty_sub_all : forall a, T_empty a -> T_all a :=
  fun a H => match H return T_all a with end.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem no_full_functor_empty_to_all (F : Lind T_empty ⟶ Lind T_all) :
  Full F -> False.
Proof.
  intros [pre _].
  exact (not_entails_empty
           (pre (sv true) (sv false)
              (ent_ax T_all (fobj[F] (sv true)) (fobj[F] (sv false)) I))).
Qed.

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem no_equivalence_empty_to_all (F : Lind T_empty ⟶ Lind T_all) :
  EquivalenceOfCategories F -> False.
Proof.
  intros E.
  exact (no_full_functor_empty_to_all F (Equivalence_Full E)).
Qed.

(** ** (H) The comparison with Props is not an equivalence *)

(* The valuation under which every atom, hence every sentence, holds. *)
Definition val_true (b : bool) : Prop := True.

Lemma val_true_empty : forall a, T_empty a -> sdenote val_true a.
Proof. intros a []. Qed.

Lemma sdenote_all {V} (val : V -> Prop)
  (Hv : forall v, val v) (p : Sent V) : sdenote val p.
Proof.
  induction p; simpl;
    [ apply Hv | exact I | split; assumption | intros _; assumption ].
Qed.

(* Not full: fullness at this valuation would be completeness, and it
   would hand back the underivable entailment of [not_entails_empty]. *)
Theorem sound_not_Full :
  Full (LindSound T_empty val_true val_true_empty) -> False.
Proof.
  intros [pre _].
  exact (not_entails_empty (pre (sv true) (sv false) (fun x => x))).
Qed.

(* Every object in the image of this comparison is inhabited, so none of
   them is isomorphic to False in Props. *)
Theorem sound_misses_False (p : Sent bool) :
  @Isomorphism Props (sdenote val_true p) False -> False.
Proof.
  intros i.
  exact (to i (sdenote_all val_true (fun _ => I) p)).
Qed.

(* Not essentially surjective, by the previous result at False. *)
Theorem sound_not_EssentiallySurjective :
  EssentiallySurjective (LindSound T_empty val_true val_true_empty)
    -> False.
Proof.
  intros [pick iso].
  exact (sound_misses_False (pick False) (iso False)).
Qed.
