Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Regular arrows in Sets: the blanket principle decides every proposition *)

(*
 nLab:      https://ncatlab.org/nlab/show/split+epimorphism
 Wikipedia: https://en.wikipedia.org/wiki/Diaconescu%27s_theorem
 Wikipedia: https://en.wikipedia.org/wiki/Axiom_of_choice

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(** ** The countermodel: bool coarsened by a proposition *)

Section Coarsening.

Context (P : Prop).

(* Two booleans count as equal when they are equal, or when P holds.  The
   relation is [Type]-valued, as every hom-setoid relation in this library is
   ([crelation], Lib/Setoid.v), so a proof of it can be taken apart by
   [destruct] into the informative case distinction the theorems below run
   on. *)
Definition sets_coarse_equiv (b b' : bool) : Type := ((b = b') + P)%type.

Program Definition sets_coarse_setoid : Setoid bool := {|
  equiv := sets_coarse_equiv
|}.
Next Obligation.
  constructor; repeat intro.
  - left; reflexivity.
  - destruct X; [ left; now symmetry | now right ].
  - destruct X; destruct X0; try (now right).
    left; now transitivity y.
Qed.

Definition sets_coarse : SetoidObject :=
  {| carrier := bool ; is_setoid := sets_coarse_setoid |}.

(* The identity on carriers, read as an arrow into the coarser setoid.  It
   respects the equivalences because it only ever has to make things MORE
   equal.  Its domain is [bool_setoid_object] (Instance/Sets.v), which is
   inhabited by [true], so the blanket principle applies to it. *)
Program Definition sets_coarsen : bool_setoid_object ~{Sets}~> sets_coarse := {|
  morphism := fun b : bool => b
|}.

(* The reverse hom-set is inhabited: a constant map respects any pair of
   equivalences.  This is what keeps the theorems below from being about an
   empty hom-set, which is how the tree's other non-regularity results
   work. *)
Program Definition sets_coarse_const :
  sets_coarse ~{Sets}~> bool_setoid_object := {|
  morphism := fun _ : bool => true
|}.

(* When P is refuted, the identity on carriers runs BACK as well: the
   coarsening added nothing. *)
Program Definition sets_coarse_sharpen (np : P → False) :
  sets_coarse ~{Sets}~> bool_setoid_object := {|
  morphism := fun b : bool => b
|}.
Next Obligation.
  repeat intro.
  destruct X as [E | p]; [ exact E | now contradiction np ].
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Regularity of this one arrow is decidability of P *)

(* Forwards.  A pseudoinverse g satisfies (g b = b) + P at each of the two
   booleans.  If it answers on the left at both then g true = true and
   g false = false, while P would force g true = g false through g's own
   respectfulness; so P is refuted.  If it answers on the right anywhere, P
   is handed over directly. *)
Lemma sets_coarsen_regular_dec :
  RegularMorphism sets_coarsen → (P + (P → False))%type.
Proof.
  intros [g Hg].
  destruct (Hg true)  as [Et | p]; [| exact (inl p) ].
  destruct (Hg false) as [Ef | p]; [| exact (inl p) ].
  right; intro p.
  assert (Hgg : g true = g false)
    by (apply (proper_morphism g); right; exact p).
  simpl in Et, Ef.
  rewrite Et, Ef in Hgg.
  discriminate.
Qed.

(* Backwards, by cases on the decision.  If P holds, everything in the
   codomain is equivalent to everything else and any arrow back will do; if P
   is refuted, the coarsening is invisible and the identity on carriers is a
   two-sided inverse. *)
Definition sets_coarsen_regular_of_dec :
  (P + (P → False))%type → RegularMorphism sets_coarsen.
Proof.
  intros [p | np].
  - exists sets_coarse_const.
    intro b; simpl; unfold sets_coarse_equiv.
    now right.
  - exists (sets_coarse_sharpen np).
    intro b; simpl; unfold sets_coarse_equiv.
    now left.
Defined.

(* So the two are equivalent, and the regularity of a single named arrow of
   [Sets] is neither more nor less than the decidability of an arbitrary
   proposition. *)
Definition sets_coarsen_regular_iff_dec :
  RegularMorphism sets_coarsen ↔ (P + (P → False))%type :=
  (sets_coarsen_regular_dec, sets_coarsen_regular_of_dec).

(* It is epic outright: the identity on carriers is right-cancellable because
   two arrows out of the coarse setoid that agree after it already agree
   pointwise. *)
Lemma sets_coarsen_epic : Epic sets_coarsen.
Proof. constructor; intros Z g1 g2 H b; exact (H b). Qed.

(* Hence a splitting of it would decide P too, through
   [regular_of_retraction]: a right inverse is in particular a
   pseudoinverse. *)
Lemma sets_coarsen_retraction_dec :
  Retraction sets_coarsen → (P + (P → False))%type.
Proof.
  intro R.
  exact (sets_coarsen_regular_dec (regular_of_retraction _ R)).
Qed.

(* And non-regularity is not merely unproven but refutable: if regularity led
   to a contradiction then P would be refuted, P alone being enough to build a
   pseudoinverse, and a refutation of P builds one as well.  This is the
   precise sense in which an arrow of [Sets] with inhabited domain cannot be
   shown non-regular. *)
Lemma sets_coarsen_not_regular_absurd :
  (RegularMorphism sets_coarsen → False) → False.
Proof.
  intro H.
  apply H, sets_coarsen_regular_of_dec.
  right; intro p.
  exact (H (sets_coarsen_regular_of_dec (inl p))).
Qed.

End Coarsening.

(* ------------------------------------------------------------------------ *)
(** ** The two blanket principles, and what each entails *)

(* The statement Mac Lane's exercise makes about Set, transcribed for [Sets]:
   every arrow whose domain is inhabited -- inhabitation taken as DATA, an
   actual element, which is what "nonempty" means constructively -- is
   regular. *)
Definition BlanketRegularity : Type :=
  ∀ (A B : SetoidObject) (a0 : carrier A) (f : A ~{Sets}~> B),
    RegularMorphism f.

(* The internal axiom of choice in the same restricted form: every
   epimorphism whose domain is inhabited splits.  The nLab page on split
   epimorphisms records that the axiom of choice internal to a category may
   be phrased as "all epimorphisms are split" and that "In Set this is
   equivalent to the usual axiom of choice" (retrieved 2026-08). *)
Definition BlanketSplitting : Type :=
  ∀ (A B : SetoidObject) (a0 : carrier A) (f : A ~{Sets}~> B),
    Epic f → Retraction f.

(* The implication between them, as a statement of Coq rather than as prose:
   [regular_epic_retraction] applied under both quantifiers.  This is the
   step Instance/FinSet/Regular.v's header describes, and it is one line. *)
Definition blanket_regularity_entails_splitting :
  BlanketRegularity → BlanketSplitting :=
  fun HR A B a0 f E => regular_epic_retraction f (HR A B a0 f) E.

(* The internal choice principle decides every proposition, by the
   countermodel: [sets_coarsen] is epic with inhabited domain, so the
   principle splits it, and a splitting is a pseudoinverse. *)
Theorem blanket_splitting_entails_LEM :
  BlanketSplitting → ∀ P : Prop, (P + (P → False))%type.
Proof.
  intros HS P.
  exact (sets_coarsen_retraction_dec P
           (HS bool_setoid_object (sets_coarse P) true
              (sets_coarsen P) (sets_coarsen_epic P))).
Qed.

(* And so does the regularity principle, which implies the splitting one.
   Proved twice over: directly from the countermodel, and -- as
   [blanket_regularity_entails_splitting] composed with
   [blanket_splitting_entails_LEM] -- through the splitting principle, which
   is the route the FinSet header describes in prose. *)
Theorem blanket_regularity_entails_LEM :
  BlanketRegularity → ∀ P : Prop, (P + (P → False))%type.
Proof.
  intros HR P.
  exact (sets_coarsen_regular_dec P
           (HR bool_setoid_object (sets_coarse P) true (sets_coarsen P))).
Qed.

Definition blanket_regularity_entails_LEM_via_splitting :
  BlanketRegularity → ∀ P : Prop, (P + (P → False))%type :=
  fun HR => blanket_splitting_entails_LEM
              (blanket_regularity_entails_splitting HR).
