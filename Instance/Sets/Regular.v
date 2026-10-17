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

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition sets_coarsen : bool_setoid_object ~{Sets}~> sets_coarse := {|
  morphism := fun b : bool => b
|}.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition BlanketSplitting : Type :=
  ∀ (A B : SetoidObject) (a0 : carrier A) (f : A ~{Sets}~> B),
    Epic f → Retraction f.

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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

(*
   本节说明 Regular 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
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
