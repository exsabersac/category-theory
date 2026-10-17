(*
   本文件给出阿贝尔群相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*  SCOPE.  Issue #256 also asks for [Ab] as a [Preadditive] instance and for a
    forgetful [Ab ⟶ Grp] alongside [Ab ⟶ Sets].  NEITHER is delivered here.
    [Structure/Preadditive.v]'s instance has since landed as
    Structure/AbCategory.v's [Ab_Preadditive] (with the Ab-enrichment
    [Ab_AbEnriched]);
    [Ab ⟶ Grp] had no target when this file
    was written; the category of groups has since landed
    (Instance/Grp.v) and the inclusion is
    Instance/Grp/Abelianization.v's [Ab_to_Grp].  Only [Ab_Forget :
    Ab ⟶ Sets] is provided here.  *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** ** Objects *)

(** An abelian group: a commutative monoid with a negation that is a
    left inverse.  The right inverse law follows by commutativity
    ([ab_neg_right] below), so it is not a field. *)
Record AbObject := {
  ab_cmon :> CMonObject;

  ab_neg : carrier (cmon_setoid ab_cmon) → carrier (cmon_setoid ab_cmon);
  ab_neg_respects : Proper (equiv ==> equiv) ab_neg;

  ab_neg_left : ∀ a, cmon_plus ab_cmon (ab_neg a) a ≈ cmon_zero ab_cmon
}.

#[export] Existing Instance ab_neg_respects.

Corollary ab_neg_right (A : AbObject) (a : carrier (cmon_setoid A)) :
  cmon_plus A a (ab_neg A a) ≈ cmon_zero A.
Proof.
  rewrite cmon_plus_comm.
  apply ab_neg_left.
Qed.

(** Cancellation, used repeatedly below.  This is the one property that
    genuinely separates a group from a monoid. *)
Lemma ab_cancel_l (A : AbObject) (a b c : carrier (cmon_setoid A)) :
  cmon_plus A a b ≈ cmon_plus A a c → b ≈ c.
Proof.
  intro H.
  rewrite <- (cmon_plus_zero_l A b), <- (cmon_plus_zero_l A c).
  rewrite <- (ab_neg_left A a).
  rewrite !cmon_plus_assoc.
  now rewrite H.
Qed.

(** Negation is determined: anything acting as a left inverse IS the
    negation.  Needed to show homomorphisms preserve it. *)
Lemma ab_neg_unique (A : AbObject) (a b : carrier (cmon_setoid A)) :
  cmon_plus A b a ≈ cmon_zero A → b ≈ ab_neg A a.
Proof.
  intro H.
  apply (ab_cancel_l A a).
  rewrite (cmon_plus_comm A a b), H.
  now symmetry; apply ab_neg_right.
Qed.

Lemma ab_neg_zero (A : AbObject) : ab_neg A (cmon_zero A) ≈ cmon_zero A.
Proof.
  symmetry; apply ab_neg_unique.
  apply cmon_plus_zero_l.
Qed.

(** Negation distributes over addition.  This needs commutativity, so it is an
    abelian-group fact rather than a group fact, and it is what makes the
    quotient below respect negation. *)
Lemma ab_neg_plus (A : AbObject) (a b : carrier (cmon_setoid A)) :
  ab_neg A (cmon_plus A a b)
    ≈ cmon_plus A (ab_neg A a) (ab_neg A b).
Proof.
  symmetry; apply ab_neg_unique.
  rewrite cmon_plus_assoc.
  rewrite <- (cmon_plus_assoc A (ab_neg A b) a b).
  rewrite (cmon_plus_comm A (ab_neg A b) a).
  rewrite (cmon_plus_assoc A a (ab_neg A b) b).
  rewrite ab_neg_left, cmon_plus_zero_r.
  apply ab_neg_left.
Qed.

(** ** Morphisms *)

(** A homomorphism of abelian groups is exactly a homomorphism of the
    underlying commutative monoids.  Preservation of negation is derived, not
    demanded -- the standard fact that a monoid map between groups is a group
    map. *)
Definition AbHom (A B : AbObject) := CMonHom A B.

Lemma ab_map_neg {A B : AbObject} (f : AbHom A B) (a : carrier (cmon_setoid A)) :
  cmon_map f (ab_neg A a) ≈ ab_neg B (cmon_map f a).
Proof.
  apply ab_neg_unique.
  rewrite <- cmon_map_plus.
  rewrite ab_neg_left.
  apply cmon_map_zero.
Qed.

(** ** The category *)

(** [Ab] is the full subcategory of [CMon] on the objects carrying a negation:
    same homs, same identities, same composition, same hom-setoid.  Stating it
    this way is what makes [ab_map_neg] a theorem rather than a coherence
    obligation. *)
(** The universes are pinned by hand, for the reason recorded at
    Instance/CMon.v's [CMon]: once [cmon_prop] is a field the record's sort
    carries a [Set+1] and the elaborator stops identifying the record's own
    sort variable with the category's object universe, which would give [Ab] a
    third, redundant universe and refuse every `Ab@{u o}` annotation in the
    tree for arity.  Measured after the change,
    [Ab@{u p} : Category@{u p p}] with the single new constraint [Set < u]. *)
Program Definition Ab@{u p} : Category@{u p p} := {|
  obj     := AbObject@{p p p};
  hom     := AbHom@{p};
  homset  := fun A B => @CMonHom_Setoid@{p} A B;
  id      := fun A => @cmon_hom_id@{p} A;
  compose := fun A B C f g => @cmon_hom_compose@{u p} A B C f g;

  (* [compose_respects] is inherited from [CMon] literally.  The remaining four
     laws are NOT: they are [Program] obligations, discharged afresh by the
     file-global [Obligation Tactic] (Lib/Tactics.v's [cat_simpl]).  What is
     true is that no new mathematical content is needed -- [Ab]'s homs,
     identities and composition ARE [CMon]'s -- not that nothing is reproved. *)
  compose_respects := fun A B C => @cmon_hom_compose_respects@{u p} A B C
|}.

(** The forgetful functor to [Sets], through the underlying setoid. *)
Program Definition Ab_Forget : Ab ⟶ Sets := {|
  fobj := fun A => cmon_setoid (ab_cmon A);
  fmap := fun _ _ f => cmon_map f
|}.

(** ** The zero group as a zero object *)

(** The one-element abelian group.  Its negation is forced: there is only one
    element, so [ab_neg] is the constant map and the inverse law is
    [reflexivity]. *)
Definition Ab_trivial : AbObject.
Proof.
  unshelve notypeclasses refine {|
    ab_cmon := CMon_trivial;
    ab_neg  := fun _ => ttt
  |}.
  - intros x y Hxy; reflexivity.
  - intros a; reflexivity.
Defined.

(** Everything maps to the point, and only one map does. *)
Definition Ab_one (A : AbObject) : A ~{Ab}~> Ab_trivial := CMon_one A.

Lemma Ab_one_unique (A : AbObject) (f : A ~{Ab}~> Ab_trivial) :
  f ≈ Ab_one A.
Proof. intro a; destruct (cmon_map f a); reflexivity. Qed.

Program Definition Ab_Terminal : @Terminal Ab := {|
  terminal_obj := Ab_trivial;
  one          := Ab_one
|}.
Next Obligation. now rewrite (Ab_one_unique _ f), (Ab_one_unique _ g). Qed.

(** Dually: the unique map OUT of the point sends the point to zero.  This is
    where the group being trivial does the work -- there is nothing to choose. *)
Definition Ab_zero_hom (A : AbObject) : Ab_trivial ~{Ab}~> A :=
  CMon_zero_hom A.

Lemma Ab_zero_hom_unique (A : AbObject) (f : Ab_trivial ~{Ab}~> A) :
  f ≈ Ab_zero_hom A.
Proof.
  intro a; destruct a; simpl.
  now rewrite (cmon_map_zero f).
Qed.

Program Definition Ab_Initial : @Initial Ab := {|
  terminal_obj := Ab_trivial : obj[Ab^op];
  one          := Ab_zero_hom
|}.
Next Obligation.
  (* Routed through transitivity at the hom-setoid level rather than by
     [rewrite]: rewriting puts both sides under [cmon_map], where it leaves
     undetermined evars. *)
  etransitivity;
    [ apply Ab_zero_hom_unique | symmetry; apply Ab_zero_hom_unique ].
Qed.

(** The same object is both, so the coincidence iso is the identity -- exactly
    as at Instance/CMon/Biproduct.v. *)
#[export] Instance Ab_Zero : ZeroObject Ab :=
  @Build_ZeroObject Ab Ab_Terminal Ab_Initial iso_id.

(** ** Mac Lane's §I.7 proposition: monic = injective, epic = surjective *)

Definition AbInjective {A B : AbObject} (f : A ~{Ab}~> B) : Type :=
  ∀ x y : carrier (cmon_setoid A), cmon_map f x ≈ cmon_map f y → x ≈ y.

Definition AbSurjective {A B : AbObject} (f : A ~{Ab}~> B) : Type :=
  ∀ b : carrier (cmon_setoid B), { a & cmon_map f a ≈ b }.

(** The PROPOSITIONAL surjectivity of the same map: a preimage exists, but is
    not handed back as data.  [AbSurjective] above is the SPLIT notion, whose
    witness IS a section of [f] up to `≈`; this one is the image-theoretic
    notion of ordinary mathematics.  The split notion implies this one
    ([ab_surjective_prop] below) and the converse needs choice, so the two are
    kept apart on purpose: constructions that build a preimage directly keep
    proving [AbSurjective], while [ab_epic_surjective] -- which reads its
    witness out of a quotient, and so out of a [Prop] -- concludes this one. *)
Definition AbPropSurjective {A B : AbObject} (f : A ~{Ab}~> B) : Type :=
  ∀ b : carrier (cmon_setoid B),
    (exists a : carrier (cmon_setoid A),
       @pequiv _ _ (cmon_prop B) (cmon_map f a) b)%type.

Lemma ab_surjective_prop {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → AbPropSurjective f.
Proof.
  intros Hs b.
  destruct (Hs b) as [a Ha].
  exists a.
  now apply pequiv_from.
Qed.

(** *** The kernel, used as the probe object for the monic half *)

(** A probe object is genuinely needed: monic does not imply injective in an
    arbitrary category.  The kernel is the cheapest one available here --
    unlike the usual textbook probe it needs neither the free abelian group on
    one generator nor any scalar action, only a sub-setoid. *)

Section Kernel.

Context {A B : AbObject}.
Context (f : A ~{Ab}~> B).

Definition ab_ker_carrier : Type :=
  { a : carrier (cmon_setoid A) & cmon_map f a ≈ cmon_zero B }.

Program Definition ab_ker_setoid : Setoid ab_ker_carrier := {|
  equiv := fun p q => projT1 p ≈ projT1 q
|}.

Lemma ab_ker_zero_pf : cmon_map f (cmon_zero A) ≈ cmon_zero B.
Proof. apply cmon_map_zero. Qed.

Lemma ab_ker_plus_pf (p q : ab_ker_carrier) :
  cmon_map f (cmon_plus A (projT1 p) (projT1 q)) ≈ cmon_zero B.
Proof.
  rewrite cmon_map_plus, (projT2 p), (projT2 q).
  apply cmon_plus_zero_l.
Qed.

Lemma ab_ker_neg_pf (p : ab_ker_carrier) :
  cmon_map f (ab_neg A (projT1 p)) ≈ cmon_zero B.
Proof.
  rewrite ab_map_neg, (projT2 p).
  apply ab_neg_zero.
Qed.

Definition AbKernel : AbObject.
Proof using A B f.
  unshelve notypeclasses refine {|
    ab_cmon :=
      {| cmon_setoid := {| carrier := ab_ker_carrier ; is_setoid := ab_ker_setoid |}
       ; cmon_zero := existT _ (cmon_zero A) ab_ker_zero_pf
       ; cmon_plus := fun p q =>
           existT _ (cmon_plus A (projT1 p) (projT1 q)) (ab_ker_plus_pf p q)
       ; cmon_prop :=
           sigma_first_PropEquiv ab_ker_setoid
             (fun _ _ h => h) (fun _ _ h => h) (cmon_prop A) |};
    ab_neg := fun p => existT _ (ab_neg A (projT1 p)) (ab_ker_neg_pf p)
  |}.
  - (* cmon_plus_respects *)
    intros p p' Hp q q' Hq; simpl in *.
    now rewrite Hp, Hq.
  - (* cmon_plus_assoc *)
    intros a b c; simpl; apply cmon_plus_assoc.
  - (* cmon_plus_comm *)
    intros a b; simpl; apply cmon_plus_comm.
  - (* cmon_plus_zero_l *)
    intros a; simpl; apply cmon_plus_zero_l.
  - (* ab_neg_respects *)
    intros p q Hpq; simpl in *; now rewrite Hpq.
  - (* ab_neg_left *)
    intros a; simpl; apply ab_neg_left.
Defined.

(** The inclusion of the kernel, and the zero map alongside it.  [f] equalizes
    them, which is the whole point. *)
Program Definition ab_kernel_incl : AbKernel ~{Ab}~> A :=
  {| cmon_map := {| morphism := fun p : ab_ker_carrier => projT1 p |} |}.

Program Definition ab_kernel_zero : AbKernel ~{Ab}~> A :=
  {| cmon_map := {| morphism := fun _ : ab_ker_carrier => cmon_zero A |} |}.
Next Obligation. symmetry; apply cmon_plus_zero_l. Qed.

End Kernel.

Arguments AbKernel {A B} f.
Arguments ab_kernel_incl {A B} f.
Arguments ab_kernel_zero {A B} f.

(** *** Monic *)

(** Monic implies injective, by probing with the kernel: [f] equalizes the
    inclusion and the zero map, so monic collapses them, so every kernel
    element is zero -- and then [f x ≈ f y] puts [x - y] in the kernel.

    NOTE what this does and does not show.  [x - y] is where THIS proof spends
    the group structure, but the THEOREM does not need it: monic implies
    injective already in [CMon], probing with the free commutative monoid on
    one generator ([nat]) instead of a kernel.  So the kernel is a convenient
    probe here, not a necessary one, and the monic half is NOT a place where
    [Ab] does something [CMon] cannot. *)
Lemma ab_monic_injective {A B : AbObject} (f : A ~{Ab}~> B) :
  Monic f → AbInjective f.
Proof.
  intros Hm x y Hxy.
  (* Step 1: monic collapses the two maps out of the kernel. *)
  assert (Hk : ∀ p : carrier (cmon_setoid (AbKernel f)),
                 projT1 p ≈ cmon_zero A).
  { apply (@monic _ _ _ f Hm (AbKernel f)
             (ab_kernel_incl f) (ab_kernel_zero f)).
    intro p; simpl.
    rewrite (projT2 p).
    symmetry; apply cmon_map_zero. }
  (* Step 2: x - y lies in the kernel. *)
  assert (Hd : cmon_map f (cmon_plus A x (ab_neg A y)) ≈ cmon_zero B).
  { rewrite cmon_map_plus, ab_map_neg, Hxy.
    apply ab_neg_right. }
  (* Step 3: so x - y is zero, hence x ≈ y. *)
  pose proof (Hk (existT _ (cmon_plus A x (ab_neg A y)) Hd)) as Hz.
  simpl in Hz.
  apply (ab_cancel_l A (ab_neg A y)).
  rewrite (cmon_plus_comm A (ab_neg A y) x) in *.
  rewrite Hz.
  now rewrite (cmon_plus_comm A (ab_neg A y) y), ab_neg_right.
Qed.

Lemma ab_injective_monic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbInjective f → Monic f.
Proof.
  intros Hi.
  constructor; intros Z g h Hgh z.
  apply Hi.
  exact (Hgh z).
Qed.

Theorem ab_monic_iff_injective {A B : AbObject} (f : A ~{Ab}~> B) :
  Monic f ↔ AbInjective f.
Proof.
  split; [ apply ab_monic_injective | apply ab_injective_monic ].
Qed.

(** *** The quotient B/fA, used as the probe object for the epic half *)

(** Mac Lane's construction.  The carrier is [B] itself; only the equality
    coarsens, to "differ by something in the image of [f]".

    THE RELATION IS [Prop]-VALUED.  An earlier revision of this paragraph said
    the opposite -- "Note the relation is TYPE-valued -- [{ a & ... }], not
    [∃] -- which is what lets the witness be read back out at the end without
    any choice principle" -- and that is no longer so.  Since the PR "algebraic
    carriers are sets" (2026-09-17) every [AbObject] carries [cmon_prop], the
    property that its `≈` is logically equivalent to a [Prop]-valued relation,
    and a quotient's equality has to be a [Prop] too or the field could not be
    supplied.  So [ab_coset_eq] is Coq's [ex], spelled [(exists a, …)%type]
    because this library's bare [∃] and [exists] are [sigT]
    (Lib/Foundation.v).  The consequence is stated where it bites:
    [ab_epic_surjective] below concludes PROPOSITIONAL surjectivity, and the
    split form [AbSurjective] is no longer derivable from an epi.  Its body
    compares through [pequiv] rather than `≈` for the same reason -- the body
    of an [ex] must itself be a [Prop]. *)

Section Quotient.

Context {A B : AbObject}.
Context (f : A ~{Ab}~> B).

Definition ab_coset_eq (x y : carrier (cmon_setoid B)) : Prop :=
  (exists a : carrier (cmon_setoid A),
     @pequiv _ _ (cmon_prop B) x (cmon_plus B y (cmon_map f a)))%type.

Lemma ab_coset_refl (x : carrier (cmon_setoid B)) : ab_coset_eq x x.
Proof.
  exists (cmon_zero A).
  apply pequiv_from.
  rewrite cmon_map_zero.
  symmetry; apply cmon_plus_zero_r.
Qed.

(** SYMMETRY IS WHERE THE INVERSES ARE SPENT.  From [x ≈ y + f a] one recovers
    [y ≈ x + f (-a)] only because [f (-a)] inverts [f a].  This single step is
    the formal reason the construction works in [Ab] and has no analogue one
    level down in [CMon]. *)
Lemma ab_coset_sym (x y : carrier (cmon_setoid B)) :
  ab_coset_eq x y → ab_coset_eq y x.
Proof.
  intros [a Ha].
  apply pequiv_to in Ha.
  exists (ab_neg A a).
  apply pequiv_from.
  rewrite ab_map_neg, Ha.
  rewrite cmon_plus_assoc.
  rewrite ab_neg_right.
  symmetry; apply cmon_plus_zero_r.
Qed.

Lemma ab_coset_trans (x y z : carrier (cmon_setoid B)) :
  ab_coset_eq x y → ab_coset_eq y z → ab_coset_eq x z.
Proof.
  intros [a Ha] [b Hb].
  apply pequiv_to in Ha.
  apply pequiv_to in Hb.
  exists (cmon_plus A b a).
  apply pequiv_from.
  rewrite cmon_map_plus.
  rewrite Ha, Hb.
  now rewrite cmon_plus_assoc.
Qed.

Program Definition ab_coset_setoid : Setoid (carrier (cmon_setoid B)) := {|
  equiv := ab_coset_eq
|}.
Next Obligation.
  constructor.
  - exact ab_coset_refl.
  - exact ab_coset_sym.
  - exact ab_coset_trans.
Qed.

Definition AbQuotient : AbObject.
Proof using A B f.
  unshelve notypeclasses refine {|
    ab_cmon :=
      {| cmon_setoid := {| carrier := carrier (cmon_setoid B)
                         ; is_setoid := ab_coset_setoid |}
       ; cmon_zero := cmon_zero B
       ; cmon_plus := cmon_plus B
       ; cmon_prop :=
           @PropEquiv_of_relation _ ab_coset_setoid ab_coset_eq
             (fun _ _ h => h) (fun _ _ h => h) |};
    ab_neg := ab_neg B
  |}.
  - (* cmon_plus_respects.  [simpl] first: the goal is an application of the
       [equiv] projection, whose ASCRIBED sort is [Type] ([equiv] lives in
       [crelation]), and a [Prop] hypothesis may not be destructed into a
       [Type] goal.  Reducing the projection exposes [ab_coset_eq], which is a
       [Prop], and the elimination is then allowed.  Every obligation below
       needs the same step. *)
    intros x x' Hx y y' Hy; simpl in Hx, Hy |- *.
    destruct Hx as [a Ha], Hy as [b Hb].
    apply pequiv_to in Ha.
    apply pequiv_to in Hb.
    exists (cmon_plus A a b).
    apply pequiv_from.
    rewrite cmon_map_plus, Ha, Hb.
    (* (x' + f a) + (y' + f b) ≈ (x' + y') + (f a + f b) *)
    rewrite !cmon_plus_assoc.
    apply cmon_plus_respects; [ reflexivity | ].
    rewrite <- !cmon_plus_assoc.
    apply cmon_plus_respects; [ | reflexivity ].
    apply cmon_plus_comm.
  - (* cmon_plus_assoc *)
    intros x y z; simpl; exists (cmon_zero A).
    apply pequiv_from.
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply cmon_plus_assoc.
  - (* cmon_plus_comm *)
    intros x y; simpl; exists (cmon_zero A).
    apply pequiv_from.
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply cmon_plus_comm.
  - (* cmon_plus_zero_l *)
    intros x; simpl; exists (cmon_zero A).
    apply pequiv_from.
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply cmon_plus_zero_l.
  - (* ab_neg_respects *)
    intros x y Hxy; simpl in Hxy |- *.
    destruct Hxy as [a Ha].
    apply pequiv_to in Ha.
    exists (ab_neg A a).
    apply pequiv_from.
    rewrite ab_map_neg.
    change (ab_neg B x ≈ cmon_plus B (ab_neg B y) (ab_neg B (cmon_map f a))).
    rewrite <- ab_neg_plus.
    now rewrite Ha.
  - (* ab_neg_left *)
    intros x; simpl; exists (cmon_zero A).
    apply pequiv_from.
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply ab_neg_left.
Defined.

(** The projection (identity on carriers, coarser equality) and the zero map.
    [f] equalizes them -- which is exactly the statement that [f a] is
    congruent to zero modulo the image. *)
Program Definition ab_quot_proj : B ~{Ab}~> AbQuotient :=
  {| cmon_map := {| morphism := fun b : carrier (cmon_setoid B) => b |} |}.
Next Obligation. intros x y Hxy; simpl; exists (cmon_zero A); apply pequiv_from;
  rewrite cmon_map_zero, cmon_plus_zero_r; exact Hxy. Qed.
Next Obligation. apply ab_coset_refl. Qed.
Next Obligation. apply ab_coset_refl. Qed.

Program Definition ab_quot_zero : B ~{Ab}~> AbQuotient :=
  {| cmon_map :=
       {| morphism := fun _ : carrier (cmon_setoid B) => cmon_zero B |} |}.
Next Obligation. intros x y Hxy; apply ab_coset_refl. Qed.
Next Obligation. apply ab_coset_refl. Qed.
Next Obligation.
  simpl.
  exists (cmon_zero A).
  apply pequiv_from.
  rewrite cmon_map_zero, cmon_plus_zero_r.
  symmetry; apply cmon_plus_zero_l.
Qed.

End Quotient.

Arguments AbQuotient {A B} f.
Arguments ab_quot_proj {A B} f.
Arguments ab_quot_zero {A B} f.

(** *** Epic *)

(** Epic implies PROPOSITIONAL surjectivity, constructively and with no
    double-negation.

    [f] equalizes the projection and the zero map into [B/fA], so an epi
    collapses them -- and [ab_quot_proj ≈ ab_quot_zero] says precisely that
    every [b] is congruent to zero modulo the image, which is to say that a
    preimage EXISTS.

    AN EARLIER REVISION concluded the split [AbSurjective] and said the witness
    "IS the preimage -- read straight back out, with nothing chosen and nothing
    doubly negated".  Since the PR "algebraic carriers are sets" (2026-09-17)
    the coset relation is a [Prop] (see [ab_coset_eq] above), so the witness may
    not be read back out into a [Type]-valued goal and the conclusion is
    [AbPropSurjective].  Nothing is doubly negated and nothing is chosen -- the
    existential is Coq's [ex], not a double negation -- but the preimage is no
    longer data.  Test/ProbeAbPropSurjective.v pins the refusal, with the
    surviving direction ([ab_surjective_prop]) as its positive control.  The
    old reading was an artefact of proof-relevant quotients: in Set, epi implies
    surjective, while surjective implies SPLIT only by choice. *)
Lemma ab_epic_surjective {A B : AbObject} (f : A ~{Ab}~> B) :
  Epic f → AbPropSurjective f.
Proof.
  intros He b.
  assert (Hpq : ab_quot_proj f ≈ ab_quot_zero f).
  { apply (@epic _ _ _ f He (AbQuotient f)
             (ab_quot_proj f) (ab_quot_zero f)).
    intro a; simpl.
    exists a.
    apply pequiv_from.
    rewrite cmon_plus_zero_l.
    reflexivity. }
  specialize (Hpq b); simpl in Hpq.
  destruct Hpq as [a Ha].
  apply pequiv_to in Ha.
  exists a.
  apply pequiv_from.
  rewrite cmon_plus_zero_l in Ha.
  now symmetry.
Qed.

Lemma ab_surjective_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → Epic f.
Proof.
  intros Hs.
  constructor; intros Z g h Hgh b.
  destruct (Hs b) as [a Ha].
  rewrite <- Ha.
  exact (Hgh a).
Qed.

(** The same implication from the propositional notion.  The target's equation
    is [Type]-valued, so the [Prop] existential may not be destructed into it
    directly; [pequiv_to] puts a [Prop] goal in front of the elimination and
    converts back afterwards.  This is the pattern every consumer of a
    truncated relation follows. *)
Lemma ab_prop_surjective_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbPropSurjective f → Epic f.
Proof.
  intros Hs.
  constructor; intros Z g h Hgh b.
  apply (@pequiv_to _ _ (cmon_prop Z)).
  destruct (Hs b) as [a Ha].
  apply pequiv_from.
  apply pequiv_to in Ha.
  rewrite <- Ha.
  exact (Hgh a).
Qed.

(** Mac Lane §I.7's proposition, second half.  An earlier revision stated it
    with [AbSurjective] on the right; see [ab_epic_surjective] for why the
    right-hand side is now the propositional notion.  The split notion still
    implies [Epic] ([ab_surjective_epic] above), so no direction is lost -- only
    the shape of the witness the forward direction produces. *)
Theorem ab_epic_iff_surjective {A B : AbObject} (f : A ~{Ab}~> B) :
  Epic f ↔ AbPropSurjective f.
Proof.
  split; [ apply ab_epic_surjective | apply ab_prop_surjective_epic ].
Qed.

(** ** The hom-setoids are propositional *)

(** L8: [Ab]'s hom-setoid IS [CMonHom_Setoid] (see [Ab] above), so
    Instance/CMon.v's [CMonHom_PropEquiv] supplies the whole family at once.
    This is what lets a construction that turns an object of an ambient
    category into an abelian group -- [hom_ab] of Adjunction/Additive.v,
    [ehom_ab] of Construction/Enriched/Ab.v -- be instantiated at [Ab] itself
    without a hand-written hypothesis. *)
#[export] Instance Ab_LocallyPropositional : LocallyPropositional Ab.
Proof.
  constructor.
  intros A B.
  exact (@CMonHom_PropEquiv A B).
Defined.
