Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.

Generalizable All Variables.

(** * Concrete categories *)

(* nLab:      https://ncatlab.org/nlab/show/concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Concrete_category

   具体范畴 (concrete category) 是配备到 [Sets]（或类似基础范畴）的忠实函子
   [underlying] 的范畴 [C]：箭头由底层函数忠实表示。Mac Lane 与 nLab 强调「具体」
   是相对选定遗忘函子的结构，而非内在性质。本文件打包 [Concrete] 类（范畴 + 忠实
   遗忘）、底层函数提取，以及与忠实性相关的基本引理。长历史短文若仍为英文属后续波次；
   此处定义性文首已译。 *)

Section Concrete.

(* A concrete category: a category `C` paired with a chosen faithful functor
   to `Sets`.  Mac Lane §I.7's `⟨C, U⟩`; Riehl §1.6, Definition 1.6.18. *)
Class Concrete (C : Category) := {
  underlying : C ⟶ Sets;             (* the chosen underlying-set functor U *)
  underlying_faithful : Faithful underlying   (* arrows ARE actual functions *)
}.

#[export] Existing Instance underlying_faithful.

Context {C : Category}.
Context `{Con : @Concrete C}.

(* The actual function carried by an arrow: the object part of [underlying]
   supplies the underlying set of each object, and [concrete_fun f] is `f`
   read as a setoid map between those sets.  (`SetoidMorphism` coerces to its
   carrier function, so `concrete_fun f a` is literally an application.) *)
Definition concrete_fun {x y : C} (f : x ~> y) :
  underlying x ~{Sets}~> underlying y := fmap[underlying] f.

(* An arrow determines its function.  This half is just functoriality
   ([fmap_respects]); it is recorded so the two halves sit together. *)
Lemma concrete_fun_respects {x y : C} (f g : x ~> y) :
  f ≈ g → ∀ a : carrier (underlying x), concrete_fun f a ≈ concrete_fun g a.
Proof.
  intros Hfg a.
  exact (fmap_respects (Functor:=underlying) x y f g Hfg a).
Qed.

(* The function determines the arrow: "arrows ARE actual functions", as the
   definitional unfolding of [underlying_faithful] at the level of elements.
   Note that the conclusion is `≈` in `C`'s hom-setoid and the hypothesis is
   `≈` in the codomain setoid — no `=` occurs on either side. *)
Lemma concrete_arrow_eq {x y : C} (f g : x ~> y) :
  (∀ a : carrier (underlying x), concrete_fun f a ≈ concrete_fun g a) → f ≈ g.
Proof.
  intros Hfg.
  apply (fmap_inj (F:=underlying)).
  exact Hfg.
Qed.

(* The two halves packaged as the biconditional Riehl states: parallel arrows
   are equal exactly when the functions they carry agree pointwise. *)
Corollary concrete_arrow_iff {x y : C} (f g : x ~> y) :
  f ≈ g ↔ (∀ a : carrier (underlying x), concrete_fun f a ≈ concrete_fun g a).
Proof.
  split.
  - apply concrete_fun_respects.
  - apply concrete_arrow_eq.
Qed.

End Concrete.

Arguments concrete_fun {C Con x y} f.

(** ** Awodey's refinement: separators and well-pointedness *)

Section Separator.

Context {C : Category}.

(* nLab: https://ncatlab.org/nlab/show/separator

   A separator (generator) is a test object `t` whose generalized elements
   `e : t ~> x` jointly detect equality of arrows out of `x`.  Awodey §1.5,
   Remark 1.7 introduces exactly this condition, as the repair of the naive
   notion of concreteness.  Compare Adjunction/SAFT.v's `Cogenerator`,
   which is the dual notion (arrows INTO a test object) packaged there for
   the special adjoint functor theorem. *)
Class Separator (t : C) := {
  separates {x y : C} (f g : x ~> y) :
    (∀ e : t ~> x, f ∘ e ≈ g ∘ e) → f ≈ g   (* generalized elements detect ≈ *)
}.

(* A separator concretizes: `Hom(t, −)` is faithful precisely when `t`
   separates, since `fmap[Hom(t,−)] f ≈ fmap[Hom(t,−)] g` unfolds to
   `∀ e : t ~> x, f ∘ e ≈ g ∘ e`.  This is the exact sense in which Awodey's
   refinement implies (his version of) concreteness. *)
Program Definition Concrete_of_Separator (t : C) `{@Separator t} :
  Concrete C := {|
  underlying := fobj[Curried_Hom C] t
|}.
Next Obligation.
  constructor; simpl; intros x y f g Hfg.
  apply (separates (t:=t)).
  intro e.
  exact (Hfg e).
Qed.

(* The converse reading: whenever `Hom(t, −)` is faithful, `t` separates.  So
   [Separator t] and faithfulness of the representable are interderivable, and
   neither direction is an extra assumption. *)
Definition Separator_of_Faithful (t : C)
  (H : Faithful (fobj[Curried_Hom C] t)) : Separator t.
Proof.
  constructor; intros x y f g Hfg.
  apply (fmap_inj (F:=fobj[Curried_Hom C] t)).
  simpl; intro e.
  exact (Hfg e).
Qed.

End Separator.

Arguments separates {C} t {Separator x y} f g _.

(* Awodey's own case: the test object is terminal, so generalized elements are
   GLOBAL elements `1 ~> x` — the points of `x`.  A category in which the
   terminal object separates is well-pointed.

   This is a property of a CATEGORY equipped with a terminal object.  It has
   nothing to do with the [WellPointed] class of Instance/Fun.v, which is
   a coherence condition on a pointed endofunctor; the names are kept apart
   deliberately. *)
Definition WellPointedCategory (C : Category) `{T : @Terminal C} : Type :=
  Separator (@terminal_obj C T).

(* A well-pointed category is concrete, via its global-elements functor
   `Hom(1, −)`.  This is Awodey's refined notion of concreteness. *)
Definition Concrete_of_WellPointed {C : Category} `{T : @Terminal C}
  (W : WellPointedCategory C) : Concrete C :=
  @Concrete_of_Separator C (@terminal_obj C T) W.

(** ** The category of setoids is concrete, and well-pointed *)

(* `Sets` is concrete by way of its identity functor: an object IS its
   underlying set and an arrow IS its function.  Faithfulness is then the
   identity implication.  This instance is the degenerate one, and it is NOT
   vacuous: `Sets` has parallel arrows that differ, as [Sets_two_arrows]
   below witnesses. *)
#[export] Program Instance Sets_Concrete@{o so+} : Concrete Sets@{o so} := {|
  underlying := Id[Sets@{o so}]
|}.
Next Obligation.
  constructor; simpl; intros x y f g Hfg.
  exact Hfg.
Qed.

(* The two-element setoid, used below to show the `Sets` instance has
   content. *)
Definition bool_setoid_object@{t u+} : SetoidObject@{t u} :=
  {| carrier   := bool
   ; is_setoid := {| equiv := @eq bool ; setoid_equiv := eq_equivalence |} |}.

(* Non-vacuity of [Sets_Concrete]: faithfulness is not free, because the
   hom-setoid it is injective on is not trivial.  The identity and negation
   maps on the two-element setoid are parallel arrows that are DISTINCT in
   the hom-setoid `bool_setoid_object ~{Sets}~> bool_setoid_object`, whose
   `≈` is pointwise equality of the underlying functions. *)
Program Definition Sets_negb@{o so+} :
  bool_setoid_object@{o o} ~{Sets@{o so}}~> bool_setoid_object@{o o} :=
  {| morphism := negb |}.

(* Stated with an explicit `→ False` rather than `¬`: hom-equivalence in this
   library is a `crelation`, i.e. `Type`-valued, and `¬` is `Prop`-valued. *)
Lemma Sets_two_arrows@{o so+} :
  @id Sets@{o so} bool_setoid_object@{o o} ≈ Sets_negb@{o so} → False.
Proof.
  intro Heq.
  (* `≈` in this hom-setoid is pointwise `=` on `bool`; instantiate at
     `true`. *)
  specialize (Heq true).
  simpl in Heq.
  discriminate.
Qed.

(* The point of a setoid `x` at an element `a`: the constant map out of the
   singleton terminal object.  This is the same probe Instance/Sets.v uses to
   characterize monos as injections. *)
Program Definition Sets_point@{o so+} {x : Sets@{o so}} (a : carrier x) :
  @terminal_obj Sets Sets_Terminal ~{Sets}~> x := {| morphism := fun _ => a |}.

(* `Sets` is well-pointed: a point of `x` is a map out of the singleton
   setoid, and the constant map at `a` is such a point picking out `a`.  So
   global elements detect equality of setoid maps. *)
#[export] Instance Sets_Separator@{o so+} :
  @Separator Sets@{o so} (@terminal_obj Sets@{o so} Sets_Terminal@{so o}).
Proof.
  constructor.
  intros x y f g Hfg a.
  exact (Hfg (Sets_point a) ttt).
Qed.

Definition Sets_WellPointed@{o so+} : WellPointedCategory Sets@{o so} :=
  Sets_Separator@{o so}.

(* [Separator] is a genuine condition on an object, not one every object
   satisfies: the EMPTY setoid is not a separator of `Sets`, because there is
   nothing to probe with — every hypothesis of the separator condition holds
   vacuously, so it would identify the two distinct arrows of
   [Sets_two_arrows].  Recording this keeps the class from being read as
   content-free. *)
Definition empty_setoid_object@{t u+} : SetoidObject@{t u} :=
  {| carrier := False ; is_setoid := False_Setoid@{u} |}.

Lemma Sets_empty_not_Separator@{o so+} :
  @Separator Sets@{o so} empty_setoid_object@{o o} → False.
Proof.
  intro Hsep.
  destruct Hsep as [sep].
  apply Sets_two_arrows@{o so}.
  apply sep.
  intros e a.
  destruct a.
Qed.

(* The global-elements concretization of `Sets` obtained from
   well-pointedness.  It is a SECOND concrete structure on the same category:
   its underlying-set functor is `Hom(1, −)` where [Sets_Concrete]'s is the
   identity.  The two are different data — which is why Mac Lane's definition
   pairs the functor with the category — and no claim is made here about how
   the two functors compare up to natural isomorphism. *)
Definition Sets_Concrete_Points@{o so+} : Concrete Sets@{o so} :=
  Concrete_of_WellPointed Sets_WellPointed@{o so}.
