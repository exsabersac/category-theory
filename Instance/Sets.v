Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The category of setoids *)

(*
 nLab: https://ncatlab.org/nlab/show/setoid
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets
 Wikipedia: https://en.wikipedia.org/wiki/Setoid

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:   https://ncatlab.org/nlab/show/Bishop+set
   nLab:   https://ncatlab.org/nlab/show/E-category
   nLab:   https://ncatlab.org/nlab/show/predicative+topos
   Book:   Bishop, "Foundations of Constructive Analysis", McGraw-Hill 1967

   本节说明 Sets 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Record SetoidObject@{o p} : Type@{max(o+1,p+1)} := {
  carrier :> Type@{o};               (* the underlying type (Bishop carrier) *)
  is_setoid :> Setoid@{o p} carrier   (* its equivalence relation `≈` *)
}.
#[export] Existing Instance is_setoid.

(* A setoid map: a function on carriers together with a proof that it respects
   the two equivalences. This is the morphism part of [Sets]. *)
Record SetoidMorphism@{o h p} `{Setoid@{o p} x} `{Setoid@{o p} y} := {
  morphism :> x → y;                  (* the underlying function on carriers *)
  proper_morphism :>                  (* it sends `≈`-related inputs to `≈`-related outputs *)
    Proper@{h p} (respectful@{h p h p h p} equiv equiv) morphism
}.
#[export] Existing Instance proper_morphism.

Arguments SetoidMorphism {_} _ {_} _.
Arguments morphism {_ _ _ _ _} _.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SetoidMorphism_equiv@{o h p} {x y : SetoidObject@{o p}} :
  crelation@{h p} (SetoidMorphism@{o h p} x y) :=
  fun f g => ∀ x, @equiv@{o p} _ y (f x) (g x).

Arguments SetoidMorphism_equiv {x y} _ _ /.

#[export]
Program Instance SetoidMorphism_Setoid@{o h p} {x y : SetoidObject@{o p}} :
  Setoid@{h p} (SetoidMorphism@{o h p} x y) := {|
  equiv := SetoidMorphism_equiv@{o h p};
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - symmetry.
    apply X.
  - transitivity (y0 x1).
    + apply X.
    + apply X0.
Qed.

(*
   本节说明 Sets 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition setoid_morphism_id@{o h p} {x : SetoidObject@{o p}} :
  SetoidMorphism@{o h p} x x := {|
  morphism := Datatypes.id;
  proper_morphism := fun _ _ H => H
|}.

#[export] Hint Unfold setoid_morphism_id : core.

Definition setoid_morphism_compose@{o h p} {x y z : SetoidObject@{o p}}
        (g : SetoidMorphism@{o h p} y z)
        (f : SetoidMorphism@{o h p} x y) : SetoidMorphism@{o h p} x z := {|
  morphism := Basics.compose g f;
  proper_morphism := fun a b H =>
    proper_morphism g _ _ (proper_morphism f a b H)
|}.

#[export] Hint Unfold setoid_morphism_compose : core.

Program Definition setoid_morphism_compose_respects@{o h p}
  {x y z : SetoidObject@{o p}} :
  Proper@{h p} (equiv@{h p} ==> equiv@{h p} ==> equiv@{h p})
    (@setoid_morphism_compose x y z).
Proof.
  unfold Proper, respectful.
  simpl; intros.
  rewrite X.
  apply proper_morphism, X0.
Qed.

(* The category of setoids.

       objects: setoids
        arrows: setoid homomorphisms
      identity: typical identity of sets
   composition: composition of set maps, preserving equivalence
 *)
Program Definition Sets@{o so} : Category@{so o o} := {|
  obj     := SetoidObject@{o o} : Type@{so};
  hom     := λ x y, SetoidMorphism@{o o o} x y : Type@{o};
  homset  := @SetoidMorphism_Setoid@{o o o};
  id      := @setoid_morphism_id@{o o o};
  compose := @setoid_morphism_compose@{o o o};

  compose_respects := @setoid_morphism_compose_respects@{o o o}
|}.

Require Import Category.Theory.Isomorphism.

(*
   本节说明hom、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Notation "x ≊ y" := ({| carrier := x |} ≅[Sets] {| carrier := y |})
  (at level 99) : category_scope.

#[export]
Program Instance isomorphism_to_sets_respects
        `{Setoid x} `{Setoid y}
        (iso : @Isomorphism Sets {| carrier := x |} {| carrier := y |}) :
  Proper (equiv ==> equiv) (to iso).
Next Obligation.
  repeat intro.
  destruct iso; simpl in *.
  destruct to; simpl in *.
  rewrite X; reflexivity.
Qed.

#[export]
Program Instance isomorphism_from_sets_respects
        `{Setoid x} `{Setoid y}
        (iso : @Isomorphism Sets {| carrier := x |} {| carrier := y |}) :
  Proper (equiv ==> equiv) (from iso).
Next Obligation.
  repeat intro.
  destruct iso; simpl in *.
  destruct from; simpl in *.
  rewrite X; reflexivity.
Qed.

(* Build a [SetoidMorphism] by giving its underlying function and leaving the
   [proper_morphism] obligation as a fresh goal. *)
Ltac morphism :=
  unshelve (refine {| morphism := _ |}; simpl; intros).

Require Import Category.Structure.Terminal.

(* The singleton setoid: [poly_unit] under `=`, used as the terminal object. *)
#[export]
Program Instance Unit_Setoid@{u} : Setoid@{u u} poly_unit@{u} := {
  equiv := fun x y => x = y
}.

(* Terminal object: the singleton. There is exactly one map into it (every
   element maps to [ttt]), unique up to `≈`. *)
#[export]
Program Instance Sets_Terminal : @Terminal Sets := {
  terminal_obj := {| carrier := poly_unit |};
  one := fun _ => {| morphism := fun _ => ttt |};
  one_unique := fun x f g => _
}.
Next Obligation. destruct (f x0), (g x0); reflexivity. Qed.

Require Import Category.Structure.Initial.

(* The empty setoid: [False] as carrier; equivalence is vacuous. *)
#[export]
Program Instance False_Setoid@{u} : Setoid@{u u} False.
Next Obligation. proper. Qed.

(* Initial object: the empty setoid. The unique map out of it is the empty
   function (by [False] elimination). *)
#[export]
Program Instance Sets_Initial : @Initial Sets := {
  terminal_obj := {| carrier := False |};
  one := _
}.
Next Obligation.
  construct.
  - contradiction.
  - proper.
Qed.
Next Obligation. contradiction. Qed.

Require Import Category.Structure.Monoidal.

(*
   本节说明幺半结构、幺半群、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance Sets_Product_Monoidal : @Monoidal Sets := {
  I      := {| carrier := poly_unit |};
  tensor := {|
    fobj := fun p =>
      {| carrier := carrier (fst p) * carrier (snd p)
       ; is_setoid := _
       |};
    fmap := fun x y f =>
      {| morphism := fun p => (fst f (fst p), snd f (snd p))
       ; proper_morphism := _ |}
  |}
}.
Next Obligation.
  construct.
  - repeat intro.
    destruct s, s0.
    try rename X into H.
    try rename X0 into H0.
    exact (fst H ≈ fst H0 ∧ snd H ≈ snd H0).
  - simpl.
    equivalence.
Defined.
Next Obligation.
  proper; simpl in *.
  - destruct s.
    now rewrites.
  - destruct s0.
    now rewrites.
Qed.
Next Obligation.
  construct.
  - construct.
    + try rename X into H.
      now destruct H.
    + proper.
  - construct.
    + split; [ exact ttt | assumption ].
    + proper.
  - simpl.
    reflexivity.
  - simpl.
    destruct x0.
    simpl.
    destruct p.
    split; reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + try rename X into H.
      now destruct H.
    + proper.
  - construct.
    + split; [ assumption | exact ttt ].
    + proper.
  - simpl.
    reflexivity.
  - simpl.
    destruct x0.
    simpl.
    destruct p.
    split; reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + simplify; auto.
    + proper.
  - construct.
    + simplify; auto.
    + proper.
  - simpl.
    simplify; simpl; cat.
  - simpl.
    simplify; simpl; cat.
Defined.

(* The singleton as a [SetoidObject], packaging [unit_setoid] for use as a
   probe object below (a map out of it picks an element up to `≈`). *)
Definition unit_setoid_object@{t u} : SetoidObject@{t u} :=
  {| carrier   := poly_unit@{t}
   ; is_setoid := unit_setoid@{t u} |}.

(* In [Sets] the monomorphisms are exactly the injections (up to `≈`). The
   non-trivial direction probes [f] with two constant maps out of the singleton
   [unit_setoid_object]. *)
Lemma injectivity_is_monic {X Y : SetoidObject} (f : X ~{Sets}~> Y) :
  (∀ x y : X, f x ≈ f y → x ≈ y) ↔ Monic f.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    apply HA, HB.
  - intros HA ?? HB.
    given (const_x : unit_setoid_object ~{ Sets }~> X). {
      construct.
      - apply x.
      - proper.
    }
    given (const_y : unit_setoid_object ~{ Sets }~> X). {
      construct.
      - apply y.
      - proper.
    }
    destruct HA.
    specialize (monic unit_setoid_object const_x const_y).
    unfold const_x in monic.
    unfold const_y in monic.
    simpl in *.
    eapply monic; eauto.
    constructor.
Qed.

(* In [Sets] a bijection (injective and split-surjective up to `≈`) is an
   isomorphism: the chosen preimage assembles a two-sided inverse. *)
Lemma bijective_is_iso {A B : SetoidObject} (h : A ~{Sets}~> B) :
  injective h -> surjective h -> IsIsomorphism h.
Proof.
  intros [i] [lift] ; unshelve econstructor.
  - exists (fun b => `1 (lift b)).
    abstract(intros a b eq; simpl;
    apply i; now rewrite `2 (lift a), `2 (lift b)).
  - abstract(intro x; now rewrite `2 (lift x)).
  - abstract(intro x; apply i; now rewrite `2 (lift (h x))).
Defined.


(*
   本节说明 Sets 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CokernelPair.

Universes h p.
Context {A B : SetoidObject@{p p}}.
Context (f : A ~{Sets@{p h}}~> B).

(* Membership in the image of f, at the level of the carriers. *)
Definition Im (b : carrier B) : Type@{p} := ∃ a : carrier A, f a ≈ b.

Lemma Im_resp (x y : carrier B) : x ≈ y → Im x → Im y.
Proof. intros E [a Ha]; exists a; transitivity x; assumption. Qed.

(* Two copies of B, identified across the copies exactly on the image. *)
Definition ckrel (u v : (carrier B + carrier B)%type) : Type@{p} :=
  match u, v with
  | inl x, inl y => x ≈ y
  | inr x, inr y => x ≈ y
  | inl x, inr y => prod (x ≈ y) (Im x)
  | inr x, inl y => prod (x ≈ y) (Im x)
  end.

Lemma ckrel_equiv : Equivalence ckrel.
Proof.
  constructor.
  - intro u; destruct u; simpl; reflexivity.
  - intros u v; destruct u, v; simpl; intro H;
      try (symmetry; assumption);
      destruct H as [E I]; split;
      [ symmetry; assumption | eapply Im_resp; eassumption
      | symmetry; assumption | eapply Im_resp; eassumption ].
  - intros u v w; destruct u, v, w; simpl; intros H1 H2;
      repeat match goal with [ X : prod _ _ |- _ ] => destruct X end;
      try (etransitivity; eassumption);
      split; try (etransitivity; eassumption); try assumption;
      try (eapply Im_resp; [ symmetry; eassumption | assumption ]).
Qed.

Definition CKSetoid : SetoidObject@{p p} :=
  {| carrier := (carrier B + carrier B)%type;
     is_setoid := {| equiv := ckrel; setoid_equiv := ckrel_equiv |} |}.

Definition ck_left : B ~{Sets@{p h}}~> CKSetoid.
Proof.
  refine {| morphism := fun b => inl b |}; repeat intro; simpl; assumption.
Defined.

Definition ck_right : B ~{Sets@{p h}}~> CKSetoid.
Proof.
  refine {| morphism := fun b => inr b |}; repeat intro; simpl; assumption.
Defined.

(* The two inclusions agree after f: every f a lies in the image, by a. *)
Lemma ck_agree : ck_left ∘[Sets@{p h}] f ≈ ck_right ∘[Sets@{p h}] f.
Proof.
  intro a; simpl; split; [ reflexivity | exists a; reflexivity ].
Qed.

End CokernelPair.

(* Mac Lane, CWM 2nd ed., §I.5, printed p. 19: in Set the epis are exactly the
   surjections.  Both directions, at one universe. *)
Lemma surjectivity_is_epic@{h p} {A B : SetoidObject@{p p}}
  (h : A ~{Sets}~> B) :
  (∀ b, ∃ a, h a ≈ b)%type ↔ Epic@{h p} h.
Proof.
  split.
  - intros HA.
    constructor.
    autounfold in *; intros ??? HB.
    simpl in *; intros.
    specialize (HA x).
    destruct HA as [? HA].
    rewrite <- HA.
    apply HB.
  - intros E b.
    exact (snd (@epic _ _ _ _ E (CKSetoid h)
                  (ck_left h) (ck_right h) (ck_agree h) b)).
Defined.

(* The two halves under their own names, for callers that want just one. *)
Definition surjective_implies_epic@{h p} {A B : SetoidObject@{p p}}
  (h : A ~{Sets}~> B) : (∀ b, ∃ a, h a ≈ b)%type → Epic@{h p} h :=
  fst (surjectivity_is_epic@{h p} h).

Definition epic_implies_surjective@{h p} {A B : SetoidObject@{p p}}
  (h : A ~{Sets}~> B) : Epic@{h p} h → (∀ b, ∃ a, h a ≈ b)%type :=
  snd (surjectivity_is_epic@{h p} h).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_balanced@{h p} {A B : SetoidObject@{p p}}
  (h : A ~{Sets@{p h}}~> B)
  (Hm : @Monic Sets@{p h} A B h) (He : @Epic@{h p} Sets@{p h} A B h) :
  @IsIsomorphism Sets@{p h} A B h :=
  bijective_is_iso h
    {| inj := λ x y, snd (injectivity_is_monic h) Hm x y |}
    {| surj := λ b, epic_implies_surjective@{h p} h He b |}.

(* ------------------------------------------------------------------------ *)
(** ** The cancellation lemmas do not cancel the other factor *)

(*
   本节说明 Sets 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition bool_setoid_object@{t u} : SetoidObject@{t u} :=
  {| carrier   := bool
   ; is_setoid := {| equiv := eq ; setoid_equiv := eq_equivalence |} |}.

Program Definition pick_true : unit_setoid_object ~{Sets}~> bool_setoid_object :=
  {| morphism := fun _ => true |}.

Program Definition collapse : bool_setoid_object ~{Sets}~> unit_setoid_object :=
  {| morphism := fun _ => ttt |}.

Program Definition pick_false : unit_setoid_object ~{Sets}~> bool_setoid_object :=
  {| morphism := fun _ => false |}.

(* The composite is the identity on the singleton, up to `≈`. *)
Lemma collapse_pick : collapse ∘[Sets] pick_true ≈ id{Sets}.
Proof. intro u; now destruct u. Qed.

(* Hence it is both monic and epic: everything into or out of the singleton is
   forced, the singleton being terminal. *)
Lemma collapse_pick_monic : Monic (collapse ∘[Sets] pick_true).
Proof. constructor; intros z g1 g2 _ u; now destruct (g1 u), (g2 u). Qed.

Lemma collapse_pick_epic : Epic (collapse ∘[Sets] pick_true).
Proof. constructor; intros z g1 g2 H u; destruct u; apply (H ttt). Qed.

(* ... while the OTHER factor need not be, in either case.  [collapse] identifies the
   two booleans, so it is not monic: probe it with [pick_true] against
   [pick_false], which it cannot tell apart. *)
Lemma collapse_not_monic : Monic collapse → False.
Proof.
  intro M.
  assert (E : collapse ∘[Sets] pick_true ≈ collapse ∘[Sets] pick_false)
    by (intro u; now destruct u).
  exact (Bool.diff_true_false
           (@monic Sets _ _ collapse M unit_setoid_object
              pick_true pick_false E ttt)).
Qed.

(* And [pick_true] misses [false], so it is not epic: probe it with the
   identity against the constantly-true map, which agree on [true] alone. *)
Lemma pick_true_not_epic : Epic pick_true → False.
Proof.
  intro E.
  assert (H : id{Sets} ∘[Sets] pick_true
                ≈ (pick_true ∘[Sets] collapse) ∘[Sets] pick_true)
    by (intro u; now destruct u).
  exact (Bool.diff_false_true
           (@epic Sets _ _ pick_true E bool_setoid_object
              id{Sets} (pick_true ∘[Sets] collapse) H false)).
Qed.

(* The two asymmetries, packaged under the names Theory/Morphisms.v cites. *)
Definition sets_epic_left_factor_only :
  Epic (collapse ∘[Sets] pick_true) * (Epic pick_true → False) :=
  (collapse_pick_epic, pick_true_not_epic).

Definition sets_monic_right_factor_only :
  Monic (collapse ∘[Sets] pick_true) * (Monic collapse → False) :=
  (collapse_pick_monic, collapse_not_monic).

