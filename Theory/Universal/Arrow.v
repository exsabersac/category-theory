Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Initial.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Universal arrows *)

(*
 nLab: https://ncatlab.org/nlab/show/universal+morphism
   Wikipedia: https://en.wikipedia.org/wiki/Universal_property

   本文件给出箭头范畴：对象为底范畴的态射，态射为交换方块。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/universal+construction
   Paper: Samuel, "On universal mappings and free topological groups",
   Paper: Porst, "The history of the General Adjoint Functor Theorem",
   book: a functor has a left adjoint precisely when every object of its

   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniversalArrow.

Context `{C : Category}.
Context `{D : Category}.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class UniversalArrow (c : C) (F : D ⟶ C) := {
  arrow_initial : @Initial (=(c) ↓ F);   (* the universal property, as initiality *)

  arrow_obj := snd (`1 (@initial_obj _ arrow_initial));     (* the universal object a : D *)
  arrow : c ~> F arrow_obj := `2 (@initial_obj _ arrow_initial)  (* the universal morphism u : c ~> F a *)
}.

Notation "c ⟿ F" := (UniversalArrow c F) (at level 20) : category_theory_scope.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary ump_universal_arrows `(c ⟿ F) `(h : c ~> F d) :
  ∃! g : arrow_obj ~> d, h ≈ fmap[F] g ∘ arrow.
Proof.
  unfold arrow_obj, arrow; simpl.
  destruct (@zero _ arrow_initial ((ttt, d); h)), x.
  simpl in *.
  rewrite id_right in e.
  exists h1.
  - assumption.
  - intros.
    rewrite <- id_right in e.
    rewrite <- id_right in X.
    exact (snd (@zero_unique _ arrow_initial ((ttt, d); h)
                             ((ttt, h1); e) ((ttt, v); X))).
Qed.

(* Conversely, the universal mapping property reconstructs the initial object,
   hence a UniversalArrow: given η : c ~> F d that factors every f : c ~> F d'
   uniquely, (d, η) is initial in =(c) ↓ F. *)
Definition universal_arrow_from_UMP (c : C) (F : D ⟶ C) (d : D) (η : c ~> fobj[F] d)
  (u : ∀ (d' : D) (f : c ~> fobj[F] d'), ∃! g : d ~> d', f ≈ fmap[F] g ∘ η)
  : UniversalArrow c F.
Proof.
  unshelve eapply Build_UniversalArrow. simpl. unshelve esplit.
  - simpl. unshelve esplit; [ split; [ exact ttt | exact d ] | exact η ].
  - simpl. intros [ [unit d'] f]; simpl in *.
    unshelve esplit; [ split ; [ exact ttt | exact (unique_obj (u d' f))] | ].
    rewrite id_right; simpl. exact (unique_property (u d' f)).
  - simpl. intros [[unit d']  f]; simpl in *.
    intros [[unit2 g] g_eq]. simpl in g_eq.
    intros [[unit3 h] h_eq]. split.
    + simpl. destruct unit2, unit3; reflexivity.
    + simpl. rewrite id_right in g_eq, h_eq. simpl in h_eq.
      rewrite <- (uniqueness (u d' f) _ g_eq).
      exact (uniqueness (u d' f) _ h_eq).
Defined.

(* * ** Uniqueness up unique 同构 （已译） *)

(*
   本节说明幺半群、同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniversalArrowUnique.

Context {c : C}.
Context {F : D ⟶ C}.

(* The canonical mediating 态射: unique factorization second
 泛箭头 through first. （已译） *)
Definition ua_med (U1 U2 : UniversalArrow c F)
  : @arrow_obj c F U1 ~{D}~> @arrow_obj c F U2 :=
  unique_obj (@ump_universal_arrows c F U1 (@arrow_obj c F U2) (@arrow c F U2)).

Lemma ua_med_commutes (U1 U2 : UniversalArrow c F) :
  fmap[F] (ua_med U1 U2) ∘ @arrow c F U1 ≈ @arrow c F U2.
Proof.
  symmetry.
  exact (unique_property
           (@ump_universal_arrows c F U1 (@arrow_obj c F U2) (@arrow c F U2))).
Qed.

(* Any 态射 commuting two universal arrows IS mediator. （已译） *)
Lemma ua_med_unique (U1 U2 : UniversalArrow c F)
      (g : @arrow_obj c F U1 ~{D}~> @arrow_obj c F U2) :
  fmap[F] g ∘ @arrow c F U1 ≈ @arrow c F U2 → ua_med U1 U2 ≈ g.
Proof.
  intro Hg.
  exact (uniqueness
           (@ump_universal_arrows c F U1 (@arrow_obj c F U2) (@arrow c F U2))
           g (symmetry Hg)).
Qed.

Lemma ua_med_id (U1 : UniversalArrow c F) : ua_med U1 U1 ≈ id.
Proof.
  apply ua_med_unique.
  rewrite fmap_id.
  apply id_left.
Qed.

Lemma ua_med_comp (U1 U2 U3 : UniversalArrow c F) :
  ua_med U2 U3 ∘ ua_med U1 U2 ≈ ua_med U1 U3.
Proof.
  symmetry.
  apply ua_med_unique.
  rewrite fmap_comp, <- comp_assoc.
  rewrite ua_med_commutes.
  apply ua_med_commutes.
Qed.

(* The two mediators mutually inverse, so universal 对象 are
 isomorphic. （已译） *)
Program Definition universal_arrow_iso (U1 U2 : UniversalArrow c F)
  : @arrow_obj c F U1 ≅ @arrow_obj c F U2 := {|
  to   := ua_med U1 U2;
  from := ua_med U2 U1
|}.
Next Obligation. rewrite ua_med_comp; apply ua_med_id. Qed.
Next Obligation. rewrite ua_med_comp; apply ua_med_id. Qed.

(* An 同构 determined [to] component
 ([to_equiv_implies_iso_equiv]), so compatibility universal
 arrows pins it down completely. （已译） *)
Lemma universal_arrow_iso_unique (U1 U2 : UniversalArrow c F)
      (v : @arrow_obj c F U1 ≅ @arrow_obj c F U2) :
  fmap[F] (to v) ∘ @arrow c F U1 ≈ @arrow c F U2 →
  universal_arrow_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply ua_med_unique.
Qed.

(* Awodey's Proposition 1.10 general form: exactly one 同构 the
 universal 对象 carries first 泛箭头 second. （已译） *)
Program Definition universal_arrow_unique (U1 U2 : UniversalArrow c F) :
  Unique (fun i : @arrow_obj c F U1 ≅ @arrow_obj c F U2 =>
            fmap[F] (to i) ∘ @arrow c F U1 ≈ @arrow c F U2) := {|
  unique_obj      := universal_arrow_iso U1 U2;
  unique_property := ua_med_commutes U1 U2
|}.
Next Obligation. exact (universal_arrow_iso_unique U1 U2 v X). Qed.

End UniversalArrowUnique.

Context (U : @Functor D C).

Arguments arrow : clear implicits.
Arguments arrow_obj : clear implicits.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition LeftAdjointFunctorFromUniversalArrows (H : forall c : C, UniversalArrow c U)
  : @Functor C D.
Proof.
  refine
    ({|
        fobj := (fun c => arrow_obj _ _ (H c));
        fmap := (fun x y f => unique_obj (ump_universal_arrows (H x)
                                            ((arrow _ _ (H y) ∘ f))))

      |}).
  - abstract(intros x y f g f_eq_g;
             apply uniqueness;
             rewrite <- (unique_property
                  (ump_universal_arrows (H x) (arrow y U (H y) ∘ g)));
             now rewrite f_eq_g).
  - abstract(intros ?; apply uniqueness; cat_simpl).
  - abstract(intros c1 c2 c3 g f; apply uniqueness;
      rewrite fmap_comp,
      <- comp_assoc,
      <- (unique_property (ump_universal_arrows (H c1) _)),
      2! comp_assoc;
      exact (compose_respects _ _
             (unique_property (ump_universal_arrows (H c2) _))
             f f (Equivalence_Reflexive _))).
Defined.

(*
   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition AdjunctionFromUniversalArrows (H: forall c : C, UniversalArrow c U) :
  @Adjunction _ _ (LeftAdjointFunctorFromUniversalArrows H) U.
Proof.
  unshelve eapply Build_Adjunction'.
  + intros c d; unshelve eapply Isomorphism.Build_Isomorphism.
  - unshelve eapply Sets.Build_SetoidMorphism.
    * exact (fun g => (fmap[U] g) ∘ (arrow _ _ (H c))).
    * abstract(intros ? ? g1_eq_g2; rewrite g1_eq_g2; reflexivity).
  - unshelve eapply Sets.Build_SetoidMorphism.
    * exact(fun f => unique_obj (ump_universal_arrows (H c) f)).
    * abstract(intros f1 f2 f1_eq_f2; apply uniqueness; rewrite f1_eq_f2;
               apply (unique_property (ump_universal_arrows (H c) f2))).
  - abstract(intro f; symmetry; exact (unique_property (ump_universal_arrows (H c) f))).
  - abstract(simpl; intro g; apply uniqueness; reflexivity).
  + abstract(intros c1 c2 d f g;
             simpl; rewrite fmap_comp, <- 2! comp_assoc;
             apply (compose_respects (fmap[U] f) _ (Equivalence_Reflexive _) _ _);
             symmetry;
             apply (unique_property (ump_universal_arrows (H c1) _))).
  + abstract(intros ? ? ? ? ?; simpl; rewrite fmap_comp, <- comp_assoc; reflexivity).
Defined.


(*
   本节说明 Arrow 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class AUniversalArrow (c : C) (F : D ⟶ C) (a : D) := {
    universal_arrow : c ~> fobj[F] a ;                 (* the universal morphism u : c ~> F a *)
    universal_arrow_universal {d} {f : c ~> (fobj[F] d)} :  (* the universal property: f factors uniquely as fmap[F] g ∘ u *)
    Unique (fun g : hom a d => fmap[F] g ∘ universal_arrow ≈ f)
  }.

(* Two universal arrows at same 对象 equivalent underlying
 态射 agree; uniqueness property carries no further data. （已译） *)
#[export] Program Instance AUniversalArrowEquiv (c : C) (F : D ⟶ C) (a : D) :
  Setoid (AUniversalArrow c F a) :=
  {| equiv := fun X Y => (@universal_arrow _ _ _ X) ≈ (@universal_arrow _ _ _ Y) |}.

(*
   本节说明幺半群、同构、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AUniversalArrowUnique.

Context {c : C}.
Context {F : D ⟶ C}.

Definition aua_med {a b : D} (U1 : AUniversalArrow c F a)
           (U2 : AUniversalArrow c F b) : a ~{D}~> b :=
  unique_obj (@universal_arrow_universal c F a U1 b
                (@universal_arrow c F b U2)).

Lemma aua_med_commutes {a b : D} (U1 : AUniversalArrow c F a)
      (U2 : AUniversalArrow c F b) :
  fmap[F] (aua_med U1 U2) ∘ @universal_arrow c F a U1
    ≈ @universal_arrow c F b U2.
Proof.
  exact (unique_property
           (@universal_arrow_universal c F a U1 b (@universal_arrow c F b U2))).
Qed.

Lemma aua_med_unique {a b : D} (U1 : AUniversalArrow c F a)
      (U2 : AUniversalArrow c F b) (g : a ~{D}~> b) :
  fmap[F] g ∘ @universal_arrow c F a U1 ≈ @universal_arrow c F b U2 →
  aua_med U1 U2 ≈ g.
Proof.
  intro Hg.
  exact (uniqueness
           (@universal_arrow_universal c F a U1 b (@universal_arrow c F b U2))
           g Hg).
Qed.

Lemma aua_med_id {a : D} (U1 : AUniversalArrow c F a) : aua_med U1 U1 ≈ id.
Proof.
  apply aua_med_unique.
  rewrite fmap_id.
  apply id_left.
Qed.

Lemma aua_med_comp {a b e : D} (U1 : AUniversalArrow c F a)
      (U2 : AUniversalArrow c F b) (U3 : AUniversalArrow c F e) :
  aua_med U2 U3 ∘ aua_med U1 U2 ≈ aua_med U1 U3.
Proof.
  symmetry.
  apply aua_med_unique.
  rewrite fmap_comp, <- comp_assoc.
  rewrite aua_med_commutes.
  apply aua_med_commutes.
Qed.

Program Definition auniversal_arrow_iso {a b : D} (U1 : AUniversalArrow c F a)
        (U2 : AUniversalArrow c F b) : a ≅ b := {|
  to   := aua_med U1 U2;
  from := aua_med U2 U1
|}.
Next Obligation. rewrite aua_med_comp; apply aua_med_id. Qed.
Next Obligation. rewrite aua_med_comp; apply aua_med_id. Qed.

Lemma auniversal_arrow_iso_unique {a b : D} (U1 : AUniversalArrow c F a)
      (U2 : AUniversalArrow c F b) (v : a ≅ b) :
  fmap[F] (to v) ∘ @universal_arrow c F a U1 ≈ @universal_arrow c F b U2 →
  auniversal_arrow_iso U1 U2 ≈ v.
Proof.
  intro Hv.
  apply to_equiv_implies_iso_equiv; simpl.
  now apply aua_med_unique.
Qed.

Program Definition auniversal_arrow_unique {a b : D}
        (U1 : AUniversalArrow c F a) (U2 : AUniversalArrow c F b) :
  Unique (fun i : a ≅ b =>
            fmap[F] (to i) ∘ @universal_arrow c F a U1
              ≈ @universal_arrow c F b U2) := {|
  unique_obj      := auniversal_arrow_iso U1 U2;
  unique_property := aua_med_commutes U1 U2
|}.
Next Obligation. exact (auniversal_arrow_iso_unique U1 U2 v X). Qed.

End AUniversalArrowUnique.

(* * ** The two packagings 泛箭头 interchangeable （已译） *)

(*
   本节说明伴随、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniversalArrowPackaging.

Context {c : C}.
Context {F : D ⟶ C}.

(* Naming 对象 factorization property enough rebuild the
 comma-initial packaging: 这是 [universal_arrow_from_UMP] fed class's
 own two fields. （已译） *)
Definition ua_of_aua {a : D} (W : AUniversalArrow c F a) : UniversalArrow c F.
Proof.
  unshelve eapply (universal_arrow_from_UMP c F a (@universal_arrow c F a W)).
  intros d' f.
  unshelve econstructor.
  - exact (unique_obj (@universal_arrow_universal c F a W d' f)).
  - simpl; symmetry.
    exact (unique_property (@universal_arrow_universal c F a W d' f)).
  - simpl; intros v Hv.
    apply (uniqueness (@universal_arrow_universal c F a W d' f)).
    now symmetry.
Defined.

(* And conversely, projected 对象 arrow carry direct form, with
 uniqueness clause read off [ump_universal_arrows]. （已译） *)
Definition aua_of_ua (W : UniversalArrow c F)
  : AUniversalArrow c F (@arrow_obj c F W).
Proof.
  unshelve econstructor.
  - exact (@arrow c F W).
  - intros d f.
    unshelve econstructor.
    + exact (unique_obj (ump_universal_arrows W f)).
    + simpl; symmetry.
      exact (unique_property (ump_universal_arrows W f)).
    + simpl; intros v Hv.
      apply (uniqueness (ump_universal_arrows W f)).
      now symmetry.
Defined.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ua_of_aua_obj {a : D} (W : AUniversalArrow c F a) :
  @arrow_obj c F (ua_of_aua W) = a := eq_refl.

Example ua_of_aua_arrow {a : D} (W : AUniversalArrow c F a) :
  @arrow c F (ua_of_aua W) = @universal_arrow c F a W := eq_refl.

(*
   本节说明 Arrow 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example aua_ua_round_arrow {a : D} (W : AUniversalArrow c F a) :
  @universal_arrow c F a (aua_of_ua (ua_of_aua W))
    = @universal_arrow c F a W := eq_refl.

(* Hence at [AUniversalArrowEquiv] — compares underlying 态射
 nothing else, uniqueness field carrying no further data — that
 round trip 恒等. （已译） *)
Lemma aua_ua_round {a : D} (W : AUniversalArrow c F a) :
  aua_of_ua (ua_of_aua W) ≈ W.
Proof. simpl; reflexivity. Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example ua_aua_round_obj (W : UniversalArrow c F) :
  @arrow_obj c F (ua_of_aua (aua_of_ua W)) = @arrow_obj c F W := eq_refl.

Example ua_aua_round_arrow (W : UniversalArrow c F) :
  @arrow c F (ua_of_aua (aua_of_ua W)) = @arrow c F W := eq_refl.

End UniversalArrowPackaging.

End UniversalArrow.
