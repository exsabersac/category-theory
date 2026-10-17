(** * The components functor and its right adjoint *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.One.
Require Import Category.Instance.Roof.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Construction.Comma.Special.

Generalizable All Variables.

(*
 Book:      Riehl, "Category Theory in Context", Dover 2016, §1.5,
 nLab:      https://ncatlab.org/nlab/show/connected+component
 nLab:      https://ncatlab.org/nlab/show/discrete+category
 nLab:      https://ncatlab.org/nlab/show/adjoint+string
 nLab:      https://ncatlab.org/nlab/show/reflective+subcategory
 nLab:      https://ncatlab.org/nlab/show/Cat
 Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   本文件给出 Cat 相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** §1. The discrete category on a setoid: two small lemmas *)

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition disc_setoid_iso {A : Type} (S : Setoid A) {x y : A}
  (e : @equiv A S x y) : @Isomorphism (DiscreteSetoidCat S) x y :=
  {| to := e ; from := symmetry e |}.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma zigzag_setoid_contract {A : Type} (S : Setoid A)
  (x y : DiscreteSetoidCat S) : ZigZag x y → @equiv A S x y.
Proof.
  intro s; induction s.
  - reflexivity.
  - now transitivity y.
  - now transitivity y; [ symmetry |].
Qed.

(** ** §2. The discrete functor Sets ⟶ Cat *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Cat_Disc_map {A B : Sets} (f : A ~> B) :
  DiscreteSetoidCat (is_setoid A) ⟶ DiscreteSetoidCat (is_setoid B) :=
  {| fobj := f
   ; fmap := fun x y (e : x ≈ y) => proper_morphism f x y e |}.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Cat_Disc : Sets ⟶ Cat := {|
  fobj := fun A => DiscreteSetoidCat (is_setoid A)
; fmap := fun _ _ f => Cat_Disc_map f
|}.
Next Obligation.
  intros f g H.
  exists (fun a => disc_setoid_iso (is_setoid y) (H a)); intros; exact I.
Defined.

(* Four readbacks, all [eq_refl].  The second and third are the ones a
   consumer needs: the objects of the discrete category ARE the carrier
   and its homs ARE the setoid's own relation. *)
Example cat_disc_obj (A : Sets) :
  fobj[Cat_Disc] A = DiscreteSetoidCat (is_setoid A) := eq_refl.

Example cat_disc_obj_carrier (A : Sets) :
  obj[fobj[Cat_Disc] A] = carrier A := eq_refl.

Example cat_disc_hom (A : Sets) (x y : carrier A) :
  (x ~{fobj[Cat_Disc] A}~> y) = (x ≈ y) := eq_refl.

Example cat_disc_fmap (A B : Sets) (f : A ~> B) (a : carrier A) :
  fobj[fmap[Cat_Disc] f] a = f a := eq_refl.

(** ** §3. The transposition *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition pi0_to {C : Cat} {A : Sets}
  (h : fobj[Pi0] C ~{Sets}~> A) : C ~{Cat}~> fobj[Cat_Disc] A :=
  {| fobj := h
   ; fmap := fun x y (f : x ~> y) =>
       @proper_morphism _ _ _ _ h x y (hom_zigzag f) |}.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition pi0_from {C : Cat} {A : Sets}
  (F : C ~{Cat}~> fobj[Cat_Disc] A) : fobj[Pi0] C ~{Sets}~> A :=
  {| morphism := fobj[F] |}.
Next Obligation.
  intros x y s.
  exact (zigzag_setoid_contract (is_setoid A) _ _ (zigzag_fmap F s)).
Defined.

(* The hom-setoid isomorphism.  Two obligations, both [Proper] fields;
   the two round trips are discharged by the ambient tactic, and §4
   records that the second of them is vacuous on arrows. *)
Program Definition pi0_adj_iso (C : Cat) (A : Sets) :
  @Isomorphism Sets
    {| carrier := @hom Sets (fobj[Pi0] C) A
     ; is_setoid := @homset Sets (fobj[Pi0] C) A |}
    {| carrier := @hom Cat C (fobj[Cat_Disc] A)
     ; is_setoid := @homset Cat C (fobj[Cat_Disc] A) |} :=
  {| to   := {| morphism := fun h => @pi0_to C A h |}
   ; from := {| morphism := fun F => @pi0_from C A F |} |}.
Next Obligation.
  intros h k H.
  exists (fun a => disc_setoid_iso (is_setoid A) (H a)); intros; exact I.
Defined.
Next Obligation. intros F G H a; exact (to (`1 H a)). Defined.

(** ** §4. The adjunction *)

(*
   本节说明伴随、函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Components_Disc_Adjunction : Pi0 ⊣ Cat_Disc :=
  Build_Adjunction' pi0_adj_iso _ _.

Example pi0_adj_to_at (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) (x : C) :
  fobj[to (pi0_adj_iso C A) h] x = h x := eq_refl.

Example pi0_adj_from_at (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) (x : C) :
  from (pi0_adj_iso C A) F x = F x := eq_refl.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example pi0_unit_is_id (C : Cat) (x : C) :
  fobj[@unit _ _ _ _ Components_Disc_Adjunction C] x = x := eq_refl.

Example pi0_counit_is_id (A : Sets) (a : carrier A) :
  @counit _ _ _ _ Components_Disc_Adjunction A a = a := eq_refl.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example pi0_rt_from_to_strict (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) :
  from (pi0_adj_iso C A) (to (pi0_adj_iso C A) h) = h := eq_refl.

Example pi0_rt_from_to_at (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) (x : carrier (fobj[Pi0] C)) :
  from (pi0_adj_iso C A) (to (pi0_adj_iso C A) h) x = h x := eq_refl.

Example pi0_rt_from_to_fn (C : Cat) (A : Sets)
  (h : fobj[Pi0] C ~{Sets}~> A) :
  @morphism _ _ _ _ (from (pi0_adj_iso C A) (to (pi0_adj_iso C A) h))
    = @morphism _ _ _ _ h := eq_refl.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example pi0_rt_to_from_strict (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) :
  to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F) = F := eq_refl.

Example pi0_rt_to_from_obj (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) :
  fobj[to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F)] = fobj[F]
  := eq_refl.

Fail Example pi0_rt_to_from_map (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) (x y : C) (f : x ~> y) :
  fmap[to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F)] f = fmap[F] f
  := eq_refl.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example pi0_rt_to_from_map_equiv (C : Cat) (A : Sets)
  (F : C ~{Cat}~> fobj[Cat_Disc] A) (x y : C) (f : x ~> y) :
  fmap[to (pi0_adj_iso C A) (from (pi0_adj_iso C A) F)] f ≈ fmap[F] f
  := I.

Example cat_disc_hom_trivial (A : Sets) (x y : carrier A)
  (p q : x ~{fobj[Cat_Disc] A}~> y) : p ≈ q := I.

(** ** §5. Cat_Disc is fully faithful; Sets is reflective in Cat *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Cat_Disc_Full : Full Cat_Disc := {|
  prefmap := fun A B F => {| morphism := fobj[F] |}
|}.
Next Obligation. intros x y e; exact (fmap[F] e). Defined.

Definition Cat_Disc_Faithful : Faithful Cat_Disc.
Proof.
  unshelve econstructor.
  intros A B f g H a; exact (to (`1 H a)).
Defined.

(*
   本节说明伴随、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition pi0_counit_iso (A : Sets) :
  @Isomorphism Sets (fobj[Pi0] (fobj[Cat_Disc] A)) A :=
  {| to   := @counit _ _ _ _ Components_Disc_Adjunction A
   ; from := {| morphism := fun a : carrier A => a |} |}.
Next Obligation.
  intros x y e.
  exact (@hom_zigzag (DiscreteSetoidCat (is_setoid A)) x y e).
Defined.
Next Obligation. exact (zz_nil _). Defined.

Example pi0_counit_iso_to (A : Sets) (a : carrier A) :
  to (pi0_counit_iso A) a = a := eq_refl.

Example pi0_counit_iso_from (A : Sets) (a : carrier A) :
  from (pi0_counit_iso A) a = a := eq_refl.

(** ** §6. Non-vacuity: π₀ genuinely forgets *)

(*
   本节说明函子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition roof_pt@{o h p ru rh} (r : Roof@{ru rh}) :
  _1@{o h p} ⟶ Roof@{ru rh} :=
  {| fobj := fun _ => r ; fmap := fun _ _ _ => id[r] |}.

Example roof_objs_distinct : RNeg <> RPos.
Proof. discriminate. Qed.

Example roof_pi0_merges :
  @equiv _ (fobj[Pi0] Roof) RNeg RPos := Roof_Connected RNeg RPos.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Pi0_not_Faithful : Faithful Pi0 → False.
Proof.
  intro H.
  destruct (@fmap_inj _ _ Pi0 H _1 Roof (roof_pt RNeg) (roof_pt RPos)
              (fun _ => Roof_Connected RNeg RPos)) as [iso _].
  exact (RNeg_RPos_absurd (to (iso ttt))).
Qed.

(*
   本节说明伴随、等价、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem unit_not_Full :
  Full (@unit _ _ _ _ Components_Disc_Adjunction Roof) → False.
Proof.
  intro H.
  exact (RNeg_RPos_absurd
           (@prefmap _ _ _ H RNeg RPos (Roof_Connected RNeg RPos))).
Qed.

(** ** §7. Why the right adjoint is not the plain discrete category *)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition blur_bool : Sets := {|
  carrier   := bool
; is_setoid := {| equiv := fun _ _ => True |}
|}.

Program Definition blur_bool_negb : blur_bool ~{Sets}~> blur_bool :=
  {| morphism := negb |}.

Example blur_bool_id_equiv_negb : id[blur_bool] ≈ blur_bool_negb := fun _ => I.

(* The arrow action a carrier-based discrete functor would have to have:
   objects the CARRIER, arrows Leibniz equalities, so the action on
   arrows is [f_equal]. *)
Program Definition disc_carrier_map@{o so dh dp} {A B : Sets@{o so}}
  (f : A ~> B) :
  DiscreteCat@{o dh dp} (carrier A) ⟶ DiscreteCat@{o dh dp} (carrier B) :=
  {| fobj := f ; fmap := fun x y (e : x = y) => f_equal f e |}.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem DiscreteCat_carrier_not_functorial :
  (∀ (A B : Sets) (f g : A ~> B), f ≈ g →
     @equiv _ (@homset Cat (DiscreteCat (carrier A))
                           (DiscreteCat (carrier B)))
       (disc_carrier_map f) (disc_carrier_map g)) → False.
Proof.
  intro H.
  destruct (H blur_bool blur_bool id[blur_bool] blur_bool_negb (fun _ => I))
    as [iso _].
  exact (Bool.diff_true_false (to (iso true))).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem no_skeletal_carrier_functor_Sets_Cat
  (K : Sets ⟶ Cat)
  (pt : ∀ A : Sets, carrier A → obj[fobj[K] A])
  (Kobj : ∀ (A B : Sets) (f : A ~> B) (x : carrier A),
            fobj[fmap[K] f] (pt A x) = pt B (f x))
  (Kskel : ∀ (A : Sets) (x y : obj[fobj[K] A]), x ≅ y → x = y)
  (Kinj : ∀ (A : Sets) (x y : carrier A), pt A x = pt A y → x = y) :
  False.
Proof.
  destruct (@fmap_respects _ _ K blur_bool blur_bool
              id[blur_bool] blur_bool_negb (fun _ => I)) as [iso _].
  pose proof (iso (pt blur_bool true)) as I0.
  rewrite (Kobj blur_bool blur_bool id[blur_bool] true) in I0.
  rewrite (Kobj blur_bool blur_bool blur_bool_negb true) in I0.
  simpl in I0.
  exact (Bool.diff_true_false (Kinj blur_bool true false (Kskel _ _ _ I0))).
Qed.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cat_disc_pt (A : Sets) : carrier A → obj[fobj[Cat_Disc] A] :=
  fun a => a.

Example cat_disc_Kobj (A B : Sets) (f : A ~> B) (x : carrier A) :
  fobj[fmap[Cat_Disc] f] (cat_disc_pt A x) = cat_disc_pt B (f x) := eq_refl.

Definition cat_disc_Kinj (A : Sets) (x y : carrier A) :
  cat_disc_pt A x = cat_disc_pt A y → x = y := fun e => e.

Theorem Cat_Disc_not_skeletal :
  (∀ (A : Sets) (x y : obj[fobj[Cat_Disc] A]), x ≅ y → x = y) → False.
Proof.
  intro Hskel.
  refine (Bool.diff_true_false (Hskel blur_bool true false _)).
  exact (disc_setoid_iso (is_setoid blur_bool) I).
Qed.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example disc_is_DiscreteCat (A : Sets) :
  fobj[Cat_Disc] A = DiscreteCat (carrier A) := eq_refl.

(** ** §8. The universe boundary *)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Definition probe_instrument_live : Datatypes.unit := 0.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section Pi0Restriction.
  Universes co ch.
  Constraint ch < co.
  Context (C D : Category@{co ch ch}).

  Check (C : obj[Cat]).
  Check (pi0 C).
  Check (fun F : C ⟶ D => pi0_fmap F).

  Fail Check (fun (F G : C ⟶ D) => @pi0_fmap_respects C D F G).
  Fail Check (fobj[Pi0] C).
End Pi0Restriction.

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section Pi0Accepted.
  Universes cu.
  Context (C : Category@{cu cu cu}).
  Check (fun (F G : C ⟶ C) => @pi0_fmap_respects C C F G).
  Check (fobj[Pi0] C).
  Check (fun A : Sets => pi0_adj_iso C A).
End Pi0Accepted.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Section Pi0RespectsRepairable.
  Universes o hc hd so.
  Constraint hc < o.
  Constraint hd < o.

  Lemma probe_pi0_fmap_respects_annotated
    {C : Category@{o hc hc}} {D : Category@{o hd hd}} (F G : C ⟶ D)
    (H : F ≈ G) : @pi0_fmap@{o so hc hd} C D F ≈ pi0_fmap G.
  Proof. intro x; exact (hom_zigzag (to (`1 H x))). Qed.
End Pi0RespectsRepairable.
