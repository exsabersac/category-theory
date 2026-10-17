Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Sets.Cocartesian.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Indexed.Hom.
Require Import Category.Structure.Limit.Power.
Require Coq.Vectors.Fin.

Generalizable All Variables.

Import EqNotations.

(** * The characterizing isomorphisms of a power and a copower *)

(*
   nLab:      https://ncatlab.org/nlab/show/copower

   本文件给出 hom 形式的伴随/同态。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(** ** The two hom functors, at a constant family *)

(* [c ↦ ∏_J C(c, b)], the right-hand side of Riehl's [C(X, A)^I]. *)
Definition power_hom_functor {C : Category} (J : Type) (b : C) : C^op ⟶ Sets :=
  iprod_hom_functor (fun _ : J => b).

(* [c ↦ ∏_J C(b, c)], the right-hand side of [C(∐_I A, X) ≅ C(A, X)^I]. *)
Definition copower_hom_functor {C : Category} (J : Type) (b : C) : C ⟶ Sets :=
  icoprod_hom_functor (fun _ : J => b).

(* Each right-hand side is itself a power, in [Sets]. *)
Example power_hom_functor_is_Sets_power {C : Category} (J : Type) (b c : C) :
  fobj[power_hom_functor J b] c
  = @power Sets Sets_HasIndexedProducts J
      {| carrier := @hom C c b ; is_setoid := @homset C c b |} := eq_refl.

Example copower_hom_functor_is_Sets_power {C : Category} (J : Type) (b c : C) :
  fobj[copower_hom_functor J b] c
  = @power Sets Sets_HasIndexedProducts J
      {| carrier := @hom C b c ; is_setoid := @homset C b c |} := eq_refl.

(** ** The comparison maps: composing with the evaluations, resp. injections *)

Definition power_hom_transform {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  @Transform (C^op) Sets (@Curried_CoHom C p) (power_hom_functor J b) :=
  @iprod_hom_transform C J (fun _ : J => b) p ev.

Definition copower_hom_transform {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  @Transform C Sets (@Curried_Hom C p) (copower_hom_functor J b) :=
  @icoprod_hom_transform C J (fun _ : J => b) p inj.

Example power_hom_transform_computes {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) (c : C) (u : c ~> p) :
  transform (power_hom_transform b p ev) c u = fun j : J => ev j ∘ u := eq_refl.

Example copower_hom_transform_computes {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) (c : C) (u : p ~> c) :
  transform (copower_hom_transform b p inj) c u = fun j : J => u ∘ inj j
  := eq_refl.

(** ** The isomorphisms, derived at the constant family *)

Definition power_hom_inverse {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) :
  @Transform (C^op) Sets (power_hom_functor J b) (@Curried_CoHom C p) :=
  @iprod_hom_inverse C J (fun _ : J => b) p ev H.

Definition copower_hom_inverse {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) :
  @Transform C Sets (copower_hom_functor J b) (@Curried_Hom C p) :=
  @icoprod_hom_inverse C J (fun _ : J => b) p inj H.

(* Riehl 3.5.4: [C(X, A^I) ≅ C(X, A)^I], natural in [X]. *)
Definition power_hom_iso {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C p) (power_hom_functor J b) :=
  @iprod_hom_iso C J (fun _ : J => b) p ev H.

(* Riehl 3.5.8: [C(I · A, X) ≅ C(A, X)^I], natural in [X]. *)
Definition copower_hom_iso {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C p) (copower_hom_functor J b) :=
  @icoprod_hom_iso C J (fun _ : J => b) p inj H.

(* The converse, and the biconditional: an invertible comparison map is a
   universal property.  Both are the donor's, at the constant family. *)
Definition power_of_hom_iso {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b}
  (I : @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C p)
                      (power_hom_functor J b)
                      (power_hom_transform b p ev)) :
  IsPower b p ev :=
  @iprod_of_hom_iso C J (fun _ : J => b) p ev I.

Definition copower_of_hom_iso {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p}
  (I : @IsIsomorphism ([C, Sets]) (@Curried_Hom C p)
                      (copower_hom_functor J b)
                      (copower_hom_transform b p inj)) :
  IsCopower b p inj :=
  @icoprod_of_hom_iso C J (fun _ : J => b) p inj I.

Definition power_iff_hom_iso {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  IsPower b p ev ↔
  @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C p) (power_hom_functor J b)
                 (power_hom_transform b p ev) :=
  @iprod_iff_hom_iso C J (fun _ : J => b) p ev.

Definition copower_iff_hom_iso {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  IsCopower b p inj ↔
  @IsIsomorphism ([C, Sets]) (@Curried_Hom C p) (copower_hom_functor J b)
                 (copower_hom_transform b p inj) :=
  @icoprod_iff_hom_iso C J (fun _ : J => b) p inj.

(** ** The derived forms are the donors' TERMS, not merely their types *)

Example power_hom_functor_is_donor {C : Category} (J : Type) (b : C) :
  power_hom_functor J b = @iprod_hom_functor C J (fun _ : J => b) := eq_refl.

Example copower_hom_functor_is_donor {C : Category} (J : Type) (b : C) :
  copower_hom_functor J b = @icoprod_hom_functor C J (fun _ : J => b)
  := eq_refl.

Example power_hom_transform_is_donor {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  power_hom_transform b p ev = @iprod_hom_transform C J (fun _ : J => b) p ev
  := eq_refl.

Example copower_hom_transform_is_donor {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  copower_hom_transform b p inj
  = @icoprod_hom_transform C J (fun _ : J => b) p inj := eq_refl.

Example power_hom_inverse_is_donor {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) :
  power_hom_inverse H = @iprod_hom_inverse C J (fun _ : J => b) p ev H
  := eq_refl.

Example copower_hom_inverse_is_donor {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) :
  copower_hom_inverse H = @icoprod_hom_inverse C J (fun _ : J => b) p inj H
  := eq_refl.

Example power_hom_iso_is_donor {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) :
  power_hom_iso H = @iprod_hom_iso C J (fun _ : J => b) p ev H := eq_refl.

Example copower_hom_iso_is_donor {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) :
  copower_hom_iso H = @icoprod_hom_iso C J (fun _ : J => b) p inj H := eq_refl.

Example power_iff_hom_iso_is_donor {C : Category} {J : Type} (b p : C)
  (ev : ∀ _ : J, p ~> b) :
  power_iff_hom_iso b p ev = @iprod_iff_hom_iso C J (fun _ : J => b) p ev
  := eq_refl.

Example copower_iff_hom_iso_is_donor {C : Category} {J : Type} (b p : C)
  (inj : ∀ _ : J, b ~> p) :
  copower_iff_hom_iso b p inj = @icoprod_iff_hom_iso C J (fun _ : J => b) p inj
  := eq_refl.

(* And the backward leg still computes to the mediator the [∃!] accessor
   names, so the packaging cannot drift from the universal property. *)
Example power_hom_iso_from_is_desc {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev)
  (c : C) (fam : ∀ _ : J, c ~> b) :
  transform (from (power_hom_iso H)) c fam = unique_obj (power_desc H fam)
  := eq_refl.

Example copower_hom_iso_from_is_desc {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj)
  (c : C) (fam : ∀ _ : J, b ~> c) :
  transform (from (copower_hom_iso H)) c fam = unique_obj (copower_desc H fam)
  := eq_refl.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition power_hom_iso_at {C : Category} {J : Type} {b p : C}
  {ev : ∀ _ : J, p ~> b} (H : IsPower b p ev) (c : C) :
  @Isomorphism Sets {| carrier := @hom C c p ; is_setoid := @homset C c p |}
    (@power Sets Sets_HasIndexedProducts J
       {| carrier := @hom C c b ; is_setoid := @homset C c b |}) := {|
  to   := transform (to (power_hom_iso H)) c;
  from := transform (from (power_hom_iso H)) c
|}.
Next Obligation.
  intros C J b p ev H c fam j.
  pose proof (iso_to_from (power_hom_iso H) c fam j) as Hr; simpl in *.
  now rewrite id_right in Hr.
Qed.
Next Obligation.
  intros C J b p ev H c u.
  pose proof (iso_from_to (power_hom_iso H) c u) as Hl; simpl in *.
  now rewrite id_right in Hl.
Qed.

Program Definition copower_hom_iso_at {C : Category} {J : Type} {b p : C}
  {inj : ∀ _ : J, b ~> p} (H : IsCopower b p inj) (c : C) :
  @Isomorphism Sets {| carrier := @hom C p c ; is_setoid := @homset C p c |}
    (@power Sets Sets_HasIndexedProducts J
       {| carrier := @hom C b c ; is_setoid := @homset C b c |}) := {|
  to   := transform (to (copower_hom_iso H)) c;
  from := transform (from (copower_hom_iso H)) c
|}.
Next Obligation.
  intros C J b p inj H c fam j.
  pose proof (iso_to_from (copower_hom_iso H) c fam j) as Hr; simpl in *.
  now rewrite id_left in Hr.
Qed.
Next Obligation.
  intros C J b p inj H c u.
  pose proof (iso_from_to (copower_hom_iso H) c u) as Hl; simpl in *.
  now rewrite id_left in Hl.
Qed.

(** ** At the chosen (co)power of a category that has all of them *)

Definition class_power_hom_iso {C : Category} {HP : @HasIndexedProducts C}
  (J : Type) (b : C) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C (power J b))
               (power_hom_functor J b) :=
  power_hom_iso (power_ump J b).

Definition class_copower_hom_iso {C : Category} {HC : @HasIndexedCoproducts C}
  (J : Type) (b : C) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C (copower J b))
               (copower_hom_functor J b) :=
  copower_hom_iso (copower_ump J b).

(*
   本节说明 Hom 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Sets_power_exponent (J : Type) (X : obj[Sets]) :
  @power Sets Sets_HasIndexedProducts J X ≅[Sets] Sets_pow J X :=
  Sets_constant_iprod_exponent J X.

Example Sets_power_carrier (J : Type) (X : obj[Sets]) :
  carrier (@power Sets Sets_HasIndexedProducts J X) = (J → carrier X)
  := eq_refl.

Example Sets_power_ev_computes (J : Type) (X : obj[Sets]) (j : J)
  (g : carrier (@power Sets Sets_HasIndexedProducts J X)) :
  @power_ev Sets Sets_HasIndexedProducts J X j g = g j := eq_refl.

Lemma Sets_power_ev_is_exponent_eval (J : Type) (X : obj[Sets]) (j : J) :
  Sets_exponent_eval J X j ∘ to (Sets_power_exponent J X)
    ≈ @power_ev Sets Sets_HasIndexedProducts J X j.
Proof. intros g; reflexivity. Qed.

(** ** Riehl 3.5.8 in [Sets]: the copower is the product with the index *)

Example Sets_copower_carrier (J : Type) (Y : obj[Sets]) :
  carrier (@copower Sets Sets_HasIndexedCoproducts J Y)
  = { _ : J & carrier Y } := eq_refl.

Example Sets_copower_inj_computes (J : Type) (Y : obj[Sets]) (j : J)
  (y : carrier Y) :
  @copower_inj Sets Sets_HasIndexedCoproducts J Y j y
  = existT (fun _ : J => carrier Y) j y := eq_refl.

Program Definition Sets_copower_prod_to (J : Type) (Y : obj[Sets]) :
  @copower Sets Sets_HasIndexedCoproducts J Y
    ~{Sets}~> (Sets_discrete J × Y)%object := {|
  morphism := fun p : { _ : J & carrier Y } => (projT1 p, projT2 p)
|}.
Next Obligation.
  intros J Y [i x] [j y] [e Hxy]; simpl in *; destruct e; simpl in *.
  split; [reflexivity|exact Hxy].
Qed.

Program Definition Sets_copower_prod_from (J : Type) (Y : obj[Sets]) :
  (Sets_discrete J × Y)%object
    ~{Sets}~> @copower Sets Sets_HasIndexedCoproducts J Y := {|
  morphism := fun p : (J * carrier Y)%type =>
                existT (fun _ : J => carrier Y) (fst p) (snd p)
|}.
Next Obligation.
  intros J Y [i x] [j y] [He Hxy]; simpl in *; destruct He; simpl in *.
  exists eq_refl; exact Hxy.
Qed.

Definition Sets_copower_prod (J : Type) (Y : obj[Sets]) :
  @copower Sets Sets_HasIndexedCoproducts J Y
    ≅[Sets] (Sets_discrete J × Y)%object.
Proof.
  refine {| to := Sets_copower_prod_to J Y
          ; from := Sets_copower_prod_from J Y |}.
  - intros [i x]; split; reflexivity.
  - intros [i x]; exists eq_refl; reflexivity.
Defined.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Sets_copower_one_to (J : Type) :
  @copower Sets Sets_HasIndexedCoproducts J 1%object
    ~{Sets}~> Sets_discrete J := {|
  morphism := fun p : { _ : J & poly_unit } => projT1 p
|}.
Next Obligation.
  intros J [i x] [j y] [e Hxy]; simpl in *; destruct e; reflexivity.
Qed.

(*
   本节说明 Hom 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_copower_one_from (J : Type) :
  Sets_discrete J
    ~{Sets}~> @copower Sets Sets_HasIndexedCoproducts J 1%object.
Proof.
  unshelve refine {| morphism := fun i : J =>
                       existT (fun _ : J => poly_unit) i ttt |}.
  intros i j Hij; destruct Hij; exists eq_refl; reflexivity.
Defined.

Definition Sets_copower_one (J : Type) :
  @copower Sets Sets_HasIndexedCoproducts J 1%object ≅[Sets] Sets_discrete J.
Proof.
  refine {| to := Sets_copower_one_to J; from := Sets_copower_one_from J |}.
  - intros i; reflexivity.
  - intros [i []]; exists eq_refl; reflexivity.
Defined.

(* The finite case: a set of [n] elements is the [n]-fold copower of [1]. *)
Definition Sets_copower_fin (n : nat) :
  @copower Sets Sets_HasIndexedCoproducts (Fin.t n) 1%object
    ≅[Sets] Sets_discrete (Fin.t n) :=
  Sets_copower_one (Fin.t n).

(* Awodey's [2 = 1 + 1], through the BINARY coproduct of
   Instance/Sets/Cocartesian.v: the constant-family instance of the
   pre-existing [Sets_icoprod_bool], so the passage costs nothing. *)
Definition Sets_copower_two :
  @copower Sets Sets_HasIndexedCoproducts bool 1%object ≅[Sets] (1 + 1)%object :=
  Sets_icoprod_bool (fun _ : bool => 1%object).

(** ** Non-vacuity: the [n]-fold copower of [1] does not collapse *)

Definition Sets_copower_pt {n : nat} (k : Fin.t n) :
  carrier (@copower Sets Sets_HasIndexedCoproducts (Fin.t n) 1%object) :=
  existT (fun _ : Fin.t n => poly_unit) k ttt.

Definition fin3_0 : Fin.t 3 := Fin.F1.
Definition fin3_1 : Fin.t 3 := Fin.FS Fin.F1.
Definition fin3_2 : Fin.t 3 := Fin.FS (Fin.FS Fin.F1).

Lemma Sets_copower_three_distinct :
  ((Sets_copower_pt fin3_0 ≈ Sets_copower_pt fin3_1) → False) *
  ((Sets_copower_pt fin3_1 ≈ Sets_copower_pt fin3_2) → False) *
  ((Sets_copower_pt fin3_0 ≈ Sets_copower_pt fin3_2) → False).
Proof.
  repeat split; intros [e _]; simpl in e.
  - discriminate.
  - apply Fin.FS_inj in e; discriminate.
  - discriminate.
Qed.
